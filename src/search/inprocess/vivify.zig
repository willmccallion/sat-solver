const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseRef = core.cnf.ClauseRef;
const Reason = core.assignment.Reason;
const clause_mod = core.clause;

const state = @import("../state.zig");
const Solver = state.Solver;
const solver_mod = @import("../solver.zig");
const Result = solver_mod.Result;

// Vivification — at level 0, walk low-LBD learned clauses and assume the
// negation of each literal in turn at a throwaway decision level. If BCP
// derives a conflict at position i, then the prefix C[0..i+1] is already
// implied by the formula, so the clause is replaced by that shorter
// version; if BCP derives a later literal of C to true, the same prefix
// shrink applies. Lits already falsified at level 0 are just dropped in
// place. Targets LBD ≤ 6 because glue-adjacent clauses are the ones
// whose BCP cost compounds through long searches.
pub const initial_interval: u64 = 15_000;
pub const grow_num: u64 = 3;
pub const grow_den: u64 = 2;
pub const budget_num: u64 = 2;
pub const budget_den: u64 = 10;
pub const lbd_cap: u32 = 6;

// Returns .unsat if any shrink lands on an empty clause or derives a
// conflicting level-0 unit; otherwise null. Preconditions: level 0, BCP
// is at fixed point.
//
// Memory safety: addClauseToArena may reallocate the arena and
// invalidate outstanding `clauseLits` slices. We copy each candidate
// into `scratch` up-front and hold no arena slice across the decision
// loop.
//
// Deleted-clause watcher sweep: shrunk/subsumed clauses leave their
// watchers dangling in `watchers[...]` pointing at deleted_bit-set arena
// slots. Propagate does not check `clauseIsDeleted`, so we must sweep
// watcher lists before returning.
pub fn vivify(self: *Solver) !?Result {
    std.debug.assert(self.assignment.level == 0);
    self.stats.vivifies += 1;

    const props_start = self.stats.propagations;
    const delta = if (props_start > self.props_at_last_vivify)
        props_start - self.props_at_last_vivify
    else
        0;
    const budget: u64 = (delta * budget_num) / budget_den;
    self.props_at_last_vivify = props_start;

    var candidates: std.ArrayList(ClauseRef) = .empty;
    defer candidates.deinit(self.allocator);
    for (self.learned_clauses.items) |cref| {
        if (self.clauseIsDeleted(cref)) continue;
        if (self.clauseLbd(cref) > lbd_cap) continue;
        try candidates.append(self.allocator, cref);
    }

    var scratch: std.ArrayList(Literal) = .empty;
    defer scratch.deinit(self.allocator);

    var any_deleted = false;

    outer: for (candidates.items) |cref| {
        if (budget > 0 and self.stats.propagations - props_start > budget) break;
        if (solver_mod.interruptRequested()) break;
        if (self.clauseIsDeleted(cref)) continue;

        // Copy lits before any decision-level push. Arena slices are
        // only safe between allocations; we intentionally don't hold one
        // across propagate().
        const lits_now = self.clauseLits(cref);
        scratch.clearRetainingCapacity();
        try scratch.ensureTotalCapacity(self.allocator, lits_now.len);
        scratch.appendSliceAssumeCapacity(lits_now);

        // Locked-clause check: if this clause is currently a reason for
        // a level-0 literal, mutating it would break reason chains.
        var locked = false;
        for (scratch.items) |lit| {
            const vi = self.assignment.vars[lit.variable()];
            if (vi.level == 0 and !vi.reason.isNone() and
                !vi.reason.isBinary() and vi.reason.clauseRef() == cref)
            {
                locked = true;
                break;
            }
        }
        if (locked) continue;

        var shrink_len: ?usize = null;
        var subsumed = false;

        var i: usize = 0;
        while (i < scratch.items.len) {
            const lit = scratch.items[i];
            const vi = self.assignment.vars[lit.variable()];

            if (vi.level == 0 and vi.value != .unassigned) {
                if (self.assignment.valueOfLiteral(lit) == .true) {
                    subsumed = true;
                    break;
                }
                _ = scratch.swapRemove(i);
                continue;
            }

            const cur = self.assignment.valueOfLiteral(lit);
            if (cur == .true) {
                shrink_len = i + 1;
                break;
            }
            if (cur == .false) {
                _ = scratch.swapRemove(i);
                continue;
            }

            try self.assignment.pushDecisionLevel();
            try self.assignment.assign(lit.negate(), Reason.none);
            const conflict = try self.propagate();
            if (conflict != null) {
                shrink_len = i + 1;
                break;
            }
            i += 1;
        }

        self.backtrack(0);

        if (subsumed) {
            try self.proof.deleteClause(self.clauseLits(cref));
            self.markDeleted(cref);
            self.stats.vivified += 1;
            any_deleted = true;
            continue :outer;
        }

        const original_len = self.clauseLen(cref);
        const new_len: usize = shrink_len orelse scratch.items.len;
        if (new_len >= original_len) continue;

        const new_lits = scratch.items[0..new_len];

        if (new_len == 0) {
            try self.proof.empty();
            return .unsat;
        }

        try self.proof.addClause(new_lits);
        try self.proof.deleteClause(self.clauseLits(cref));
        self.markDeleted(cref);
        any_deleted = true;
        self.stats.vivified += 1;

        if (new_len == 1) {
            const unit = new_lits[0];
            const val = self.assignment.valueOfLiteral(unit);
            if (val == .false) {
                try self.proof.empty();
                return .unsat;
            }
            if (val == .unassigned) {
                try self.assignment.assign(unit, Reason.none);
            }
        } else if (new_len == 2) {
            try self.addBinary(new_lits[0], new_lits[1]);
        } else {
            const new_lbd = self.computeLbd(new_lits);
            const new_cref = try self.addClauseToArena(new_lits, true, new_lbd);
            try self.learned_clauses.append(self.allocator, new_cref);
            try self.attachWatches(new_cref);
        }
    }

    // Watcher sweep — drop entries pointing at any clause marked deleted
    // this pass. Mirrors reduceDB's post-delete sweep so propagate never
    // dereferences a tombstoned arena slot.
    if (any_deleted) {
        for (self.watchers) |*wlist| {
            var j: usize = 0;
            for (wlist.items) |w| {
                if (!self.clauseIsDeleted(w.clause)) {
                    wlist.items[j] = w;
                    j += 1;
                }
            }
            wlist.shrinkRetainingCapacity(j);
        }

        var j: usize = 0;
        for (self.learned_clauses.items) |cref| {
            if (!self.clauseIsDeleted(cref)) {
                self.learned_clauses.items[j] = cref;
                j += 1;
            }
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }

    // Any new level-0 unit we derived (from a 1-lit shrink) needs
    // propagating before we return to search. If that itself conflicts,
    // the formula is UNSAT.
    if ((try self.propagate()) != null) {
        try self.proof.empty();
        return .unsat;
    }

    return null;
}

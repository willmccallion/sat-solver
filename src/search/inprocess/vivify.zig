const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseRef = core.cnf.ClauseRef;
const Reason = core.assignment.Reason;
const clause_mod = core.clause;

const common = @import("common.zig");
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
const budget_share: common.BudgetShare = .{ .num = 2, .den = 10 };
const lbd_cap: u32 = 6;

// Returns .unsat if any shrink lands on an empty clause or derives a
// conflicting level-0 unit; otherwise null. Precondition: level 0. It
// propagates to a fixed point first, since a decision at level 1 would
// claim any implication still pending at level 0.
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
    if (try self.propagateAtRoot()) |r| return r;
    self.stats.vivify_passes += 1;

    const props_start = self.stats.propagations;
    const budget = common.propagationBudget(props_start, &self.props_at_last_vivify, budget_share);

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
        if (self.stats.propagations - props_start > budget) break;
        if (solver_mod.interruptRequested()) break;
        if (self.clauseIsDeleted(cref)) continue;
        if (self.clauseIsLocked(cref)) continue;

        // Copy lits before any decision-level push. Arena slices are
        // only safe between allocations; we intentionally don't hold one
        // across propagate().
        const lits_now = self.clauseLits(cref);
        scratch.clearRetainingCapacity();
        try scratch.ensureTotalCapacity(self.allocator, lits_now.len);
        scratch.appendSliceAssumeCapacity(lits_now);

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
            self.stats.vivified_clauses += 1;
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
        self.stats.vivified_clauses += 1;

        const new_lbd = clause_mod.rewrittenLbd(self.clauseLbd(cref), new_len);
        if (try self.installClause(new_lits, .learned, new_lbd) == .refuted) {
            try self.proof.empty();
            return .unsat;
        }
    }

    if (any_deleted) self.dropDeletedClauseRefs();

    // Any new level-0 unit we derived (from a 1-lit shrink) needs
    // propagating before we return to search.
    if (try self.propagateAtRoot()) |r| return r;

    return null;
}

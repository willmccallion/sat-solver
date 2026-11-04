const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseRef = core.cnf.ClauseRef;
const Reason = core.assignment.Reason;
const clause_mod = core.clause;

const state = @import("../state.zig");
const Solver = state.Solver;

// Clause DB reduction. Called at level 0, on its own conflict schedule,
// when the learned clause count has outgrown `max_learned`. Keeps the better half
// (by LBD — lower is better). Clauses that are currently reasons for
// trail literals are "locked" and must never be deleted, since `analyze`
// follows reasons. Glue clauses (LBD ≤ 2) are also kept unconditionally
// — they are empirically the most useful learned clauses.
//
// Dead clauses stay in the arena as holes; this avoids rewriting
// ClauseRefs. BCP never visits them because we also strip their watchers
// from every watcher list. Arena compaction (see `compact`) reclaims the
// holes on a separate cadence.
pub fn reduceDB(self: *Solver) !void {
    std.debug.assert(self.assignment.level == 0);

    const Candidate = struct { cref: ClauseRef, lbd: u32 };
    var candidates: std.ArrayList(Candidate) = .empty;
    defer candidates.deinit(self.allocator);
    try candidates.ensureTotalCapacity(
        self.allocator,
        self.learned_clauses.items.len,
    );
    for (self.learned_clauses.items) |cref| {
        if (self.clauseIsDeleted(cref)) continue;
        if (self.clauseIsLocked(cref)) continue;
        const lbd = self.clauseLbd(cref);
        if (lbd <= 2) continue;
        candidates.appendAssumeCapacity(.{ .cref = cref, .lbd = lbd });
    }

    std.mem.sort(Candidate, candidates.items, {}, struct {
        fn lessThan(_: void, a: Candidate, b: Candidate) bool {
            return a.lbd > b.lbd;
        }
    }.lessThan);

    const to_delete = candidates.items.len / 2;
    for (candidates.items[0..to_delete]) |c| {
        try self.proof.deleteClause(self.clauseLits(c.cref));
        self.markDeleted(c.cref);
    }
    self.stats.reductions += 1;
    self.stats.deleted_clauses += to_delete;

    self.dropDeletedClauseRefs();
}

// Arena compaction. Rebuilds `self.arena` without deleted-clause holes
// and rewrites every ClauseRef consumer so references stay consistent.
// Only safe at level 0; solve() calls it after preprocessing and after
// each level-0 maintenance round once deleted clauses fill half the arena
// (no arena slices are in flight at those points).
//
// Three passes, no hashmap — we piggyback on the doomed arena to store
// the old→new mapping:
//
//   Pass 1. Walk headers sequentially. For each live clause, stash its
//     LBD into `lbd_stash` and overwrite arena[cref+1] with the new cref
//     it's going to land at.
//   Pass 2. Rewrite every consumer of ClauseRef using the in-arena
//     mapping: watchers, vars[v].reason, learned_clauses[].
//   Pass 3. Walk the old arena once more; for each live clause copy
//     header + stashed LBD + literals to the new arena at the new cref.
pub fn compact(self: *Solver) !void {
    std.debug.assert(self.assignment.level == 0);

    var lbd_stash: std.ArrayList(u32) = .empty;
    defer lbd_stash.deinit(self.allocator);

    var new_size: u32 = 0;
    var any_live = false;
    {
        var cref: u32 = 0;
        while (cref < self.arena.items.len) {
            const hdr = self.arena.items[cref].raw;
            const len = hdr & clause_mod.len_mask;
            const span = clause_mod.header_slots + len;
            if ((hdr & clause_mod.deleted_bit) == 0) {
                try lbd_stash.append(self.allocator, self.arena.items[cref + 1].raw);
                self.arena.items[cref + 1].raw = new_size;
                new_size += span;
                any_live = true;
            }
            cref += span;
        }
    }

    // Pass 2a: rewrite watchers. Also sweep deleted-clause watchers —
    // they point at arena slots we won't copy, so their redirection slot
    // is meaningless.
    for (self.watchers) |*wlist| {
        var j: usize = 0;
        for (wlist.items) |w| {
            const hdr = self.arena.items[w.clause].raw;
            if ((hdr & clause_mod.deleted_bit) != 0) continue;
            const new_cref = self.arena.items[w.clause + 1].raw;
            wlist.items[j] = .{ .clause = new_cref, .blocker = w.blocker };
            j += 1;
        }
        wlist.shrinkRetainingCapacity(j);
    }

    // Pass 2b: rewrite long-clause reasons on the trail. Binary reasons
    // inline their partner literal and don't reference the arena.
    for (self.assignment.trail.items) |lit| {
        const v = lit.variable();
        const r = self.assignment.vars[v].reason;
        if (r.isNone() or r.isBinary()) continue;
        const old_cref = r.clauseRef();
        const new_cref = self.arena.items[old_cref + 1].raw;
        self.assignment.vars[v].reason = Reason.fromClause(new_cref);
    }

    // Pass 2c: rewrite learned-clauses index, straining out the entries
    // of clauses deleted since the last sweep.
    {
        var j: usize = 0;
        for (self.learned_clauses.items) |cref| {
            const hdr = self.arena.items[cref].raw;
            if ((hdr & clause_mod.deleted_bit) != 0) continue;
            self.learned_clauses.items[j] = self.arena.items[cref + 1].raw;
            j += 1;
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }

    // Pass 3: materialize the compacted arena.
    var new_arena: std.ArrayList(Literal) = .empty;
    errdefer new_arena.deinit(self.allocator);
    try new_arena.ensureTotalCapacity(self.allocator, new_size);
    new_arena.items.len = new_size;
    if (any_live) {
        var cref: u32 = 0;
        var live_idx: usize = 0;
        while (cref < self.arena.items.len) {
            const hdr = self.arena.items[cref].raw;
            const len = hdr & clause_mod.len_mask;
            const span = clause_mod.header_slots + len;
            if ((hdr & clause_mod.deleted_bit) == 0) {
                const new_cref = self.arena.items[cref + 1].raw;
                new_arena.items[new_cref].raw = hdr & ~clause_mod.deleted_bit;
                new_arena.items[new_cref + 1].raw = lbd_stash.items[live_idx];
                live_idx += 1;
                var k: u32 = 0;
                while (k < len) : (k += 1) {
                    new_arena.items[new_cref + clause_mod.header_slots + k] =
                        self.arena.items[cref + clause_mod.header_slots + k];
                }
            }
            cref += span;
        }
    }

    self.arena.deinit(self.allocator);
    self.arena = new_arena;
    self.arena_dead_slots = 0;
    self.stats.compactions += 1;
}

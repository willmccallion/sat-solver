const std = @import("std");
const core = @import("core");
const ClauseRef = core.cnf.ClauseRef;
const Reason = core.assignment.Reason;
const clause_mod = core.clause;

const Schedule = @import("heuristics").schedule.Schedule;

const state = @import("../state.zig");
const Solver = state.Solver;

// ReduceDB cadence — fires on its own conflict-count budget, independent
// of restarts. The interval grows by a fixed step each trigger so long
// searches don't pay a log-N reduce every few thousand conflicts.
pub const schedule: Schedule = .every(2000, .{ .additive = 300 });

// The learned-clause limit starts at the formula's clause count, but no
// lower than `min_max_learned`, and grows by 11/10 after each reduction.
pub const min_max_learned: usize = 1000;
pub const max_learned_grow_num: usize = 11;
pub const max_learned_grow_den: usize = 10;

// Clauses at or below this LBD ("glue") are never deleted.
const glue_lbd: u32 = 2;

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
    std.debug.assert(self.assignment.level == .root);

    const Candidate = struct { cref: ClauseRef, lbd: u32 };
    var candidates: std.ArrayList(Candidate) = .empty;
    defer candidates.deinit(self.allocator);
    try candidates.ensureTotalCapacity(
        self.allocator,
        self.learned_clauses.items.len,
    );
    for (self.learned_clauses.items) |cref| {
        if (self.arena.isDeleted(cref)) continue;
        if (self.clauseIsLocked(cref)) continue;
        const lbd = self.arena.lbd(cref);
        if (lbd <= glue_lbd) continue;
        candidates.appendAssumeCapacity(.{ .cref = cref, .lbd = lbd });
    }

    std.mem.sort(Candidate, candidates.items, {}, struct {
        fn lessThan(_: void, a: Candidate, b: Candidate) bool {
            return a.lbd > b.lbd;
        }
    }.lessThan);

    const to_delete = candidates.items.len / 2;
    for (candidates.items[0..to_delete]) |c| {
        try self.proof.deleteClause(self.arena.literals(c.cref));
        self.arena.markDeleted(c.cref);
    }
    self.stats.reductions += 1;
    self.stats.deleted_clauses += to_delete;

    self.dropDeletedClauseRefs();
}

// Arena compaction. Moves the live clauses down over the holes deleted
// ones leave and rewrites every ClauseRef the solver holds: watchers,
// trail reasons and learned_clauses. Only safe at level 0; solve() calls it
// after preprocessing and after each level-0 maintenance round once deleted
// clauses fill half the arena, when no arena slice is in flight.
pub fn compact(self: *Solver) !void {
    std.debug.assert(self.assignment.level == .root);
    var relocation = try self.arena.compact(self.allocator);
    defer relocation.deinit(self.allocator);
    relocateWatchers(self, &relocation);
    relocateReasons(self, &relocation);
    relocateLearned(self, &relocation);
    self.stats.compactions += 1;
}

// Drops the watchers of deleted clauses, which compaction did not move.
fn relocateWatchers(self: *Solver, relocation: *const clause_mod.Relocation) void {
    for (self.watchers) |*wlist| {
        var kept: usize = 0;
        for (wlist.items) |w| {
            const new_cref = relocation.newRef(w.clause) orelse continue;
            wlist.items[kept] = .{ .clause = new_cref, .blocker = w.blocker };
            kept += 1;
        }
        wlist.shrinkRetainingCapacity(kept);
    }
}

// A binary reason names its partner literal, not an arena clause.
fn relocateReasons(self: *Solver, relocation: *const clause_mod.Relocation) void {
    for (self.assignment.trail.items) |lit| {
        const info = &self.assignment.vars[lit.variable().index()];
        const cref = switch (info.reason.decode()) {
            .clause => |cref| cref,
            .decision, .binary => continue,
        };
        info.reason = Reason.fromClause(relocation.newRef(cref).?);
    }
}

fn relocateLearned(self: *Solver, relocation: *const clause_mod.Relocation) void {
    var kept: usize = 0;
    for (self.learned_clauses.items) |cref| {
        self.learned_clauses.items[kept] = relocation.newRef(cref) orelse continue;
        kept += 1;
    }
    self.learned_clauses.shrinkRetainingCapacity(kept);
}

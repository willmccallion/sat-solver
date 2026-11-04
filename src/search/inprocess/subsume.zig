const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseRef = core.cnf.ClauseRef;
const clause_mod = core.clause;

const Schedule = @import("heuristics").schedule.Schedule;

const common = @import("common.zig");
const state = @import("../state.zig");
const Solver = state.Solver;
const solver_mod = @import("../solver.zig");
const Result = solver_mod.Result;

// Backward subsumption + self-subsuming resolution (SSR).
//
// For every non-deleted, non-locked clause C in the arena (length ≥ 3)
// and every binary in bin_watchers, we look for long-clause subsumption
// victims D in the occurrence list of C's shortest-occurring literal:
//
//   subsumption: C ⊆ D as sets of literals  ⇒ D is redundant, delete D.
//   SSR:         exactly one literal ℓ of C has ¬ℓ ∈ D and the rest of C
//                ⊆ D  ⇒  D can be strengthened to D \ {¬ℓ} (equivalent to
//                resolving C with D on ℓ and the result subsumes D).
//
// A clause's 64-bit abstract is a Bloom-style OR of (1 << (lit.raw & 63))
// over its literals, computed on demand rather than cached per clause.
// The classical fast-reject `(abstract(C) & ~abstract(D)) != 0` kills the
// overwhelming majority of candidate pairs without a subset check.
//
// Hashing literals rather than variables also rejects most SSR pairs
// (ℓ ∈ C, ¬ℓ ∈ D), so long-clause SSR is rare. Hashing variables would
// admit those pairs, but measured slower overall.
//
// Binaries in bin_watchers ARE used as subsumers and can be strengthened
// to units via SSR. They are NOT themselves subsumable or strengthenable
// into shorter binaries in this pass: that would swap-remove from two
// bin_watchers lists while the binary subsumer loop holds cursors into them.
//
// Precondition: level == 0; the pass propagates to a fixpoint first.
// Locked clauses are skipped. Strengthened long clauses are re-queued onto a
// work-list so cascading subsumptions can fire in the same pass, bounded
// per-clause by `max_revisits_per_clause` to prevent pathological loops.
//
// Memory safety: adding a clause may reallocate the arena and
// invalidate `literals` slices. We copy literals into a scratch buffer
// before any arena mutation and rebuild per-literal occurrence lists
// incrementally as clauses are strengthened.

const preprocess_cap: u64 = 100_000_000;
pub const schedule: Schedule = .every(20_000, .by_half);
const budget_share: common.BudgetShare = .{ .num = 2, .den = 10 };
const inprocess_floor: u64 = 2_000_000;

// Hard cap on how many times one clause can be revisited through the
// work queue. Prevents infinite loops where repeated strengthenings keep
// re-enqueueing the same arena slot.
const max_revisits_per_clause: u8 = 4;

// Inprocessing entry point, on a share of the propagations since the last
// call. Returns .unsat if SSR derives an empty clause or a conflicting unit.
pub fn subsume(self: *Solver) state.Error!?Result {
    if (try self.propagateAtRoot()) |r| return r;
    const share = common.propagationBudget(self.stats.propagations, &self.props_at_last_subsume, budget_share);
    return subsumeWithin(self, @max(inprocess_floor, share));
}

// Preprocessing entry point, on the large `preprocess_cap` budget because
// no search has happened yet.
pub fn preprocessSubsume(self: *Solver) state.Error!?Result {
    if (try self.propagateAtRoot()) |r| return r;
    self.props_at_last_subsume = self.stats.propagations;
    return subsumeWithin(self, preprocess_cap);
}

// Subsumption and SSR stopping once `budget` candidate checks are spent.
pub fn subsumeWithin(self: *Solver, budget: u64) state.Error!?Result {
    std.debug.assert(self.assignment.level == .root);
    self.stats.subsume_passes += 1;

    var pass = try Subsumption.init(self, budget);
    defer pass.deinit();
    try pass.runLongSubsumers();
    if (!pass.refuted) try pass.runBinarySubsumers();
    if (pass.refuted) {
        try self.proof.empty();
        return .unsat;
    }

    if (pass.any_deleted) self.dropDeletedClauseRefs();
    return self.propagateAtRoot();
}

// One subsumption pass over the clause database.
const Subsumption = struct {
    solver: *Solver,
    // Per-literal occurrence lists of long (≥3) clauses; binaries are
    // found through bin_watchers.
    occ: []std.ArrayList(ClauseRef),
    // Long subsumers still to try: the arena's clauses up front, then each
    // strengthened clause up to `max_revisits_per_clause` times.
    queue: std.ArrayList(ClauseRef) = .empty,
    revisits: std.AutoHashMap(ClauseRef, u8),
    // The current subsumer's literals, copied out of the arena, which
    // strengthening may reallocate.
    subsumer: std.ArrayList(Literal) = .empty,
    // Candidate (C, D) pairs examined.
    op_count: u64 = 0,
    budget: u64,
    any_deleted: bool = false,
    // Set once the pass derives an empty clause or a conflicting unit.
    refuted: bool = false,

    fn init(solver: *Solver, budget: u64) !Subsumption {
        const occ = try solver.allocator.alloc(std.ArrayList(ClauseRef), @as(usize, solver.num_vars) * 2);
        for (occ) |*o| o.* = .empty;
        var self: Subsumption = .{
            .solver = solver,
            .occ = occ,
            .revisits = .init(solver.allocator),
            .budget = budget,
        };
        errdefer self.deinit();
        try self.collectLongClauses();
        return self;
    }

    fn deinit(self: *Subsumption) void {
        const allocator = self.solver.allocator;
        for (self.occ) |*o| o.deinit(allocator);
        allocator.free(self.occ);
        self.queue.deinit(allocator);
        self.revisits.deinit();
        self.subsumer.deinit(allocator);
    }

    // Fills `occ` and `queue` with every live long clause in the arena.
    fn collectLongClauses(self: *Subsumption) !void {
        const solver = self.solver;
        const counts = try solver.allocator.alloc(u32, self.occ.len);
        defer solver.allocator.free(counts);
        @memset(counts, 0);
        var live = solver.arena.liveClauses();
        while (live.next()) |cref| {
            if (solver.arena.length(cref) < 3) continue;
            for (solver.arena.literals(cref)) |lit| counts[lit.raw] += 1;
        }
        for (self.occ, counts) |*o, n| try o.ensureTotalCapacityPrecise(solver.allocator, n);

        live = solver.arena.liveClauses();
        while (live.next()) |cref| {
            if (solver.arena.length(cref) < 3) continue;
            for (solver.arena.literals(cref)) |lit| self.occ[lit.raw].appendAssumeCapacity(cref);
            try self.queue.append(solver.allocator, cref);
        }
    }

    fn isOverBudget(self: *const Subsumption) bool {
        return self.op_count > self.budget;
    }

    fn runLongSubsumers(self: *Subsumption) !void {
        var qi: usize = 0;
        while (qi < self.queue.items.len) : (qi += 1) {
            if (self.refuted) return;
            if (self.isOverBudget() or self.solver.isInterrupted()) {
                @branchHint(.cold);
                return;
            }
            const c_cref = self.queue.items[qi];
            if (self.solver.arena.isDeleted(c_cref)) continue;
            if (self.solver.clauseIsLocked(c_cref)) continue;
            try self.setSubsumer(self.solver.arena.literals(c_cref));
            try self.trySubsumer(c_cref);
        }
    }

    // The binaries are snapshotted first, since strengthening adds and
    // removes bin_watchers entries, and each is re-checked before use.
    fn runBinarySubsumers(self: *Subsumption) !void {
        const solver = self.solver;
        var binaries: std.ArrayList([2]Literal) = .empty;
        defer binaries.deinit(solver.allocator);
        var all_binaries = solver.binaryClauses();
        while (all_binaries.next()) |pair| try binaries.append(solver.allocator, pair);

        for (binaries.items) |pair| {
            if (self.refuted) return;
            if (self.isOverBudget() or self.solver.isInterrupted()) {
                @branchHint(.cold);
                return;
            }
            if (!solver.hasBinary(pair[0], pair[1])) continue;
            try self.setSubsumer(&pair);
            try self.trySubsumer(null);
            if (self.refuted or self.isOverBudget()) return;
            try self.strengthenBinary(pair[0], pair[1]);
            if (self.refuted) return;
            try self.strengthenBinary(pair[1], pair[0]);
        }
    }

    fn setSubsumer(self: *Subsumption, lits: []const Literal) !void {
        self.subsumer.clearRetainingCapacity();
        try self.subsumer.appendSlice(self.solver.allocator, lits);
    }

    // Subsumes or strengthens each long clause that `subsumer` (clause
    // `c_cref`, or a binary when null) covers, walking the occurrences of
    // its rarest literal.
    fn trySubsumer(self: *Subsumption, c_cref: ?ClauseRef) !void {
        const c_abs = clauseAbstract(self.subsumer.items);
        const pivot = self.rarestLiteral();
        // Strengthening appends to occ lists, so index instead of iterating.
        var i: usize = 0;
        while (i < self.occ[pivot.raw].items.len) : (i += 1) {
            if (self.refuted) return;
            if (self.isOverBudget()) {
                @branchHint(.cold);
                return;
            }
            const d_cref = self.occ[pivot.raw].items[i];
            if (c_cref != null and d_cref == c_cref.?) continue;
            if (self.solver.arena.isDeleted(d_cref)) continue;
            try self.tryAgainst(c_cref, c_abs, d_cref);
        }
    }

    fn rarestLiteral(self: *const Subsumption) Literal {
        const lits = self.subsumer.items;
        var rarest = lits[0];
        for (lits[1..]) |lit| {
            if (self.occ[lit.raw].items.len < self.occ[rarest.raw].items.len) rarest = lit;
        }
        return rarest;
    }

    fn tryAgainst(self: *Subsumption, c_cref: ?ClauseRef, c_abs: u64, d_cref: ClauseRef) !void {
        const solver = self.solver;
        self.op_count += 1;
        const d_lits = solver.arena.literals(d_cref);
        if ((c_abs & ~clauseAbstract(d_lits)) != 0) return;
        if (d_lits.len < self.subsumer.items.len) return;

        const outcome = checkSubsumeOrSSR(self.subsumer.items, d_lits);
        if (outcome != .none and solver.clauseIsLocked(d_cref)) return;
        switch (outcome) {
            .none => {},
            .subsumed => {
                // A binary carries no learned flag, so it is already irredundant.
                if (c_cref) |c| {
                    if (!solver.arena.isLearned(d_cref)) solver.arena.promoteToIrredundant(c);
                }
                try self.deleteSubsumed(d_cref);
            },
            .strengthen => |neg_lit| try self.strengthenLongClause(d_cref, neg_lit),
        }
    }

    fn deleteSubsumed(self: *Subsumption, d_cref: ClauseRef) !void {
        const solver = self.solver;
        try solver.proof.deleteClause(solver.arena.literals(d_cref));
        solver.arena.markDeleted(d_cref);
        self.any_deleted = true;
        solver.stats.subsumed_clauses += 1;
    }

    // Self-subsuming resolution on a long clause D: removes `neg_lit` and
    // any literal false at level 0 (deleting D instead if one is true),
    // logs add-new before delete-old, and installs what is left. A new long
    // clause joins occ and the queue so later subsumers can reach it.
    fn strengthenLongClause(self: *Subsumption, d_cref: ClauseRef, neg_lit: Literal) !void {
        const solver = self.solver;
        // Copied out, since installing the new clause may reallocate the arena.
        const old_lits = try solver.allocator.dupe(Literal, solver.arena.literals(d_cref));
        defer solver.allocator.free(old_lits);
        var new_lits: std.ArrayList(Literal) = try .initCapacity(solver.allocator, old_lits.len);
        defer new_lits.deinit(solver.allocator);
        for (old_lits) |lit| {
            if (!lit.eql(neg_lit)) new_lits.appendAssumeCapacity(lit);
        }
        const kept = common.unassignedAtRoot(&solver.assignment, new_lits.items) orelse
            return self.deleteSubsumed(d_cref);

        try solver.proof.addClause(kept);
        try solver.proof.deleteClause(old_lits);
        solver.arena.markDeleted(d_cref);
        self.any_deleted = true;
        solver.stats.strengthened_clauses += 1;

        const lbd = clause_mod.rewrittenLbd(solver.arena.lbd(d_cref), kept.len);
        switch (try solver.installClause(kept, solver.arena.kind(d_cref), lbd)) {
            .refuted => self.refuted = true,
            .unit, .binary => {},
            .long => |new_cref| try self.requeue(d_cref, new_cref, kept),
        }
    }

    // Adds a strengthened clause to occ, and to the queue unless the
    // clause it replaced was already revisited `max_revisits_per_clause`
    // times, so chains of strengthenings terminate.
    fn requeue(self: *Subsumption, old_cref: ClauseRef, new_cref: ClauseRef, lits: []const Literal) !void {
        const allocator = self.solver.allocator;
        for (lits) |lit| {
            try clause_mod.reserveSlot(ClauseRef, &self.occ[lit.raw], allocator);
            self.occ[lit.raw].appendAssumeCapacity(new_cref);
        }
        const revisit_count = (self.revisits.get(old_cref) orelse 0) + 1;
        if (revisit_count > max_revisits_per_clause) return;
        try self.revisits.put(new_cref, revisit_count);
        try self.queue.append(allocator, new_cref);
    }

    // Resolving the subsumer (a ∨ b) with a binary (a ∨ ¬b) on b gives
    // the unit a, which replaces that binary at level 0.
    fn strengthenBinary(self: *Subsumption, a: Literal, b: Literal) !void {
        const solver = self.solver;
        const neg_b = b.negate();
        while (solver.hasBinary(a, neg_b)) {
            try solver.proof.addClause(&[_]Literal{a});
            try solver.proof.deleteClause(&[_]Literal{ a, neg_b });
            solver.removeBinary(a, neg_b);
            solver.stats.strengthened_clauses += 1;
            if (try solver.assertRootUnit(a) == .refuted) {
                self.refuted = true;
                return;
            }
        }
    }
};

// Bloom-style OR of one bit per literal; C ⊆ D requires abs(C) ⊆ abs(D).
fn clauseAbstract(lits: []const Literal) u64 {
    var abstract: u64 = 0;
    for (lits) |lit| abstract |= @as(u64, 1) << @intCast(lit.raw & 63);
    return abstract;
}

const CheckResult = union(enum) {
    none,
    subsumed,
    strengthen: Literal, // the literal in D to remove (= negation of the C-lit)
};

// Does the multiset C match a subset of D with at most one negated
// literal? Returns:
//   .subsumed            — every lit of C appears in D as-is.
//   .strengthen(lit)     — exactly one lit ℓ of C has ¬ℓ ∈ D; other lits
//                          of C all appear in D. The D-literal to remove
//                          is lit = ¬ℓ.
//   .none                — neither condition holds.
fn checkSubsumeOrSSR(c_lits: []const Literal, d_lits: []const Literal) CheckResult {
    var neg_match: ?Literal = null;
    for (c_lits) |cl| {
        var found_same = false;
        var found_neg: ?Literal = null;
        const cl_neg = cl.negate();
        for (d_lits) |dl| {
            if (dl.raw == cl.raw) {
                found_same = true;
                break;
            }
            if (dl.raw == cl_neg.raw) {
                found_neg = dl;
            }
        }
        if (found_same) continue;
        if (found_neg) |nl| {
            if (neg_match != null) return .none;
            neg_match = nl;
            continue;
        }
        return .none;
    }
    if (neg_match) |nl| return .{ .strengthen = nl };
    return .subsumed;
}

// Subsume: mark D deleted, DRAT-delete it, increment counters.
fn subsumeClause(
    self: *Solver,
    d_cref: ClauseRef,
    any_deleted: *bool,
) !void {
    try self.proof.deleteClause(self.arena.literals(d_cref));
    self.arena.markDeleted(d_cref);
    any_deleted.* = true;
    self.stats.subsumed_clauses += 1;
}

// Self-subsuming resolution on a long clause D. Removes `neg_lit` and
// any literal false at level 0 from D's literals (deleting D instead if
// one is true there), emits DRAT add-new then delete-old, and transitions
// to the appropriate length:
//   0  → derive empty clause (.unsat).
//   1  → assign unit at level 0 (or conflict → unsat).
//   2  → install into bin_watchers.
//   ≥3 → create a fresh arena clause, attach watches, push to learned_
//        clauses if applicable, enqueue for further subsumption.
// Old D is marked deleted. occ lists are updated for any new long clause
// so subsequent subsumers can reach it.
fn strengthenLongClause(
    self: *Solver,
    d_cref: ClauseRef,
    neg_lit: Literal,
    occ: []std.ArrayList(ClauseRef),
    revisits: *std.AutoHashMap(ClauseRef, u8),
    queue: *std.ArrayList(ClauseRef),
    any_deleted: *bool,
    unsat_derived: *bool,
) !void {
    // Build the strengthened literal list in a scratch buffer, since
    // Adding a clause may reallocate the arena.
    var new_lits: std.ArrayList(Literal) = .empty;
    defer new_lits.deinit(self.allocator);

    const d_lits_snapshot = self.arena.literals(d_cref);
    const old_lits_copy = try self.allocator.dupe(Literal, d_lits_snapshot);
    defer self.allocator.free(old_lits_copy);

    try new_lits.ensureTotalCapacity(self.allocator, d_lits_snapshot.len);
    for (d_lits_snapshot) |lit| {
        if (!lit.eql(neg_lit)) new_lits.appendAssumeCapacity(lit);
    }
    const kept = common.unassignedAtRoot(&self.assignment, new_lits.items) orelse
        return subsumeClause(self, d_cref, any_deleted);
    new_lits.shrinkRetainingCapacity(kept.len);

    const new_len = new_lits.items.len;
    const kind = self.arena.kind(d_cref);

    // Emit DRAT add FIRST, then delete (required for DRAT-RUP correctness
    // when the strengthened clause is the resolvent).
    try self.proof.addClause(new_lits.items);
    try self.proof.deleteClause(old_lits_copy);

    // Mark old D deleted.
    self.arena.markDeleted(d_cref);
    any_deleted.* = true;
    self.stats.strengthened_clauses += 1;

    const new_lbd = clause_mod.rewrittenLbd(self.arena.lbd(d_cref), new_len);
    const new_cref = switch (try self.installClause(new_lits.items, kind, new_lbd)) {
        .refuted => {
            unsat_derived.* = true;
            return;
        },
        .unit, .binary => return,
        .long => |cref| cref,
    };

    // Register in occ lists so subsequent subsumers find it.
    for (new_lits.items) |lit| {
        try clause_mod.reserveSlot(ClauseRef, &occ[lit.raw], self.allocator);
        occ[lit.raw].appendAssumeCapacity(new_cref);
    }

    // Cap revisits so pathological chains (each strengthening produces
    // the next subsumer that strengthens the next arena slot) terminate.
    const old_count = revisits.get(d_cref) orelse 0;
    const new_count: u8 = old_count + 1;
    if (new_count <= max_revisits_per_clause) {
        try revisits.put(new_cref, new_count);
        try queue.append(self.allocator, new_cref);
    }
}

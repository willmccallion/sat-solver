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
// (ℓ ∈ C, ¬ℓ ∈ D), so long-clause SSR is rare. Hashing variables enables
// it but measured ~6% slower on uf/uuf200-250 and no better on a SAT
// Competition 2025 subset (7 vs 8 of 40 solved at 120 s).
//
// Binaries in bin_watchers ARE used as subsumers and can be strengthened
// to units via SSR. They are NOT themselves subsumable or strengthenable
// into shorter binaries in this pass — doing so correctly would require
// swap-removing from two bin_watchers lists and re-scanning cursors used
// by concurrent subsumption; we defer that to a separate session.
//
// Precondition: level == 0; the pass propagates to a fixpoint first. The
// locked-clause check mirrors vivify.zig's: a clause that is currently a
// reason for a level-0 literal is skipped. Strengthened long clauses are re-queued onto a
// work-list so cascading subsumptions can fire in the same pass, bounded
// per-clause by `max_revisits_per_clause` to prevent pathological loops.
//
// Memory safety: addClauseToArena may reallocate `self.arena` and
// invalidate `clauseLits` slices. We copy literals into a scratch buffer
// before any arena mutation and rebuild per-literal occurrence lists
// incrementally as clauses are strengthened.

pub const preprocess_cap: u64 = 100_000_000;
pub const inprocess_initial_interval: u64 = 20_000;
pub const grow_num: u64 = 3;
pub const grow_den: u64 = 2;
pub const budget_num: u64 = 2;
pub const budget_den: u64 = 10;
pub const inprocess_floor: u64 = 2_000_000;

// Hard cap on how many times one clause can be revisited through the
// work queue. Prevents infinite loops where repeated strengthenings keep
// re-enqueueing the same arena slot.
const max_revisits_per_clause: u8 = 4;

// Public inprocessing entry point. Uses the budget derived from
// propagations-since-last-call; returns .unsat if SSR derives an empty
// clause or a conflicting unit.
pub fn subsume(self: *Solver) !?Result {
    return subsumeImpl(self, false);
}

// Preprocessing entry point. Uses a much larger fixed budget because
// there are no "propagations since last call" yet — the prior search has
// done zero work.
pub fn preprocessSubsume(self: *Solver) !?Result {
    return subsumeImpl(self, true);
}

fn subsumeImpl(self: *Solver, is_preprocess: bool) !?Result {
    std.debug.assert(self.assignment.level == 0);
    if (try self.propagateAtRoot()) |r| return r;
    self.stats.subsumes += 1;

    const props_start = self.stats.propagations;
    const budget: u64 = blk: {
        if (is_preprocess or self.props_at_last_subsume == 0) {
            break :blk preprocess_cap;
        }
        const delta = if (props_start > self.props_at_last_subsume)
            props_start - self.props_at_last_subsume
        else
            0;
        const raw = (delta * budget_num) / budget_den;
        break :blk @max(inprocess_floor, raw);
    };
    self.props_at_last_subsume = props_start;

    const num_lits: usize = @as(usize, self.num_vars) * 2;

    // Per-literal occurrence lists for LONG (≥3) clauses only. Binaries
    // are discovered via self.bin_watchers directly.
    var occ: []std.ArrayList(ClauseRef) = try self.allocator.alloc(
        std.ArrayList(ClauseRef),
        num_lits,
    );
    for (occ) |*o| o.* = .empty;
    defer {
        for (occ) |*o| o.deinit(self.allocator);
        self.allocator.free(occ);
    }

    // Revisit counter. Capped by max_revisits_per_clause.
    var revisits: std.AutoHashMap(ClauseRef, u8) = .init(self.allocator);
    defer revisits.deinit();

    // Work queue of long clauses yet to process. Walks the arena once up
    // front; strengthenings append the new ClauseRef.
    var queue: std.ArrayList(ClauseRef) = .empty;
    defer queue.deinit(self.allocator);

    // Scratch buffer for copying clause literals across arena mutations.
    var scratch: std.ArrayList(Literal) = .empty;
    defer scratch.deinit(self.allocator);

    // Build initial occurrence lists and queue from arena
    {
        const counts = try self.allocator.alloc(u32, num_lits);
        defer self.allocator.free(counts);
        @memset(counts, 0);
        var cref: ClauseRef = 0;
        while (cref < self.arena.items.len) {
            const header = self.arena.items[cref].raw;
            const len = header & clause_mod.len_mask;
            if ((header & clause_mod.deleted_bit) == 0 and len >= 3) {
                for (self.clauseLits(cref)) |lit| counts[lit.raw] += 1;
            }
            cref += clause_mod.header_slots + len;
        }
        for (occ, counts) |*o, n| try o.ensureTotalCapacityPrecise(self.allocator, n);

        cref = 0;
        while (cref < self.arena.items.len) {
            const header = self.arena.items[cref].raw;
            const len = header & clause_mod.len_mask;
            const span = clause_mod.header_slots + len;
            if ((header & clause_mod.deleted_bit) == 0 and len >= 3) {
                for (self.clauseLits(cref)) |lit| occ[lit.raw].appendAssumeCapacity(cref);
                try queue.append(self.allocator, cref);
            }
            cref += span;
        }
    }

    // Budget accounting: number of (C, D) candidate pairs examined.
    var op_count: u64 = 0;
    var any_deleted = false;
    var unsat_derived = false;

    // Process the work queue. Each loop iteration pulls a subsumer C and
    // tries to subsume or strengthen long clauses D in occ[ℓ] for the
    // shortest-occurrence literal ℓ of C. Binaries that are known
    // subsumers are handled in a dedicated second pass below.
    var qi: usize = 0;
    while (qi < queue.items.len) : (qi += 1) {
        if (unsat_derived) break;
        if (op_count > budget or solver_mod.interruptRequested()) {
            @branchHint(.cold);
            break;
        }

        const c_cref = queue.items[qi];
        if (self.clauseIsDeleted(c_cref)) continue;
        if (clauseIsLockedAtLevel0(self, c_cref)) continue;

        try processSubsumerLong(
            self,
            c_cref,
            occ,
            &revisits,
            &queue,
            &scratch,
            &op_count,
            budget,
            &any_deleted,
            &unsat_derived,
        );
    }

    // Binary subsumers pass
    // For each binary (a, b), try to subsume/strengthen long clauses that
    // contain a and b (subsumption), or long clauses that contain a and
    // ¬b (SSR — strengthen by removing ¬b), etc. Strengthening removes
    // and appends bin_watchers entries, so the binaries are snapshotted
    // first and each is re-checked for presence before use.
    if (!unsat_derived) {
        var binaries: std.ArrayList([2]Literal) = .empty;
        defer binaries.deinit(self.allocator);
        var l_raw: u32 = 0;
        while (l_raw < num_lits) : (l_raw += 1) {
            const a = (Literal{ .raw = l_raw }).negate();
            for (self.bin_watchers[l_raw].items) |entry| {
                if (a.raw < entry.other.raw) try binaries.append(self.allocator, .{ a, entry.other });
            }
        }

        for (binaries.items) |pair| {
            if (unsat_derived) break;
            if (op_count > budget or solver_mod.interruptRequested()) {
                @branchHint(.cold);
                break;
            }
            if (!hasBinaryClause(self, pair[0], pair[1])) continue;
            try processSubsumerBinary(
                self,
                pair[0],
                pair[1],
                occ,
                &revisits,
                &queue,
                &scratch,
                &op_count,
                &any_deleted,
                &unsat_derived,
            );
        }
    }

    if (unsat_derived) {
        try self.proof.empty();
        return .unsat;
    }

    // Watcher sweep — drop entries pointing at any clause marked deleted
    // this pass. Mirrors vivify.zig's post-delete sweep so propagate never
    // dereferences a tombstoned arena slot.
    if (any_deleted) {
        for (self.watchers) |*wlist| {
            var j: usize = 0;
            for (wlist.items) |entry| {
                if (!self.clauseIsDeleted(entry.clause)) {
                    wlist.items[j] = entry;
                    j += 1;
                }
            }
            wlist.shrinkRetainingCapacity(j);
        }

        var j: usize = 0;
        for (self.learned_clauses.items) |cref| {
            if (!self.clauseIsDeleted(cref) and self.clauseIsLearned(cref)) {
                self.learned_clauses.items[j] = cref;
                j += 1;
            }
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }

    if (try self.propagateAtRoot()) |r| return r;

    return null;
}

fn hasBinaryClause(self: *const Solver, a: Literal, b: Literal) bool {
    for (self.bin_watchers[a.negate().raw].items) |entry| {
        if (entry.other.eql(b)) return true;
    }
    return false;
}

// Returns true when `cref` is currently the reason for a level-0 literal.
// Those clauses cannot be mutated without breaking analyze()'s reason
// walks on the trail.
fn clauseIsLockedAtLevel0(self: *Solver, cref: ClauseRef) bool {
    const lits = self.clauseLits(cref);
    for (lits) |lit| {
        const vi = self.assignment.vars[lit.variable()];
        if (vi.level == 0 and !vi.reason.isNone() and
            !vi.reason.isBinary() and vi.reason.clauseRef() == cref)
        {
            return true;
        }
    }
    return false;
}

// Processes one long clause C as a potential subsumer. Walks occ[ℓ] for
// the shortest-occurrence literal of C and tries subsumption / SSR on
// each candidate D.
fn processSubsumerLong(
    self: *Solver,
    c_cref: ClauseRef,
    occ: []std.ArrayList(ClauseRef),
    revisits: *std.AutoHashMap(ClauseRef, u8),
    queue: *std.ArrayList(ClauseRef),
    scratch: *std.ArrayList(Literal),
    op_count: *u64,
    budget: u64,
    any_deleted: *bool,
    unsat_derived: *bool,
) !void {
    // Snapshot C's literals and abstract; we hold no arena slices past
    // the first allocation below.
    const c_lits_snapshot = self.clauseLits(c_cref);
    const c_abs = clauseAbstract(c_lits_snapshot);

    // Pick ℓ ∈ C with the shortest occurrence list.
    var pivot: Literal = c_lits_snapshot[0];
    var pivot_len: usize = occ[pivot.raw].items.len;
    for (c_lits_snapshot[1..]) |lit| {
        const n = occ[lit.raw].items.len;
        if (n < pivot_len) {
            pivot = lit;
            pivot_len = n;
        }
    }

    // Copy C's literals so we don't hold an arena slice across mutations.
    scratch.clearRetainingCapacity();
    try scratch.ensureTotalCapacity(self.allocator, c_lits_snapshot.len);
    scratch.appendSliceAssumeCapacity(c_lits_snapshot);
    const c_len = scratch.items.len;

    // Walk occ[pivot]. Entries may be deleted mid-pass; skip those.
    // New strengthenings append to occ lists — use an index-based loop.
    var i: usize = 0;
    while (i < occ[pivot.raw].items.len) : (i += 1) {
        if (unsat_derived.*) return;
        if (op_count.* > budget) {
            @branchHint(.cold);
            return;
        }

        const d_cref = occ[pivot.raw].items[i];
        if (d_cref == c_cref) continue;
        if (self.clauseIsDeleted(d_cref)) continue;

        if ((c_abs & ~clauseAbstract(self.clauseLits(d_cref))) != 0) {
            op_count.* += 1;
            continue;
        }

        // Check subset(C, D) allowing at most one negated-literal
        // mismatch (for SSR). Result: .subsumed, .strengthen{neg_lit}, or
        // .none.
        const d_lits = self.clauseLits(d_cref);
        if (d_lits.len < c_len) {
            op_count.* += 1;
            continue;
        }

        const outcome = checkSubsumeOrSSR(scratch.items, d_lits);
        op_count.* += 1;
        if (outcome != .none and clauseIsLockedAtLevel0(self, d_cref)) continue;

        switch (outcome) {
            .none => {},
            .subsumed => {
                if (!self.clauseIsLearned(d_cref)) self.promoteToIrredundant(c_cref);
                try subsumeClause(self, d_cref, any_deleted);
            },
            .strengthen => |neg_lit| {
                try strengthenLongClause(
                    self,
                    d_cref,
                    neg_lit,
                    occ,
                    revisits,
                    queue,
                    any_deleted,
                    unsat_derived,
                );
                if (unsat_derived.*) return;
            },
        }
    }
}

// Processes a binary clause (a, b) as subsumer.
fn processSubsumerBinary(
    self: *Solver,
    a: Literal,
    b: Literal,
    occ: []std.ArrayList(ClauseRef),
    revisits: *std.AutoHashMap(ClauseRef, u8),
    queue: *std.ArrayList(ClauseRef),
    scratch: *std.ArrayList(Literal),
    op_count: *u64,
    any_deleted: *bool,
    unsat_derived: *bool,
) !void {
    scratch.clearRetainingCapacity();
    try scratch.ensureTotalCapacity(self.allocator, 2);
    scratch.appendAssumeCapacity(a);
    scratch.appendAssumeCapacity(b);

    const c_abs = clauseAbstract(scratch.items);

    // Pivot = shorter occ list.
    const pivot: Literal = if (occ[a.raw].items.len <= occ[b.raw].items.len) a else b;

    var i: usize = 0;
    while (i < occ[pivot.raw].items.len) : (i += 1) {
        if (unsat_derived.*) return;

        const d_cref = occ[pivot.raw].items[i];
        if (self.clauseIsDeleted(d_cref)) continue;

        if ((c_abs & ~clauseAbstract(self.clauseLits(d_cref))) != 0) {
            op_count.* += 1;
            continue;
        }

        const d_lits = self.clauseLits(d_cref);
        if (d_lits.len < 2) {
            op_count.* += 1;
            continue;
        }
        const outcome = checkSubsumeOrSSR(scratch.items, d_lits);
        op_count.* += 1;
        if (outcome != .none and clauseIsLockedAtLevel0(self, d_cref)) continue;
        switch (outcome) {
            .none => {},
            .subsumed => {
                try subsumeClause(self, d_cref, any_deleted);
            },
            .strengthen => |neg_lit| {
                try strengthenLongClause(
                    self,
                    d_cref,
                    neg_lit,
                    occ,
                    revisits,
                    queue,
                    any_deleted,
                    unsat_derived,
                );
                if (unsat_derived.*) return;
            },
        }
    }

    // SSR against other binaries: (a, b) strengthens (a, -b) to unit (a).
    // Scan bin_watchers[b.raw] (entries represent (b.negate(), other)) —
    // we want the specific pair (a, -b) ≡ bin_watchers[b.raw] containing
    // {other = a}. The symmetric half (a, b) vs (-a, b) is covered by the
    // outer iteration over all subsumer binaries.
    try binarySSRAgainstBinaries(self, a, b, unsat_derived);
    if (unsat_derived.*) return;
    try binarySSRAgainstBinaries(self, b, a, unsat_derived);
}

// Looks for a sibling binary (a, -b) that can be strengthened to unit (a)
// by resolving with our subsumer (a, b) on b. Found entries are removed
// from both bin_watchers lists; the unit is DRAT-emitted and assigned at
// level 0.
fn binarySSRAgainstBinaries(
    self: *Solver,
    a: Literal,
    b: Literal,
    unsat_derived: *bool,
) !void {
    // Target clause: (a, -b). Found in bin_watchers[b.raw] as entry
    // {.other = a}.
    const target_idx = b.raw;
    var i: usize = 0;
    while (i < self.bin_watchers[target_idx].items.len) {
        const entry = self.bin_watchers[target_idx].items[i];
        if (entry.other.raw != a.raw) {
            i += 1;
            continue;
        }
        // Found (a, -b). Strengthen to unit (a).
        const unit = a;
        const neg_b = b.negate();

        // Emit proof first: add the stronger clause, then delete the old.
        try self.proof.addClause(&[_]Literal{unit});
        try self.proof.deleteClause(&[_]Literal{ unit, neg_b });

        // Remove from bin_watchers[target_idx] at position i.
        _ = self.bin_watchers[target_idx].swapRemove(i);
        // Remove the sibling entry in bin_watchers[a.negate().raw]
        // whose .other == neg_b (the full clause is (a, -b) so the
        // pair registered the other direction too).
        {
            const sibling_idx = a.negate().raw;
            var j: usize = 0;
            while (j < self.bin_watchers[sibling_idx].items.len) : (j += 1) {
                if (self.bin_watchers[sibling_idx].items[j].other.raw == neg_b.raw) {
                    _ = self.bin_watchers[sibling_idx].swapRemove(j);
                    break;
                }
            }
        }

        self.stats.strengthened += 1;

        // Assign unit or detect conflict.
        const val = self.assignment.valueOfLiteral(unit);
        if (val == .false) {
            unsat_derived.* = true;
            return;
        }
        if (val == .unassigned) {
            try self.assignment.assign(unit, Reason.none);
        }
        // If val == .true already, the unit adds no new info.
        // Do NOT increment i — we swap-removed at i.
        // Continue scanning for further matches (unlikely for a distinct
        // binary, but safe).
    }
}

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
    try self.proof.deleteClause(self.clauseLits(d_cref));
    self.markDeleted(d_cref);
    any_deleted.* = true;
    self.stats.subsumed += 1;
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
    // addClauseToArena may reallocate the arena.
    var new_lits: std.ArrayList(Literal) = .empty;
    defer new_lits.deinit(self.allocator);

    const d_lits_snapshot = self.clauseLits(d_cref);
    const old_lits_copy = try self.allocator.dupe(Literal, d_lits_snapshot);
    defer self.allocator.free(old_lits_copy);

    try new_lits.ensureTotalCapacity(self.allocator, d_lits_snapshot.len);
    for (d_lits_snapshot) |lit| {
        if (lit.raw == neg_lit.raw) continue;
        switch (self.assignment.valueOfLiteral(lit)) {
            .true => return subsumeClause(self, d_cref, any_deleted),
            // Already propagated at level 0, so a watch on it would never fire.
            .false => {},
            .unassigned => new_lits.appendAssumeCapacity(lit),
        }
    }

    const new_len = new_lits.items.len;
    const is_learned = self.clauseIsLearned(d_cref);

    // Emit DRAT add FIRST, then delete (required for DRAT-RUP correctness
    // when the strengthened clause is the resolvent).
    try self.proof.addClause(new_lits.items);
    try self.proof.deleteClause(old_lits_copy);

    // Mark old D deleted.
    self.markDeleted(d_cref);
    any_deleted.* = true;
    self.stats.strengthened += 1;

    if (new_len == 0) {
        unsat_derived.* = true;
        return;
    }

    if (new_len == 1) {
        const unit = new_lits.items[0];
        const val = self.assignment.valueOfLiteral(unit);
        if (val == .false) {
            unsat_derived.* = true;
            return;
        }
        if (val == .unassigned) {
            try self.assignment.assign(unit, Reason.none);
        }
        return;
    }

    if (new_len == 2) {
        const a = new_lits.items[0];
        const bb = new_lits.items[1];
        try self.addBinary(a, bb);
        return;
    }

    // ≥3: install in arena. addClauseToArena may realloc arena — any
    // cached ClauseLits pointer from before is invalid after.
    const new_lbd = clause_mod.rewrittenLbd(self.clauseLbd(d_cref), new_len);
    const new_cref = try self.addClauseToArena(new_lits.items, is_learned, new_lbd);
    try self.attachWatches(new_cref);
    if (is_learned) {
        try self.learned_clauses.append(self.allocator, new_cref);
    }

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

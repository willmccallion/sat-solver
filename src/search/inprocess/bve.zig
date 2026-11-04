const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseRef = core.cnf.ClauseRef;
const clause_mod = core.clause;

const common = @import("common.zig");
const state = @import("../state.zig");
const Solver = state.Solver;
const solver_mod = @import("../solver.zig");
const Result = solver_mod.Result;

// Bounded Variable Elimination (BVE) — resolution-based preprocessing /
// inprocessing. For each variable v, enumerate the resolvents
// (c_pos ∪ c_neg) \ {+v, -v} over every pair of irredundant clauses
// (c_pos, c_neg) with +v ∈ c_pos and -v ∈ c_neg; if the set of
// non-tautological resolvents is no larger than the number of those
// clauses, replace them by the resolvents, delete the
// learned clauses on v, and mark v eliminated. Binaries carry no learned
// flag, so a learned binary counts as irredundant. Variables with too
// many occurrences, resolvents that grow past `max_resolvent_len`, or
// occurrences locked as reasons for level-0 units are skipped.
//
// Occurrence lists are built as a tagged union over LONG arena clauses
// and BINARY clauses in bin_watchers, with a `a.raw < b.raw` dedup to
// visit each binary once. Long clauses marked deleted (deleted_bit set)
// are skipped during build — they are holes in the arena.
//
// Commit order is fixed by the DRAT checker's RUP semantics: all
// resolvents are added first, all originals deleted second, then per-v
// bookkeeping runs. The original literals are buffered into
// `bve_witness_lits` (as length-prefixed runs, two sides: +v side then
// -v side) so the .sat reconstruction in model.zig can give a value to
// every eliminated variable by walking the witness frames in reverse.
//
// Precondition: level == 0; the pass propagates to a fixpoint first. Any
// 1-literal resolvent is asserted as a root-level unit; any empty
// resolvent triggers `.unsat` immediately after emitting an empty DRAT
// clause.
//
// Memory safety: addClauseToArena may reallocate self.arena. Each
// original clause's literals are materialized into a scratch buffer
// before the resolution / commit phase, and no arena slice is held
// across an allocation boundary.

const preprocess_cap: u64 = 50_000_000;
pub const inprocess_initial_interval: u64 = 40_000;
pub const grow_num: u64 = 3;
pub const grow_den: u64 = 2;
const budget_share: common.BudgetShare = .{ .num = 1, .den = 10 };
const inprocess_floor: u64 = 1_000_000;
const max_resolvent_len: u32 = 16;
const max_occ_product: u64 = 10_000;

// Inprocessing entry point, on a share of the propagations since the last
// call. Returns `.unsat` if elimination derives an empty clause or a
// conflicting unit.
pub fn bve(self: *Solver) !?Result {
    if (try self.propagateAtRoot()) |r| return r;
    const share = common.propagationBudget(self.stats.propagations, &self.props_at_last_bve, budget_share);
    return eliminateWithin(self, @max(inprocess_floor, share));
}

// Preprocessing entry point, on the large `preprocess_cap` budget because
// no search has happened yet.
pub fn preprocessBVE(self: *Solver) !?Result {
    if (try self.propagateAtRoot()) |r| return r;
    self.props_at_last_bve = self.stats.propagations;
    return eliminateWithin(self, preprocess_cap);
}

// Tagged occurrence: either a long-clause arena ref, or a binary
// (partner literal). The pivot variable is implied by the owning
// occurrence list index.
const Occurrence = union(enum) {
    long: ClauseRef,
    binary: Literal,
};

fn eliminateWithin(self: *Solver, budget: u64) !?Result {
    std.debug.assert(self.assignment.level == 0);

    const num_vars = self.num_vars;
    const num_lits: usize = @as(usize, num_vars) * 2;

    // Per-literal occurrence lists. Built fresh each call — simpler than
    // maintaining them incrementally, and BVE is not on the hot path.
    var occ: []std.ArrayList(Occurrence) = try self.allocator.alloc(
        std.ArrayList(Occurrence),
        num_lits,
    );
    for (occ) |*o| o.* = .empty;
    defer {
        for (occ) |*o| o.deinit(self.allocator);
        self.allocator.free(occ);
    }

    // Build occurrence lists
    // Sized exactly first: a literal x occurs in its long clauses plus one
    // binary per entry of bin_watchers[¬x].
    {
        const long_counts = try self.allocator.alloc(u32, num_lits);
        defer self.allocator.free(long_counts);
        @memset(long_counts, 0);
        var cref: ClauseRef = 0;
        while (cref < self.arena.items.len) {
            const header = self.arena.items[cref].raw;
            const len = header & clause_mod.len_mask;
            if ((header & clause_mod.deleted_bit) == 0) {
                for (self.clauseLits(cref)) |lit| long_counts[lit.raw] += 1;
            }
            cref += clause_mod.header_slots + len;
        }
        for (occ, long_counts, 0..) |*o, n, lit_raw| {
            const binary_count = self.bin_watchers[lit_raw ^ 1].items.len;
            try o.ensureTotalCapacityPrecise(self.allocator, n + binary_count);
        }
    }

    // Long clauses from the arena.
    {
        var cref: ClauseRef = 0;
        while (cref < self.arena.items.len) {
            const header = self.arena.items[cref].raw;
            const len = header & clause_mod.len_mask;
            const span = clause_mod.header_slots + len;
            if ((header & clause_mod.deleted_bit) == 0) {
                for (self.clauseLits(cref)) |lit| {
                    occ[lit.raw].appendAssumeCapacity(.{ .long = cref });
                }
            }
            cref += span;
        }
    }

    // Binaries from bin_watchers. Each binary (a, b) is registered twice
    // — as .other = b in bin_watchers[a.negate().raw] and as .other = a
    // in bin_watchers[b.negate().raw]. Dedup via raw ordering of the two
    // literals to visit each clause exactly once.
    {
        var l_raw: u32 = 0;
        while (l_raw < num_lits) : (l_raw += 1) {
            const a = (Literal{ .raw = l_raw }).negate();
            for (self.bin_watchers[l_raw].items) |entry| {
                const b = entry.other;
                if (a.raw >= b.raw) continue;
                occ[a.raw].appendAssumeCapacity(.{ .binary = b });
                occ[b.raw].appendAssumeCapacity(.{ .binary = a });
            }
        }
    }

    // Priority heap over variables by |occ(+v)| * |occ(-v)|
    const Entry = struct {
        product: u64,
        var_idx: u32,
    };
    const lessThan = struct {
        fn f(_: void, a: Entry, b: Entry) std.math.Order {
            return std.math.order(a.product, b.product);
        }
    }.f;

    var heap: std.PriorityQueue(Entry, void, lessThan) = .empty;
    defer heap.deinit(self.allocator);

    {
        var v: u32 = 0;
        while (v < num_vars) : (v += 1) {
            if (!self.varIsActive(v)) continue;
            const pos_cnt = occ[Literal.init(v, false).raw].items.len;
            const neg_cnt = occ[Literal.init(v, true).raw].items.len;
            if (pos_cnt == 0 and neg_cnt == 0) continue;
            const prod: u64 = @as(u64, pos_cnt) * @as(u64, neg_cnt);
            if (prod > max_occ_product) {
                @branchHint(.cold);
                continue;
            }
            try heap.push(self.allocator, .{ .product = prod, .var_idx = v });
        }
    }

    // Scratch buffers — all allocated once, reused across all pops.
    var pos_lits_buf: std.ArrayList(Literal) = .empty;
    defer pos_lits_buf.deinit(self.allocator);
    var neg_lits_buf: std.ArrayList(Literal) = .empty;
    defer neg_lits_buf.deinit(self.allocator);
    // Offsets into pos_lits_buf / neg_lits_buf where each original clause's
    // length-prefixed run begins (first slot is the length). Used so we
    // don't hold arena slices across a resolvent addClauseToArena call.
    var pos_runs: std.ArrayList(u32) = .empty;
    defer pos_runs.deinit(self.allocator);
    var neg_runs: std.ArrayList(u32) = .empty;
    defer neg_runs.deinit(self.allocator);
    var resolvent_buf: std.ArrayList(Literal) = .empty;
    defer resolvent_buf.deinit(self.allocator);
    // Non-tautological resolvents kept for the commit phase — a flat
    // buffer of length-prefixed runs, exactly like the witness format.
    var resolvents_flat: std.ArrayList(Literal) = .empty;
    defer resolvents_flat.deinit(self.allocator);
    var resolvents_offsets: std.ArrayList(u32) = .empty;
    defer resolvents_offsets.deinit(self.allocator);

    var op_count: u64 = 0;
    var any_deleted = false;
    var unsat_derived = false;

    outer: while (heap.pop()) |entry| {
        if (op_count > budget or solver_mod.interruptRequested()) {
            @branchHint(.cold);
            break;
        }
        const v = entry.var_idx;

        if (!self.varIsActive(v)) continue;

        const pos_lit = Literal.init(v, false);
        const neg_lit = Literal.init(v, true);

        // Re-read occ sizes — may have changed as prior eliminations
        // appended to occ lists. Skip if now too big.
        const pos_occ = occ[pos_lit.raw].items;
        const neg_occ = occ[neg_lit.raw].items;
        const prod: u64 = @as(u64, pos_occ.len) * @as(u64, neg_occ.len);
        if (prod > max_occ_product) {
            @branchHint(.cold);
            continue;
        }

        // Gather pos and neg clause literals into scratch
        pos_lits_buf.clearRetainingCapacity();
        neg_lits_buf.clearRetainingCapacity();
        pos_runs.clearRetainingCapacity();
        neg_runs.clearRetainingCapacity();

        var pos_live_count: u32 = 0;
        var neg_live_count: u32 = 0;
        var locked = false;

        for (pos_occ) |o| {
            switch (o) {
                .long => |cref| {
                    if (self.clauseIsDeleted(cref)) continue;
                    if (self.clauseIsLocked(cref)) {
                        locked = true;
                        break;
                    }
                    // A learned clause is implied by the irredundant ones, so
                    // it takes no part in resolution; commit deletes it.
                    if (self.clauseIsLearned(cref)) continue;
                    const lits = self.clauseLits(cref);
                    const off: u32 = @intCast(pos_lits_buf.items.len);
                    try pos_runs.append(self.allocator, off);
                    // Length-prefix slot (raw holds the length).
                    try pos_lits_buf.append(
                        self.allocator,
                        .{ .raw = @as(u32, @intCast(lits.len)) },
                    );
                    try pos_lits_buf.appendSlice(self.allocator, lits);
                    pos_live_count += 1;
                },
                .binary => |other| {
                    // Binary entries in occ go stale when `other.variable()`
                    // is itself eliminated: the binary was removed from
                    // bin_watchers during that variable's commit, but the
                    // mirror entry in this lit's occ was never cleaned. Treat
                    // such ghosts as no-ops — including them as a source would
                    // produce resolvents poisoned with an eliminated literal.
                    if (self.eliminated.isSet(other.variable())) continue;
                    // Binary clause {pos_lit, other}.
                    const off: u32 = @intCast(pos_lits_buf.items.len);
                    try pos_runs.append(self.allocator, off);
                    try pos_lits_buf.append(self.allocator, .{ .raw = 2 });
                    try pos_lits_buf.append(self.allocator, pos_lit);
                    try pos_lits_buf.append(self.allocator, other);
                    pos_live_count += 1;
                },
            }
        }
        if (locked) continue;

        for (neg_occ) |o| {
            switch (o) {
                .long => |cref| {
                    if (self.clauseIsDeleted(cref)) continue;
                    if (self.clauseIsLocked(cref)) {
                        locked = true;
                        break;
                    }
                    // A learned clause is implied by the irredundant ones, so
                    // it takes no part in resolution; commit deletes it.
                    if (self.clauseIsLearned(cref)) continue;
                    const lits = self.clauseLits(cref);
                    const off: u32 = @intCast(neg_lits_buf.items.len);
                    try neg_runs.append(self.allocator, off);
                    try neg_lits_buf.append(
                        self.allocator,
                        .{ .raw = @as(u32, @intCast(lits.len)) },
                    );
                    try neg_lits_buf.appendSlice(self.allocator, lits);
                    neg_live_count += 1;
                },
                .binary => |other| {
                    if (self.eliminated.isSet(other.variable())) continue;
                    const off: u32 = @intCast(neg_lits_buf.items.len);
                    try neg_runs.append(self.allocator, off);
                    try neg_lits_buf.append(self.allocator, .{ .raw = 2 });
                    try neg_lits_buf.append(self.allocator, neg_lit);
                    try neg_lits_buf.append(self.allocator, other);
                    neg_live_count += 1;
                },
            }
        }
        if (locked) continue;

        // Skip variables with no live clauses on either side — BVE on
        // them is a no-op that still costs bookkeeping.
        if (pos_live_count == 0 and neg_live_count == 0) continue;

        // Enumerate resolvents
        resolvents_flat.clearRetainingCapacity();
        resolvents_offsets.clearRetainingCapacity();

        var non_taut_count: u32 = 0;
        var abandon = false;
        var empty_found = false;

        for (pos_runs.items) |p_off| {
            if (abandon or empty_found) break;
            const p_len = pos_lits_buf.items[p_off].raw;
            const p_lits = pos_lits_buf.items[p_off + 1 .. p_off + 1 + p_len];

            for (neg_runs.items) |n_off| {
                if (abandon or empty_found) break;
                op_count += 1;
                if (op_count > budget) {
                    @branchHint(.cold);
                    abandon = true;
                    break;
                }
                const n_len = neg_lits_buf.items[n_off].raw;
                const n_lits = neg_lits_buf.items[n_off + 1 .. n_off + 1 + n_len];

                // Build resolvent: (p_lits ∪ n_lits) \ {pos_lit, neg_lit}.
                resolvent_buf.clearRetainingCapacity();
                for (p_lits) |lit| {
                    if (lit.raw == pos_lit.raw) continue;
                    try resolvent_buf.append(self.allocator, lit);
                }
                for (n_lits) |lit| {
                    if (lit.raw == neg_lit.raw) continue;
                    try resolvent_buf.append(self.allocator, lit);
                }

                const resolvent = common.normalizeAtRoot(&self.assignment, resolvent_buf.items) orelse continue;
                const r_len = resolvent.len;
                if (r_len > max_resolvent_len) {
                    @branchHint(.cold);
                    abandon = true;
                    break;
                }
                if (r_len == 0) {
                    empty_found = true;
                    break;
                }

                // Record this resolvent into the flat buffer.
                const off: u32 = @intCast(resolvents_flat.items.len);
                try resolvents_offsets.append(self.allocator, off);
                try resolvents_flat.append(
                    self.allocator,
                    .{ .raw = @as(u32, @intCast(r_len)) },
                );
                try resolvents_flat.appendSlice(self.allocator, resolvent);
                non_taut_count += 1;
            }
        }

        if (empty_found) {
            @branchHint(.cold);
            try self.proof.empty();
            return .unsat;
        }

        if (abandon) {
            // Budget exceeded mid-enumeration OR one resolvent was
            // oversized. Either way, this variable is not worth it —
            // skip it but continue with the next variable in the heap
            // (the budget check at the top of the loop will break out
            // if we've truly blown the budget).
            if (op_count > budget) break :outer;
            continue;
        }

        if (non_taut_count > pos_live_count + neg_live_count) continue;

        try commitElimination(
            self,
            v,
            pos_lit,
            neg_lit,
            &pos_lits_buf,
            &pos_runs,
            &neg_lits_buf,
            &neg_runs,
            &resolvents_flat,
            &resolvents_offsets,
            pos_occ,
            neg_occ,
            occ,
            &any_deleted,
            &unsat_derived,
        );

        if (unsat_derived) break;

        self.stats.eliminated_vars += 1;
        self.stats.resolvents_added += non_taut_count;

        // A unit installed by commit just landed on the trail via
        // assignAtLevel. We DO NOT propagate it here: propagate would
        // walk long-clause watchers that still reference clauses we
        // just marked deleted in step (d), which is unsafe. Instead we
        // let the single post-loop sweep + propagate handle it. If the
        // unit conflicts with an existing level-0 fact, unsat_derived
        // is already set; otherwise the only cost is that later BVE
        // passes in this call don't see the unit's consequences — an
        // acceptable loss vs. the correctness hazard.
    }

    if (unsat_derived) {
        try self.proof.empty();
        return .unsat;
    }

    if (any_deleted) self.dropDeletedClauseRefs();

    if (try self.propagateAtRoot()) |r| return r;

    self.stats.bve_passes += 1;
    return null;
}

// Performs the six-step commit for one variable's elimination:
//   a. emit proof.addClause for each resolvent (in order)
//   b. append pos / neg clause literals to the solver's witness stack
//   c. emit proof.deleteClause for each original clause
//   d. mark every original clause deleted (arena or bin_watchers), and
//      every learned clause on v, emitting its proof deletion
//   e. install each resolvent (unit / binary / long)
//   f. set eliminated bit for v (caller does the stats)
fn commitElimination(
    self: *Solver,
    v: u32,
    pos_lit: Literal,
    neg_lit: Literal,
    pos_lits_buf: *std.ArrayList(Literal),
    pos_runs: *std.ArrayList(u32),
    neg_lits_buf: *std.ArrayList(Literal),
    neg_runs: *std.ArrayList(u32),
    resolvents_flat: *std.ArrayList(Literal),
    resolvents_offsets: *std.ArrayList(u32),
    pos_occ: []const Occurrence,
    neg_occ: []const Occurrence,
    occ: []std.ArrayList(Occurrence),
    any_deleted: *bool,
    unsat_derived: *bool,
) !void {
    // (a) Emit all add-clauses BEFORE any deletes, so a DRAT checker
    // sees each resolvent under the still-live originals.
    for (resolvents_offsets.items) |off| {
        const r_len = resolvents_flat.items[off].raw;
        const r_lits = resolvents_flat.items[off + 1 .. off + 1 + r_len];
        try self.proof.addClause(r_lits);
    }

    // (b) Push the witness frame. Record pos_start, neg_start, end into
    // bve_witness_lits so model.zig can walk the frame in reverse for
    // model reconstruction. Length-prefixed runs carry the original
    // clause literals verbatim.
    const pos_start: u32 = @intCast(self.bve_witness_lits.items.len);
    for (pos_runs.items) |off| {
        const p_len = pos_lits_buf.items[off].raw;
        try self.bve_witness_lits.append(
            self.allocator,
            .{ .raw = p_len },
        );
        try self.bve_witness_lits.appendSlice(
            self.allocator,
            pos_lits_buf.items[off + 1 .. off + 1 + p_len],
        );
    }
    const neg_start: u32 = @intCast(self.bve_witness_lits.items.len);
    for (neg_runs.items) |off| {
        const n_len = neg_lits_buf.items[off].raw;
        try self.bve_witness_lits.append(
            self.allocator,
            .{ .raw = n_len },
        );
        try self.bve_witness_lits.appendSlice(
            self.allocator,
            neg_lits_buf.items[off + 1 .. off + 1 + n_len],
        );
    }
    const witness_end: u32 = @intCast(self.bve_witness_lits.items.len);
    try self.bve_witness_frames.append(self.allocator, .{
        .pivot = v,
        .pos_start = pos_start,
        .neg_start = neg_start,
        .end = witness_end,
    });

    // (c) Emit all delete-clauses for originals.
    for (pos_runs.items) |off| {
        const p_len = pos_lits_buf.items[off].raw;
        const p_lits = pos_lits_buf.items[off + 1 .. off + 1 + p_len];
        try self.proof.deleteClause(p_lits);
    }
    for (neg_runs.items) |off| {
        const n_len = neg_lits_buf.items[off].raw;
        const n_lits = neg_lits_buf.items[off + 1 .. off + 1 + n_len];
        try self.proof.deleteClause(n_lits);
    }

    // (d) Delete originals.
    for (pos_occ) |o| {
        switch (o) {
            .long => |cref| {
                if (self.clauseIsDeleted(cref)) continue;
                if (self.clauseIsLearned(cref)) try self.proof.deleteClause(self.clauseLits(cref));
                self.markDeleted(cref);
                any_deleted.* = true;
            },
            .binary => |other| {
                // Binary (pos_lit, other): swap-remove from both sides.
                self.removeBinary(pos_lit, other);
            },
        }
    }
    for (neg_occ) |o| {
        switch (o) {
            .long => |cref| {
                if (self.clauseIsDeleted(cref)) continue;
                if (self.clauseIsLearned(cref)) try self.proof.deleteClause(self.clauseLits(cref));
                self.markDeleted(cref);
                any_deleted.* = true;
            },
            .binary => |other| {
                self.removeBinary(neg_lit, other);
            },
        }
    }

    // (e) Install resolvents and add them to occ so later variables'
    // commits see them.
    for (resolvents_offsets.items) |off| {
        const r_len_u: u32 = resolvents_flat.items[off].raw;
        const r_len: usize = @intCast(r_len_u);
        const r_lits = resolvents_flat.items[off + 1 .. off + 1 + r_len];

        switch (try self.installClause(r_lits, .irredundant, 0)) {
            .refuted => {
                unsat_derived.* = true;
                return;
            },
            .unit => {},
            .binary => {
                const a = r_lits[0];
                const b = r_lits[1];
                // Extend occ[a] and occ[b] so subsequent pops see this clause.
                try clause_mod.reserveSlot(Occurrence, &occ[a.raw], self.allocator);
                try clause_mod.reserveSlot(Occurrence, &occ[b.raw], self.allocator);
                occ[a.raw].appendAssumeCapacity(.{ .binary = b });
                occ[b.raw].appendAssumeCapacity(.{ .binary = a });
            },
            .long => |new_cref| {
                // Re-fetch: installing may have reallocated the arena.
                for (self.clauseLits(new_cref)) |lit| {
                    try clause_mod.reserveSlot(Occurrence, &occ[lit.raw], self.allocator);
                    occ[lit.raw].appendAssumeCapacity(.{ .long = new_cref });
                }
            },
        }
    }

    // (f) Mark variable eliminated. Stats incremented by caller.
    self.eliminated.set(v);
}

// Reconstruct a satisfying value for every eliminated variable.
//
// Walk bve_witness_frames in reverse elimination order. For each frame,
// if every clause on the -pivot side is already satisfied by at least
// one non-pivot literal under the current assignment, set pivot=true
// (this satisfies all +pivot-side clauses via the pivot literal itself,
// while the -pivot-side clauses are already satisfied by their other
// literals). Otherwise pick pivot=false — by the BVE invariant, at
// least one of the two choices satisfies every original clause that
// touched v, and walking in reverse keeps the dependency chain sound.
//
// Never emits DRAT: this runs strictly after solve() has returned and
// the proof writer (if any) has already seen the final add-sequence.
pub fn reconstructEliminatedVars(self: *Solver) void {
    const frames = self.bve_witness_frames.items;
    if (frames.len == 0) return;

    const lits_buf = self.bve_witness_lits.items;

    var idx: usize = frames.len;
    while (idx > 0) {
        idx -= 1;
        const frame = frames[idx];
        const pivot = frame.pivot;

        // Walk every -pivot clause; confirm each has a satisfied
        // non-pivot literal. If any clause lacks one, pivot=true would
        // leave that clause unsatisfied, so we must flip to pivot=false.
        var pick_true = true;
        var cursor: u32 = frame.neg_start;
        while (cursor < frame.end) {
            const clen: u32 = lits_buf[cursor].raw;
            const clause_lits = lits_buf[cursor + 1 .. cursor + 1 + clen];
            cursor += 1 + clen;

            var clause_satisfied = false;
            for (clause_lits) |lit| {
                if (lit.variable() == pivot) continue;
                if (self.assignment.valueOfLiteral(lit) == .true) {
                    clause_satisfied = true;
                    break;
                }
            }
            if (!clause_satisfied) {
                pick_true = false;
                break;
            }
        }

        const pos_slot = pivot << 1;
        self.assignment.vars[pivot].value = if (pick_true) .true else .false;
        self.assignment.lit_values[pos_slot] =
            if (pick_true) .true else .false;
        self.assignment.lit_values[pos_slot | 1] =
            if (pick_true) .false else .true;
    }
}

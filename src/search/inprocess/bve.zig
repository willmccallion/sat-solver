const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseRef = core.cnf.ClauseRef;
const Reason = core.assignment.Reason;
const clause_mod = core.clause;

const state = @import("../state.zig");
const Solver = state.Solver;
const WitnessFrame = state.WitnessFrame;
const solver_mod = @import("../solver.zig");
const Result = solver_mod.Result;

// Bounded Variable Elimination (BVE) — resolution-based preprocessing /
// inprocessing. For each variable v, enumerate the resolvents
// (c_pos ∪ c_neg) \ {+v, -v} over every pair (c_pos, c_neg) with +v ∈
// c_pos and -v ∈ c_neg; if the set of non-tautological resolvents is no
// larger than |occ(+v)| + |occ(-v)| + growth_slack, replace the original
// clauses by those resolvents and mark v eliminated. Variables with too
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
// -v side) so the .sat branch in main.zig can reconstruct an assignment
// for every eliminated variable by walking the witness frames in reverse.
//
// Preconditions: level == 0 and BCP at fixpoint. Any 1-literal resolvent
// is asserted as a root-level unit; any empty resolvent triggers `.unsat`
// immediately after emitting an empty DRAT clause.
//
// Memory safety: addClauseToArena may reallocate self.arena. Each
// original clause's literals are materialized into a scratch buffer
// before the resolution / commit phase, and no arena slice is held
// across an allocation boundary.

pub const preprocess_cap: u64 = 50_000_000;
pub const inprocess_initial_interval: u64 = 40_000;
pub const grow_num: u64 = 3;
pub const grow_den: u64 = 2;
pub const budget_num: u64 = 1;
pub const budget_den: u64 = 10;
pub const inprocess_floor: u64 = 1_000_000;
pub const max_resolvent_len: u32 = 16;
pub const max_occ_product: u64 = 10_000;
pub const growth_slack: i32 = 0;

// Inprocess entry point. Uses the propagation-derived budget; returns
// `.unsat` if elimination derives an empty clause or a conflicting unit.
pub fn bve(self: *Solver) !?Result {
    return bveImpl(self, false);
}

// Preprocess entry point. Uses the big `preprocess_cap` budget because
// no search has yet happened.
pub fn preprocessBVE(self: *Solver) !?Result {
    return bveImpl(self, true);
}

// Tagged occurrence: either a long-clause arena ref, or a binary
// (partner literal). The pivot variable is implied by the owning
// occurrence list index.
const Occurrence = union(enum) {
    long: ClauseRef,
    binary: Literal,
};

fn bveImpl(self: *Solver, is_preprocess: bool) !?Result {
    std.debug.assert(self.assignment.level == 0);

    const props_start = self.stats.propagations;
    const budget: u64 = blk: {
        if (is_preprocess or self.props_at_last_bve == 0) {
            break :blk preprocess_cap;
        }
        const delta = if (props_start > self.props_at_last_bve)
            props_start - self.props_at_last_bve
        else
            0;
        const raw = (delta * budget_num) / budget_den;
        break :blk @max(inprocess_floor, raw);
    };
    self.props_at_last_bve = props_start;

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

    // --- Build occurrence lists --------------------------------------------
    // Long clauses from the arena.
    {
        var cref: ClauseRef = 0;
        while (cref < self.arena.items.len) {
            const header = self.arena.items[cref].raw;
            const len = header & clause_mod.len_mask;
            const span = clause_mod.header_slots + len;
            if ((header & clause_mod.deleted_bit) == 0 and len >= 1) {
                const lits = self.clauseLits(cref);
                for (lits) |lit| {
                    try occ[lit.raw].append(
                        self.allocator,
                        .{ .long = cref },
                    );
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
            const watcher_lit = Literal{ .raw = l_raw };
            const a = watcher_lit.negate();
            for (self.bin_watchers[l_raw].items) |entry| {
                const b = entry.other;
                // a < b to ensure one-way visit.
                if (a.raw >= b.raw) continue;
                try occ[a.raw].append(
                    self.allocator,
                    .{ .binary = b },
                );
                try occ[b.raw].append(
                    self.allocator,
                    .{ .binary = a },
                );
            }
        }
    }

    // --- Priority heap over variables by |occ(+v)| * |occ(-v)| ----------
    const Entry = struct {
        product: u64,
        var_idx: u32,
    };
    const lessThan = struct {
        fn f(_: void, a: Entry, b: Entry) std.math.Order {
            return std.math.order(a.product, b.product);
        }
    }.f;

    var heap = std.PriorityQueue(Entry, void, lessThan).init(self.allocator, {});
    defer heap.deinit();

    {
        var v: u32 = 0;
        while (v < num_vars) : (v += 1) {
            if (self.eliminated.isSet(v)) continue;
            if (self.assignment.vars[v].value != .unassigned) continue;
            const pos_cnt = occ[Literal.init(v, false).raw].items.len;
            const neg_cnt = occ[Literal.init(v, true).raw].items.len;
            if (pos_cnt == 0 and neg_cnt == 0) continue;
            const prod: u64 = @as(u64, pos_cnt) * @as(u64, neg_cnt);
            if (prod > max_occ_product) {
                @branchHint(.cold);
                continue;
            }
            try heap.add(.{ .product = prod, .var_idx = v });
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

    outer: while (heap.count() > 0) {
        if (unsat_derived) break;
        if (op_count > budget) {
            @branchHint(.cold);
            break;
        }
        const entry = heap.remove();
        const v = entry.var_idx;

        if (self.eliminated.isSet(v)) continue;
        if (self.assignment.vars[v].value != .unassigned) continue;

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

        // --- Gather pos and neg clause literals into scratch ---------------
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
                    if (clauseIsLockedAtLevel0(self, cref)) {
                        locked = true;
                        break;
                    }
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
                    if (clauseIsLockedAtLevel0(self, cref)) {
                        locked = true;
                        break;
                    }
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

        // Skip variables with no live clauses on at least one side —
        // BVE on them is a no-op that still costs bookkeeping.
        if (pos_live_count == 0 and neg_live_count == 0) continue;

        // --- Enumerate resolvents --------------------------------------
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

                // Sort by raw so duplicates are adjacent.
                std.mem.sort(Literal, resolvent_buf.items, {}, struct {
                    fn f(_: void, a: Literal, b: Literal) bool {
                        return a.raw < b.raw;
                    }
                }.f);

                // Dedupe in place. Detect tautology: x and ¬x adjacent
                // means the two raws differ by exactly 1 (x.raw ^ 1 ==
                // ¬x.raw) AND share the same variable bits.
                var w: usize = 0;
                var is_taut = false;
                var prev_raw: u32 = std.math.maxInt(u32);
                for (resolvent_buf.items) |lit| {
                    if (lit.raw == prev_raw) continue;
                    // Tautology if the negation of the previous literal
                    // equals this one — since we sorted, this happens
                    // when (prev_raw ^ 1) == lit.raw AND prev_raw is
                    // even (positive), so lit.raw is odd (negative).
                    if (prev_raw != std.math.maxInt(u32) and (prev_raw ^ 1) == lit.raw) {
                        is_taut = true;
                        break;
                    }
                    resolvent_buf.items[w] = lit;
                    w += 1;
                    prev_raw = lit.raw;
                }

                if (is_taut) {
                    @branchHint(.cold);
                    continue;
                }
                resolvent_buf.shrinkRetainingCapacity(w);

                // Level-0 simplification: drop false-at-level-0 literals and
                // skip this resolvent entirely if any literal is true-at-
                // level-0. Without this, attachWatches can land on a false
                // literal whose negation is already past qhead on the trail,
                // orphaning the clause (watchers never fire).
                var sat_at_l0 = false;
                var sw: usize = 0;
                for (resolvent_buf.items) |lit| {
                    const val = self.assignment.valueOfLiteral(lit);
                    switch (val) {
                        .@"true" => {
                            sat_at_l0 = true;
                            break;
                        },
                        .@"false" => {},
                        .unassigned => {
                            resolvent_buf.items[sw] = lit;
                            sw += 1;
                        },
                    }
                }
                if (sat_at_l0) continue;
                resolvent_buf.shrinkRetainingCapacity(sw);

                const r_len = resolvent_buf.items.len;
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
                try resolvents_flat.appendSlice(self.allocator, resolvent_buf.items);
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

        // Growth test. Signed comparison — slack may be negative in
        // future tunings. Here growth_slack == 0.
        const original_count: i64 = @as(i64, pos_live_count) + @as(i64, neg_live_count);
        const resolvent_count: i64 = @intCast(non_taut_count);
        if (resolvent_count > original_count + growth_slack) continue;

        // --- Commit --------------------------------------------------------
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

        self.stats.eliminated += 1;
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

    // --- Watcher / learned sweep -------------------------------------------
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
            if (!self.clauseIsDeleted(cref)) {
                self.learned_clauses.items[j] = cref;
                j += 1;
            }
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }

    if ((try self.propagate()) != null) {
        try self.proof.empty();
        return .unsat;
    }

    self.stats.bves += 1;
    return null;
}

// Returns true when `cref` is currently the reason for a level-0 literal.
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

// Performs the six-step commit for one variable's elimination:
//   a. emit proof.addClause for each resolvent (in order)
//   b. append pos / neg clause literals to the solver's witness stack
//   c. emit proof.deleteClause for each original clause
//   d. mark every original clause deleted (arena or bin_watchers)
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
    // bve_witness_lits so main.zig can walk the frame in reverse for
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
                self.arena.items[cref].raw |= clause_mod.deleted_bit;
                any_deleted.* = true;
            },
            .binary => |other| {
                // Binary (pos_lit, other): swap-remove from both sides.
                removeBinary(self, pos_lit, other);
            },
        }
    }
    for (neg_occ) |o| {
        switch (o) {
            .long => |cref| {
                if (self.clauseIsDeleted(cref)) continue;
                self.arena.items[cref].raw |= clause_mod.deleted_bit;
                any_deleted.* = true;
            },
            .binary => |other| {
                removeBinary(self, neg_lit, other);
            },
        }
    }

    // (e) Install resolvents. Uses addClauseToArena for ≥3; may
    // realloc the arena. Update occ lists so later variables' commits
    // see the new clauses.
    for (resolvents_offsets.items) |off| {
        const r_len_u: u32 = resolvents_flat.items[off].raw;
        const r_len: usize = @intCast(r_len_u);
        const r_lits = resolvents_flat.items[off + 1 .. off + 1 + r_len];

        if (r_len == 1) {
            const unit = r_lits[0];
            const val = self.assignment.valueOfLiteral(unit);
            if (val == .@"false") {
                unsat_derived.* = true;
                return;
            }
            if (val == .unassigned) {
                try self.assignment.assign(unit, Reason.none);
            }
        } else if (r_len == 2) {
            const a = r_lits[0];
            const b = r_lits[1];
            const w0 = &self.bin_watchers[a.negate().raw];
            const w1 = &self.bin_watchers[b.negate().raw];
            if (w0.items.len == w0.capacity) {
                try w0.ensureTotalCapacity(self.allocator, @max(w0.capacity * 2, 16));
            }
            if (w1.items.len == w1.capacity) {
                try w1.ensureTotalCapacity(self.allocator, @max(w1.capacity * 2, 16));
            }
            w0.appendAssumeCapacity(.{ .other = b });
            w1.appendAssumeCapacity(.{ .other = a });
            // Extend occ[a] and occ[b] so subsequent pops see this clause.
            try occ[a.raw].append(self.allocator, .{ .binary = b });
            try occ[b.raw].append(self.allocator, .{ .binary = a });
        } else {
            const lbd = self.computeLbd(r_lits);
            const new_cref = try self.addClauseToArena(r_lits, false, lbd);
            try self.attachWatches(new_cref);
            // Do NOT append to learned_clauses — these are effectively
            // new originals derived by resolution.

            // Register with occ. We must re-fetch the slice since
            // addClauseToArena may have reallocated the arena.
            const new_lits = self.clauseLits(new_cref);
            for (new_lits) |lit| {
                try occ[lit.raw].append(self.allocator, .{ .long = new_cref });
            }
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
        var pivot_true_ok = true;
        var cursor: u32 = frame.neg_start;
        while (cursor < frame.end) {
            const clen: u32 = lits_buf[cursor].raw;
            const clause_lits = lits_buf[cursor + 1 .. cursor + 1 + clen];
            cursor += 1 + clen;

            var clause_satisfied = false;
            for (clause_lits) |lit| {
                if (lit.variable() == pivot) continue;
                if (self.assignment.valueOfLiteral(lit) == .@"true") {
                    clause_satisfied = true;
                    break;
                }
            }
            if (!clause_satisfied) {
                pivot_true_ok = false;
                break;
            }
        }

        const pick_true = pivot_true_ok;
        const pos_slot = pivot << 1;
        self.assignment.vars[pivot].value = if (pick_true) .@"true" else .@"false";
        self.assignment.lit_values[pos_slot] =
            if (pick_true) .@"true" else .@"false";
        self.assignment.lit_values[pos_slot | 1] =
            if (pick_true) .@"false" else .@"true";
    }
}

// Swap-remove the binary (a, other) from both sides of bin_watchers.
// Each binary clause is represented as .other=b in bin_watchers[a.negate()]
// and .other=a in bin_watchers[b.negate()]. Remove both halves.
fn removeBinary(self: *Solver, a: Literal, other: Literal) void {
    const a_neg_idx = a.negate().raw;
    var i: usize = 0;
    while (i < self.bin_watchers[a_neg_idx].items.len) {
        if (self.bin_watchers[a_neg_idx].items[i].other.raw == other.raw) {
            _ = self.bin_watchers[a_neg_idx].swapRemove(i);
            break;
        }
        i += 1;
    }
    const other_neg_idx = other.negate().raw;
    var j: usize = 0;
    while (j < self.bin_watchers[other_neg_idx].items.len) {
        if (self.bin_watchers[other_neg_idx].items[j].other.raw == a.raw) {
            _ = self.bin_watchers[other_neg_idx].swapRemove(j);
            break;
        }
        j += 1;
    }
}

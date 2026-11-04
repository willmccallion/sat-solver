const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseList = core.cnf.ClauseList;
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
// bookkeeping runs. The original clauses are logged to `bve_witness`
// (+v side, then -v side) so the .sat reconstruction in model.zig can give
// a value to every eliminated variable by walking the frames in reverse.
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
        var live = self.liveClauses();
        while (live.next()) |cref| {
            for (self.clauseLits(cref)) |lit| long_counts[lit.raw] += 1;
        }
        for (occ, long_counts, 0..) |*o, n, lit_raw| {
            const binary_count = self.bin_watchers[lit_raw ^ 1].items.len;
            try o.ensureTotalCapacityPrecise(self.allocator, n + binary_count);
        }
    }

    // Long clauses from the arena.
    {
        var live = self.liveClauses();
        while (live.next()) |cref| {
            for (self.clauseLits(cref)) |lit| {
                occ[lit.raw].appendAssumeCapacity(.{ .long = cref });
            }
        }
    }

    // Binaries, once each.
    {
        var binaries = self.binaryClauses();
        while (binaries.next()) |pair| {
            occ[pair[0].raw].appendAssumeCapacity(.{ .binary = pair[1] });
            occ[pair[1].raw].appendAssumeCapacity(.{ .binary = pair[0] });
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

    // Scratch buffers — all allocated once, reused across all pops. The
    // clauses on each side are copied out so no arena slice is held while
    // installing a resolvent reallocates the arena.
    var pos_clauses: ClauseList = .{};
    defer pos_clauses.deinit(self.allocator);
    var neg_clauses: ClauseList = .{};
    defer neg_clauses.deinit(self.allocator);
    var resolvent_buf: std.ArrayList(Literal) = .empty;
    defer resolvent_buf.deinit(self.allocator);
    // Non-tautological resolvents kept for the commit phase.
    var resolvents: ClauseList = .{};
    defer resolvents.deinit(self.allocator);

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
        pos_clauses.clearRetainingCapacity();
        neg_clauses.clearRetainingCapacity();

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
                    try pos_clauses.append(self.allocator, self.clauseLits(cref));
                },
                .binary => |other| {
                    // Binary entries in occ go stale when `other.variable()`
                    // is itself eliminated: the binary was removed from
                    // bin_watchers during that variable's commit, but the
                    // mirror entry in this lit's occ was never cleaned. Treat
                    // such ghosts as no-ops — including them as a source would
                    // produce resolvents poisoned with an eliminated literal.
                    if (self.eliminated.isSet(other.variable())) continue;
                    try pos_clauses.append(self.allocator, &.{ pos_lit, other });
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
                    try neg_clauses.append(self.allocator, self.clauseLits(cref));
                },
                .binary => |other| {
                    if (self.eliminated.isSet(other.variable())) continue;
                    try neg_clauses.append(self.allocator, &.{ neg_lit, other });
                },
            }
        }
        if (locked) continue;

        // Skip variables with no live clauses on either side — BVE on
        // them is a no-op that still costs bookkeeping.
        if (pos_clauses.count() == 0 and neg_clauses.count() == 0) continue;

        // Enumerate resolvents
        resolvents.clearRetainingCapacity();

        var abandon = false;
        var empty_found = false;

        for (0..pos_clauses.count()) |p| {
            if (abandon or empty_found) break;
            const p_lits = pos_clauses.get(p);

            for (0..neg_clauses.count()) |n| {
                if (abandon or empty_found) break;
                op_count += 1;
                if (op_count > budget) {
                    @branchHint(.cold);
                    abandon = true;
                    break;
                }
                const n_lits = neg_clauses.get(n);

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

                try resolvents.append(self.allocator, resolvent);
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

        if (resolvents.count() > pos_clauses.count() + neg_clauses.count()) continue;

        try commitElimination(
            self,
            v,
            pos_lit,
            neg_lit,
            &pos_clauses,
            &neg_clauses,
            &resolvents,
            pos_occ,
            neg_occ,
            occ,
            &any_deleted,
            &unsat_derived,
        );

        if (unsat_derived) break;

        self.stats.eliminated_vars += 1;
        self.stats.resolvents_added += resolvents.count();

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
    pos_clauses: *const ClauseList,
    neg_clauses: *const ClauseList,
    resolvents: *const ClauseList,
    pos_occ: []const Occurrence,
    neg_occ: []const Occurrence,
    occ: []std.ArrayList(Occurrence),
    any_deleted: *bool,
    unsat_derived: *bool,
) !void {
    // (a) Emit all add-clauses BEFORE any deletes, so a DRAT checker
    // sees each resolvent under the still-live originals.
    for (0..resolvents.count()) |i| try self.proof.addClause(resolvents.get(i));

    // (b) Push the witness frame so model.zig can walk it in reverse for
    // model reconstruction.
    const pos_start: u32 = @intCast(self.bve_witness.count());
    for (0..pos_clauses.count()) |i| try self.bve_witness.append(self.allocator, pos_clauses.get(i));
    const neg_start: u32 = @intCast(self.bve_witness.count());
    for (0..neg_clauses.count()) |i| try self.bve_witness.append(self.allocator, neg_clauses.get(i));
    try self.bve_witness_frames.append(self.allocator, .{
        .pivot = v,
        .pos_start = pos_start,
        .neg_start = neg_start,
        .end = @intCast(self.bve_witness.count()),
    });

    // (c) Emit all delete-clauses for originals.
    for (0..pos_clauses.count()) |i| try self.proof.deleteClause(pos_clauses.get(i));
    for (0..neg_clauses.count()) |i| try self.proof.deleteClause(neg_clauses.get(i));

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
    for (0..resolvents.count()) |i| {
        const r_lits = resolvents.get(i);
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

    var idx: usize = frames.len;
    while (idx > 0) {
        idx -= 1;
        const frame = frames[idx];
        const pivot = frame.pivot;

        // Walk every -pivot clause; confirm each has a satisfied
        // non-pivot literal. If any clause lacks one, pivot=true would
        // leave that clause unsatisfied, so we must flip to pivot=false.
        var pick_true = true;
        for (frame.neg_start..frame.end) |i| {
            const clause_lits = self.bve_witness.get(i);
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

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

fn eliminateWithin(self: *Solver, budget: u64) !?Result {
    std.debug.assert(self.assignment.level == 0);

    var pass = try Elimination.init(self, budget);
    defer pass.deinit();
    try pass.run();
    if (pass.refuted) {
        try self.proof.empty();
        return .unsat;
    }

    if (pass.any_deleted) self.dropDeletedClauseRefs();
    if (try self.propagateAtRoot()) |r| return r;
    self.stats.bve_passes += 1;
    return null;
}

// A clause containing a literal: an arena clause, or a binary named by
// its other literal.
const Occurrence = union(enum) {
    long: ClauseRef,
    binary: Literal,
};

// A variable to try eliminating, ordered by the product of its occurrence
// counts, which bounds how many resolvents it can have.
const Candidate = struct {
    product: u64,
    var_idx: u32,

    fn order(_: void, a: Candidate, b: Candidate) std.math.Order {
        return std.math.order(a.product, b.product);
    }
};

const Resolution = enum { complete, abandoned, refuted };

// One elimination pass over the clause database.
const Elimination = struct {
    solver: *Solver,
    // Per-literal occurrence lists, built fresh each pass.
    occ: []std.ArrayList(Occurrence),
    candidates: std.PriorityQueue(Candidate, void, Candidate.order) = .empty,
    // The clauses on each side of the current variable, copied out so no
    // arena slice is held while installing a resolvent reallocates it.
    pos_clauses: ClauseList = .{},
    neg_clauses: ClauseList = .{},
    resolvent_buf: std.ArrayList(Literal) = .empty,
    // The current variable's non-tautological resolvents.
    resolvents: ClauseList = .{},
    // Resolvents built.
    op_count: u64 = 0,
    budget: u64,
    any_deleted: bool = false,
    // Set once the pass derives an empty clause or a conflicting unit.
    refuted: bool = false,

    fn init(solver: *Solver, budget: u64) !Elimination {
        const occ = try solver.allocator.alloc(std.ArrayList(Occurrence), @as(usize, solver.num_vars) * 2);
        for (occ) |*o| o.* = .empty;
        var self: Elimination = .{ .solver = solver, .occ = occ, .budget = budget };
        errdefer self.deinit();
        try self.collectOccurrences();
        try self.queueCandidates();
        return self;
    }

    fn deinit(self: *Elimination) void {
        const allocator = self.solver.allocator;
        for (self.occ) |*o| o.deinit(allocator);
        allocator.free(self.occ);
        self.candidates.deinit(allocator);
        self.pos_clauses.deinit(allocator);
        self.neg_clauses.deinit(allocator);
        self.resolvent_buf.deinit(allocator);
        self.resolvents.deinit(allocator);
    }

    // Sized exactly first: a literal x occurs in its long clauses plus one
    // binary per entry of bin_watchers[¬x].
    fn collectOccurrences(self: *Elimination) !void {
        const solver = self.solver;
        const long_counts = try solver.allocator.alloc(u32, self.occ.len);
        defer solver.allocator.free(long_counts);
        @memset(long_counts, 0);
        var live = solver.liveClauses();
        while (live.next()) |cref| {
            for (solver.clauseLits(cref)) |lit| long_counts[lit.raw] += 1;
        }
        for (self.occ, long_counts, 0..) |*o, n, lit_raw| {
            const binary_count = solver.bin_watchers[lit_raw ^ 1].items.len;
            try o.ensureTotalCapacityPrecise(solver.allocator, n + binary_count);
        }

        live = solver.liveClauses();
        while (live.next()) |cref| {
            for (solver.clauseLits(cref)) |lit| self.occ[lit.raw].appendAssumeCapacity(.{ .long = cref });
        }
        var binaries = solver.binaryClauses();
        while (binaries.next()) |pair| {
            self.occ[pair[0].raw].appendAssumeCapacity(.{ .binary = pair[1] });
            self.occ[pair[1].raw].appendAssumeCapacity(.{ .binary = pair[0] });
        }
    }

    fn queueCandidates(self: *Elimination) !void {
        for (0..self.solver.num_vars) |idx| {
            const v: u32 = @intCast(idx);
            if (!self.solver.varIsActive(v)) continue;
            const pos_count = self.occ[Literal.init(v, false).raw].items.len;
            const neg_count = self.occ[Literal.init(v, true).raw].items.len;
            if (pos_count == 0 and neg_count == 0) continue;
            const product = self.occurrenceProduct(v);
            if (product > max_occ_product) {
                @branchHint(.cold);
                continue;
            }
            try self.candidates.push(self.solver.allocator, .{ .product = product, .var_idx = v });
        }
    }

    fn occurrenceProduct(self: *const Elimination, v: u32) u64 {
        const pos_count: u64 = self.occ[Literal.init(v, false).raw].items.len;
        const neg_count: u64 = self.occ[Literal.init(v, true).raw].items.len;
        return pos_count * neg_count;
    }

    fn isOverBudget(self: *const Elimination) bool {
        return self.op_count > self.budget;
    }

    // Units that a commit asserts are propagated only once the pass ends:
    // until the sweep, watchers still point at the clauses it deleted.
    fn run(self: *Elimination) !void {
        while (self.candidates.pop()) |candidate| {
            if (self.isOverBudget() or solver_mod.interruptRequested()) {
                @branchHint(.cold);
                return;
            }
            try self.tryEliminate(candidate.var_idx);
            if (self.refuted) return;
        }
    }

    fn tryEliminate(self: *Elimination, v: u32) !void {
        if (!self.solver.varIsActive(v)) return;
        // Earlier eliminations append to occ, so the product is re-checked.
        if (self.occurrenceProduct(v) > max_occ_product) {
            @branchHint(.cold);
            return;
        }
        const pos_lit = Literal.init(v, false);
        if (!try self.gatherSide(pos_lit, &self.pos_clauses)) return;
        if (!try self.gatherSide(pos_lit.negate(), &self.neg_clauses)) return;
        const original_count = self.pos_clauses.count() + self.neg_clauses.count();
        if (original_count == 0) return;

        switch (try self.resolveSides(pos_lit)) {
            .complete => {},
            .abandoned => return,
            .refuted => {
                self.refuted = true;
                return;
            },
        }
        if (self.resolvents.count() > original_count) return;

        try self.commit(v);
        if (self.refuted) return;
        self.solver.stats.eliminated_vars += 1;
        self.solver.stats.resolvents_added += self.resolvents.count();
    }

    // Copies the irredundant clauses containing `lit` into `clauses`;
    // false when one of them is locked, which rules out eliminating it.
    fn gatherSide(self: *Elimination, lit: Literal, clauses: *ClauseList) !bool {
        const solver = self.solver;
        clauses.clearRetainingCapacity();
        for (self.occ[lit.raw].items) |o| {
            switch (o) {
                .long => |cref| {
                    if (solver.clauseIsDeleted(cref)) continue;
                    if (solver.clauseIsLocked(cref)) return false;
                    // A learned clause is implied by the irredundant ones, so
                    // it takes no part in resolution; the commit deletes it.
                    if (solver.clauseIsLearned(cref)) continue;
                    try clauses.append(solver.allocator, solver.clauseLits(cref));
                },
                .binary => |other| {
                    // A binary's mirror entry outlives it once `other`'s
                    // variable is eliminated; resolving on it would bring
                    // that variable back.
                    if (solver.eliminated.isSet(other.variable())) continue;
                    try clauses.append(solver.allocator, &.{ lit, other });
                },
            }
        }
        return true;
    }

    // Collects the resolvents on `pos_lit`'s variable of every pos/neg
    // clause pair, abandoning the variable once the budget is spent or a
    // resolvent grows past `max_resolvent_len`.
    fn resolveSides(self: *Elimination, pos_lit: Literal) !Resolution {
        self.resolvents.clearRetainingCapacity();
        for (0..self.pos_clauses.count()) |p| {
            for (0..self.neg_clauses.count()) |n| {
                self.op_count += 1;
                if (self.isOverBudget()) {
                    @branchHint(.cold);
                    return .abandoned;
                }
                const resolvent = (try self.resolve(self.pos_clauses.get(p), self.neg_clauses.get(n), pos_lit)) orelse continue;
                if (resolvent.len > max_resolvent_len) {
                    @branchHint(.cold);
                    return .abandoned;
                }
                if (resolvent.len == 0) return .refuted;
                try self.resolvents.append(self.solver.allocator, resolvent);
            }
        }
        return .complete;
    }

    // The resolvent of `p_lits` and `n_lits` on `pos_lit`'s variable,
    // normalized at level 0; null when it is a tautology or satisfied.
    fn resolve(self: *Elimination, p_lits: []const Literal, n_lits: []const Literal, pos_lit: Literal) !?[]Literal {
        const allocator = self.solver.allocator;
        self.resolvent_buf.clearRetainingCapacity();
        for (p_lits) |lit| {
            if (!lit.eql(pos_lit)) try self.resolvent_buf.append(allocator, lit);
        }
        for (n_lits) |lit| {
            if (!lit.eql(pos_lit.negate())) try self.resolvent_buf.append(allocator, lit);
        }
        return common.normalizeAtRoot(&self.solver.assignment, self.resolvent_buf.items);
    }

    // Replaces v's clauses by its resolvents. A DRAT checker must see every
    // resolvent while the originals are still live, so all adds come first.
    fn commit(self: *Elimination, v: u32) !void {
        const solver = self.solver;
        const pos_lit = Literal.init(v, false);
        for (0..self.resolvents.count()) |i| try solver.proof.addClause(self.resolvents.get(i));
        try self.recordWitness(v);
        for (0..self.pos_clauses.count()) |i| try solver.proof.deleteClause(self.pos_clauses.get(i));
        for (0..self.neg_clauses.count()) |i| try solver.proof.deleteClause(self.neg_clauses.get(i));
        try self.deleteOccurrences(pos_lit);
        try self.deleteOccurrences(pos_lit.negate());
        try self.installResolvents();
        if (self.refuted) return;
        solver.eliminated.set(v);
    }

    // Logs v's clauses so model reconstruction can give v a value.
    fn recordWitness(self: *Elimination, v: u32) !void {
        const solver = self.solver;
        const witness = &solver.bve_witness;
        const pos_start: u32 = @intCast(witness.count());
        for (0..self.pos_clauses.count()) |i| try witness.append(solver.allocator, self.pos_clauses.get(i));
        const neg_start: u32 = @intCast(witness.count());
        for (0..self.neg_clauses.count()) |i| try witness.append(solver.allocator, self.neg_clauses.get(i));
        try solver.bve_witness_frames.append(solver.allocator, .{
            .pivot = v,
            .pos_start = pos_start,
            .neg_start = neg_start,
            .end = @intCast(witness.count()),
        });
    }

    // Deletes every clause containing `lit`, learned ones included, since
    // its variable is leaving the formula.
    fn deleteOccurrences(self: *Elimination, lit: Literal) !void {
        const solver = self.solver;
        for (self.occ[lit.raw].items) |o| {
            switch (o) {
                .long => |cref| {
                    if (solver.clauseIsDeleted(cref)) continue;
                    if (solver.clauseIsLearned(cref)) try solver.proof.deleteClause(solver.clauseLits(cref));
                    solver.markDeleted(cref);
                    self.any_deleted = true;
                },
                .binary => |other| solver.removeBinary(lit, other),
            }
        }
    }

    // Installs the resolvents and adds them to occ so later variables'
    // commits see them.
    fn installResolvents(self: *Elimination) !void {
        for (0..self.resolvents.count()) |i| {
            const lits = self.resolvents.get(i);
            switch (try self.solver.installClause(lits, .irredundant, 0)) {
                .refuted => {
                    self.refuted = true;
                    return;
                },
                .unit => {},
                .binary => {
                    try self.addOccurrence(lits[0], .{ .binary = lits[1] });
                    try self.addOccurrence(lits[1], .{ .binary = lits[0] });
                },
                .long => |cref| for (lits) |lit| try self.addOccurrence(lit, .{ .long = cref }),
            }
        }
    }

    fn addOccurrence(self: *Elimination, lit: Literal, occurrence: Occurrence) !void {
        try clause_mod.reserveSlot(Occurrence, &self.occ[lit.raw], self.solver.allocator);
        self.occ[lit.raw].appendAssumeCapacity(occurrence);
    }
};

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
    var idx: usize = frames.len;
    while (idx > 0) {
        idx -= 1;
        self.assignment.setValue(frames[idx].pivot, negativeSideHolds(self, frames[idx]));
    }
}

// Whether every ¬pivot clause of `frame` has a true literal besides the
// pivot's, so that pivot = true satisfies both sides.
fn negativeSideHolds(self: *const Solver, frame: state.WitnessFrame) bool {
    for (frame.neg_start..frame.end) |i| {
        const holds = for (self.bve_witness.get(i)) |lit| {
            if (lit.variable() != frame.pivot and self.assignment.valueOfLiteral(lit) == .true) break true;
        } else false;
        if (!holds) return false;
    }
    return true;
}

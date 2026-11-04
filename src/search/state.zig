const std = @import("std");
const Allocator = std.mem.Allocator;

const core = @import("core");
const cnf = core.cnf;
const Literal = cnf.Literal;
const Formula = cnf.Formula;
const ClauseRef = cnf.ClauseRef;
const assignment_mod = core.assignment;
const Assignment = assignment_mod.Assignment;
const Reason = assignment_mod.Reason;
const clause_mod = core.clause;
const Watcher = clause_mod.Watcher;
const BinaryWatch = clause_mod.BinaryWatch;
const ClauseKind = clause_mod.ClauseKind;
const learned_bit = clause_mod.learned_bit;
const deleted_bit = clause_mod.deleted_bit;
const len_mask = clause_mod.len_mask;
const header_slots = clause_mod.header_slots;

const heuristics = @import("heuristics");
const order_heap_mod = heuristics.order_heap;
const OrderHeap = order_heap_mod.OrderHeap;
const rephase_mod = heuristics.rephase;
const mode_mod = heuristics.mode;

const io = @import("io");

pub const Stats = struct {
    decisions: u64 = 0,
    propagations: u64 = 0,
    conflicts: u64 = 0,
    restarts: u64 = 0,
    learned_clauses: u64 = 0,
    reductions: u64 = 0,
    deleted_clauses: u64 = 0,
    rephases: u64 = 0,
    chrono_backtracks: u64 = 0,
    probe_passes: u64 = 0,
    failed_literal_units: u64 = 0,
    vivify_passes: u64 = 0,
    vivified_clauses: u64 = 0,
    subsume_passes: u64 = 0,
    subsumed_clauses: u64 = 0,
    strengthened_clauses: u64 = 0,
    mode_switches: u64 = 0,
    compactions: u64 = 0,
    bve_passes: u64 = 0,
    eliminated_vars: u64 = 0,
    resolvents_added: u64 = 0,
    equiv_passes: u64 = 0,
    equiv_substituted_vars: u64 = 0,
};

// BVE witness frame. Records the original clauses touching an eliminated
// variable so the .sat reconstruction in model.zig can pick a value
// that satisfies all of them in reverse elimination order.
//
// Layout inside bve_witness_lits (length-prefixed runs):
//   [pos_start .. neg_start)  — clauses containing +pivot
//   [neg_start .. end)        — clauses containing -pivot
// Each run starts with a `Literal` whose `.raw` is the clause length,
// followed by that many literal slots.
pub const WitnessFrame = struct {
    pivot: u32,
    pos_start: u32,
    neg_start: u32,
    end: u32,
};

// Equivalent-literal substitution witness. One frame per variable folded
// into a representative during equiv(). Reconstruction sets the eliminated
// variable's value equal to the representative literal's current value.
pub const EquivFrame = struct {
    eliminated_var: u32,
    rep_lit: cnf.Literal,
};

// Whether a level-0 unit is consistent with the root assignment.
pub const RootUnit = enum { consistent, refuted };

// Where `Solver.installClause` put a clause.
pub const Installed = union(enum) {
    refuted,
    unit,
    binary,
    long: ClauseRef,
};

pub const Solver = struct {
    allocator: Allocator,
    num_vars: u32,

    // Clause arena. Every original (length >= 3) and learned clause lives
    // in this single flat buffer; ClauseRef is an index of its header.
    // See core/clause.zig for the on-disk layout.
    arena: std.ArrayList(Literal),
    watchers: []std.ArrayList(Watcher),

    // Per-literal binary watcher lists. Indexed by literal.raw. Each
    // entry carries the partner literal directly — no clause ref, no
    // arena load. Propagation never moves an entry, since a 2-clause has no
    // other literal to watch; subsume, equiv and BVE swap-remove the
    // entries of binaries they delete.
    bin_watchers: []std.ArrayList(BinaryWatch),

    assignment: Assignment,

    activities: []f64,
    var_inc: f64,
    order_heap: OrderHeap,

    analyze_seen: []bool,
    analyze_learned: std.ArrayList(Literal),
    analyze_levels: std.ArrayList(u32),
    analyze_to_clear: std.ArrayList(u32),
    analyze_stack: std.ArrayList(u32),

    learned_clauses: std.ArrayList(ClauseRef),
    max_learned: usize,

    proof: io.drat.Writer,

    // Glucose restart state. Each EMA carries a bias-correction
    // accumulator (`_bc`) that normalizes the raw sum for the Adam-style
    // `value / bc` unbiased estimate. The bc fields start at 0 and
    // asymptote to 1.
    lbd_fast: f64,
    lbd_fast_bc: f64,
    lbd_slow: f64,
    lbd_slow_bc: f64,
    trail_fast: f64,
    trail_fast_bc: f64,
    conflicts_since_restart: u64,

    next_reduce: u64,
    reduce_interval: u64,

    // Rephase state. `best_trail_len` tracks the longest partial
    // assignment seen at a conflict point — each new peak writes its
    // polarities into assignment.best_phases.
    best_trail_len: usize,
    rephase_next: u64,
    rephase_interval: u64,
    rephase_kind: rephase_mod.RephaseKind,

    // Failed literal probing cadence.
    next_probe: u64,
    probe_interval: u64,
    props_at_last_probe: u64,

    // Vivification cadence.
    next_vivify: u64,
    vivify_interval: u64,
    props_at_last_vivify: u64,

    // Subsumption cadence.
    next_subsume: u64,
    subsume_interval: u64,
    props_at_last_subsume: u64,

    // BVE — bit-indexed by variable. Eliminated variables must never be
    // branched on (pickBranching filters them), must never reappear as a
    // literal in a learned clause, and must have their values filled in
    // during the .sat reconstruction in model.zig.
    eliminated: std.DynamicBitSet,
    // Flat buffer of length-prefixed literal runs recording the original
    // clauses touching every eliminated variable. Each frame in
    // bve_witness_frames names the pivot and slices into this buffer.
    bve_witness_lits: std.ArrayList(Literal),
    bve_witness_frames: std.ArrayList(WitnessFrame),
    next_bve: u64,
    bve_interval: u64,
    props_at_last_bve: u64,

    // Equivalent-literal substitution cadence + witness.
    equiv_witness: std.ArrayList(EquivFrame),
    next_equiv: u64,
    equiv_interval: u64,

    // Focused/stable alternation.
    search_mode: mode_mod.SearchMode,
    mode_budget: u64,
    next_mode_switch: u64,

    // Arena slots held by deleted clauses; compaction runs once they
    // make up half the arena.
    arena_dead_slots: usize,

    unsat_at_init: bool,

    stats: Stats,

    // Large algorithm bodies live in sibling files as free functions
    // taking *Solver. Aliasing them here lets callers use the natural
    // `solver.propagate()` method syntax.
    pub const propagate = @import("propagate.zig").propagate;
    pub const propagateAtRoot = @import("propagate.zig").propagateAtRoot;
    pub const analyze = @import("analyze.zig").analyze;
    pub const computeLbd = @import("analyze.zig").computeLbd;
    pub const backtrack = @import("backtrack.zig").backtrack;
    pub const solve = @import("solve.zig").solve;
    pub const extendModel = @import("model.zig").extendModel;
    pub const findFalsifiedClause = @import("model.zig").findFalsifiedClause;
    pub const probe = @import("inprocess/probe.zig").probe;
    pub const vivify = @import("inprocess/vivify.zig").vivify;
    pub const subsume = @import("inprocess/subsume.zig").subsume;
    pub const preprocessSubsume = @import("inprocess/subsume.zig").preprocessSubsume;
    pub const bve = @import("inprocess/bve.zig").bve;
    pub const preprocessBVE = @import("inprocess/bve.zig").preprocessBVE;
    pub const equiv = @import("inprocess/equiv.zig").equiv;
    pub const reduceDB = @import("inprocess/reduce.zig").reduceDB;
    pub const compact = @import("inprocess/reduce.zig").compact;

    pub fn init(allocator: Allocator, formula: *const Formula) !Solver {
        var self: Solver = .{
            .allocator = allocator,
            .num_vars = formula.num_vars,
            .arena = .empty,
            .watchers = &.{},
            .bin_watchers = &.{},
            .assignment = try Assignment.init(allocator, formula.num_vars),
            .activities = &.{},
            .var_inc = 1.0,
            .order_heap = undefined,
            .analyze_seen = &.{},
            .analyze_learned = .empty,
            .analyze_levels = .empty,
            .analyze_to_clear = .empty,
            .analyze_stack = .empty,
            .learned_clauses = .empty,
            .max_learned = @max(formula.clauseCount(), @import("inprocess/reduce.zig").min_max_learned),
            .proof = .{},
            .lbd_fast = 0,
            .lbd_fast_bc = 0,
            .lbd_slow = 0,
            .lbd_slow_bc = 0,
            .trail_fast = 0,
            .trail_fast_bc = 0,
            .conflicts_since_restart = 0,
            .next_reduce = @import("inprocess/reduce.zig").initial_interval,
            .reduce_interval = @import("inprocess/reduce.zig").initial_interval,
            .best_trail_len = 0,
            .rephase_next = rephase_mod.rephase_initial,
            .rephase_interval = rephase_mod.rephase_initial,
            .rephase_kind = .best,
            .next_probe = @import("inprocess/probe.zig").initial_interval,
            .probe_interval = @import("inprocess/probe.zig").initial_interval,
            .props_at_last_probe = 0,
            .next_vivify = @import("inprocess/vivify.zig").initial_interval,
            .vivify_interval = @import("inprocess/vivify.zig").initial_interval,
            .props_at_last_vivify = 0,
            .next_subsume = @import("inprocess/subsume.zig").inprocess_initial_interval,
            .subsume_interval = @import("inprocess/subsume.zig").inprocess_initial_interval,
            .props_at_last_subsume = 0,
            .eliminated = undefined,
            .bve_witness_lits = .empty,
            .bve_witness_frames = .empty,
            .next_bve = @import("inprocess/bve.zig").inprocess_initial_interval,
            .bve_interval = @import("inprocess/bve.zig").inprocess_initial_interval,
            .props_at_last_bve = 0,
            .equiv_witness = .empty,
            .next_equiv = @import("inprocess/equiv.zig").inprocess_initial_interval,
            .equiv_interval = @import("inprocess/equiv.zig").inprocess_initial_interval,
            .search_mode = .focused,
            .mode_budget = mode_mod.stable_initial_budget,
            .next_mode_switch = mode_mod.stable_initial_budget,
            .arena_dead_slots = 0,
            .unsat_at_init = false,
            .stats = .{},
        };
        errdefer self.assignment.deinit();

        self.eliminated = try std.DynamicBitSet.initEmpty(allocator, formula.num_vars);
        errdefer self.eliminated.deinit();

        self.watchers = try allocator.alloc(std.ArrayList(Watcher), formula.num_vars * 2);
        for (self.watchers) |*w| w.* = .empty;
        errdefer {
            for (self.watchers) |*w| w.deinit(allocator);
            allocator.free(self.watchers);
        }

        self.bin_watchers = try allocator.alloc(std.ArrayList(BinaryWatch), formula.num_vars * 2);
        for (self.bin_watchers) |*w| w.* = .empty;
        errdefer {
            for (self.bin_watchers) |*w| w.deinit(allocator);
            allocator.free(self.bin_watchers);
        }

        self.activities = try allocator.alloc(f64, formula.num_vars);
        @memset(self.activities, 0);
        errdefer allocator.free(self.activities);

        self.analyze_seen = try allocator.alloc(bool, formula.num_vars);
        @memset(self.analyze_seen, false);
        errdefer allocator.free(self.analyze_seen);

        // Stacks used by recursive clause minimization in analyze. A var
        // can be pushed at most once per analyze, so num_vars is a safe
        // upper bound. Reserving up front lets litRedundant use
        // appendAssumeCapacity and stay non-throwing in the hot loop.
        try self.analyze_stack.ensureTotalCapacity(allocator, formula.num_vars);
        errdefer self.analyze_stack.deinit(allocator);
        try self.analyze_to_clear.ensureTotalCapacity(allocator, formula.num_vars);
        errdefer self.analyze_to_clear.deinit(allocator);
        // computeLbd's distinct levels each begin with a distinct decision var.
        try self.analyze_levels.ensureTotalCapacity(allocator, formula.num_vars);
        errdefer self.analyze_levels.deinit(allocator);

        self.order_heap = try OrderHeap.init(allocator, formula.num_vars, self.activities);
        errdefer self.order_heap.deinit(allocator);
        {
            var v: u32 = 0;
            while (v < formula.num_vars) : (v += 1) {
                self.order_heap.insert(v);
            }
        }

        // Reserve the arena and every watch list at its exact final size.
        // Binaries live in bin_watchers, not in the arena.
        var total_slots: usize = 0;
        const WatchCounts = struct { long: u32 = 0, binary: u32 = 0 };
        const watch_counts = try allocator.alloc(WatchCounts, @as(usize, formula.num_vars) * 2);
        defer allocator.free(watch_counts);
        @memset(watch_counts, .{});
        for (0..formula.clauseCount()) |i| {
            const lits = formula.clause(i);
            if (lits.len == 2) {
                watch_counts[lits[0].negate().raw].binary += 1;
                watch_counts[lits[1].negate().raw].binary += 1;
            } else if (lits.len >= 3) {
                total_slots += lits.len + header_slots;
                watch_counts[lits[0].negate().raw].long += 1;
                watch_counts[lits[1].negate().raw].long += 1;
            }
        }
        try self.arena.ensureTotalCapacityPrecise(allocator, total_slots);
        errdefer self.arena.deinit(allocator);
        for (self.watchers, self.bin_watchers, watch_counts) |*w, *bw, counts| {
            try w.ensureTotalCapacityPrecise(allocator, counts.long);
            try bw.ensureTotalCapacityPrecise(allocator, counts.binary);
        }

        for (0..formula.clauseCount()) |i| {
            if (try self.installClause(formula.clause(i), .irredundant, 0) == .refuted) {
                self.unsat_at_init = true;
                break;
            }
        }

        return self;
    }

    pub fn deinit(self: *Solver) void {
        self.arena.deinit(self.allocator);
        for (self.watchers) |*w| w.deinit(self.allocator);
        self.allocator.free(self.watchers);
        for (self.bin_watchers) |*w| w.deinit(self.allocator);
        self.allocator.free(self.bin_watchers);
        self.allocator.free(self.activities);
        self.allocator.free(self.analyze_seen);
        self.analyze_learned.deinit(self.allocator);
        self.analyze_levels.deinit(self.allocator);
        self.analyze_to_clear.deinit(self.allocator);
        self.analyze_stack.deinit(self.allocator);
        self.learned_clauses.deinit(self.allocator);
        self.order_heap.deinit(self.allocator);
        self.eliminated.deinit();
        self.bve_witness_lits.deinit(self.allocator);
        self.bve_witness_frames.deinit(self.allocator);
        self.equiv_witness.deinit(self.allocator);
        self.assignment.deinit();
        self.* = undefined;
    }

    pub fn setProofWriter(self: *Solver, w: *std.Io.Writer) void {
        self.proof = io.drat.Writer.wrap(w);
    }

    pub inline fn clauseLen(self: *const Solver, cref: ClauseRef) u32 {
        return self.arena.items[cref].raw & len_mask;
    }

    pub inline fn clauseIsLearned(self: *const Solver, cref: ClauseRef) bool {
        return (self.arena.items[cref].raw & learned_bit) != 0;
    }

    pub inline fn clauseKind(self: *const Solver, cref: ClauseRef) ClauseKind {
        return if (self.clauseIsLearned(cref)) .learned else .irredundant;
    }

    pub inline fn clauseIsDeleted(self: *const Solver, cref: ClauseRef) bool {
        return (self.arena.items[cref].raw & deleted_bit) != 0;
    }

    pub inline fn clauseLbd(self: *const Solver, cref: ClauseRef) u32 {
        return self.arena.items[cref + 1].raw;
    }

    pub inline fn clauseLits(self: *Solver, cref: ClauseRef) []Literal {
        const len = self.clauseLen(cref);
        const start: usize = @as(usize, cref) + header_slots;
        return self.arena.items[start .. start + len];
    }

    // An active variable is neither assigned nor eliminated, so at level 0
    // it is one the formula still constrains.
    pub fn varIsActive(self: *const Solver, v: u32) bool {
        return self.assignment.vars[v].value == .unassigned and !self.eliminated.isSet(v);
    }

    // A locked clause is the reason for a level-0 assignment, so deleting
    // or rewriting it would break the reason chain analyze follows.
    pub fn clauseIsLocked(self: *Solver, cref: ClauseRef) bool {
        for (self.clauseLits(cref)) |lit| {
            const vi = self.assignment.vars[lit.variable()];
            if (vi.level == 0 and !vi.reason.isNone() and
                !vi.reason.isBinary() and vi.reason.clauseRef() == cref)
            {
                return true;
            }
        }
        return false;
    }

    // A learned clause that subsumes an irredundant one takes over its
    // role in the formula, so it must no longer be eligible for reduceDB.
    pub fn promoteToIrredundant(self: *Solver, cref: ClauseRef) void {
        self.arena.items[cref].raw &= ~learned_bit;
    }

    pub fn markDeleted(self: *Solver, cref: ClauseRef) void {
        std.debug.assert(!self.clauseIsDeleted(cref));
        self.arena_dead_slots += header_slots + self.clauseLen(cref);
        self.arena.items[cref].raw |= deleted_bit;
    }

    // Drops watchers and learned-list entries whose clause was marked
    // deleted, so nothing dereferences a tombstoned arena slot, and drops
    // learned-list entries that subsumption promoted to irredundant.
    pub fn dropDeletedClauseRefs(self: *Solver) void {
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
            if (!self.clauseIsDeleted(cref) and self.clauseIsLearned(cref)) {
                self.learned_clauses.items[j] = cref;
                j += 1;
            }
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }

    pub fn arenaIsMostlyHoles(self: *const Solver) bool {
        return self.arena_dead_slots * 2 > self.arena.items.len;
    }

    pub fn addClauseToArena(
        self: *Solver,
        lits: []const Literal,
        kind: ClauseKind,
        lbd: u32,
    ) !ClauseRef {
        if (self.arena.items.len + header_slots + lits.len > clause_mod.max_arena_slots) {
            return error.ClauseArenaFull;
        }
        const ref: ClauseRef = @intCast(self.arena.items.len);
        const header_raw: u32 = @as(u32, @intCast(lits.len)) |
            (if (kind == .learned) learned_bit else 0);
        try self.arena.append(self.allocator, .{ .raw = header_raw });
        try self.arena.append(self.allocator, .{ .raw = lbd });
        try self.arena.appendSlice(self.allocator, lits);
        return ref;
    }

    pub fn attachWatches(self: *Solver, cref: ClauseRef) !void {
        const lits = self.clauseLits(cref);
        std.debug.assert(lits.len >= 3);
        const w0 = &self.watchers[lits[0].negate().raw];
        const w1 = &self.watchers[lits[1].negate().raw];
        try clause_mod.reserveSlot(Watcher, w0, self.allocator);
        try clause_mod.reserveSlot(Watcher, w1, self.allocator);
        w0.appendAssumeCapacity(.{ .clause = cref, .blocker = lits[1] });
        w1.appendAssumeCapacity(.{ .clause = cref, .blocker = lits[0] });
    }

    // Installs the 2-clause (a ∨ b) into both binary watch lists.
    pub fn addBinary(self: *Solver, a: Literal, b: Literal) !void {
        const w0 = &self.bin_watchers[a.negate().raw];
        const w1 = &self.bin_watchers[b.negate().raw];
        try clause_mod.reserveSlot(BinaryWatch, w0, self.allocator);
        try clause_mod.reserveSlot(BinaryWatch, w1, self.allocator);
        w0.appendAssumeCapacity(.{ .other = b });
        w1.appendAssumeCapacity(.{ .other = a });
    }

    // Installs a clause that holds at level 0: an empty clause refutes the
    // formula, a unit is assigned, a binary joins the binary watch lists
    // and a longer clause the arena. `lbd` only matters for the last.
    pub fn installClause(self: *Solver, lits: []const Literal, kind: ClauseKind, lbd: u32) !Installed {
        switch (lits.len) {
            0 => return .refuted,
            1 => return switch (try self.assertRootUnit(lits[0])) {
                .refuted => .refuted,
                .consistent => .unit,
            },
            2 => {
                try self.addBinary(lits[0], lits[1]);
                return .binary;
            },
            else => {
                const cref = try self.addClauseToArena(lits, kind, lbd);
                try self.attachWatches(cref);
                if (kind == .learned) try self.learned_clauses.append(self.allocator, cref);
                return .{ .long = cref };
            },
        }
    }

    // Assigns `lit` at level 0 unless it already holds.
    pub fn assertRootUnit(self: *Solver, lit: Literal) !RootUnit {
        switch (self.assignment.valueOfLiteral(lit)) {
            .false => return .refuted,
            .unassigned => try self.assignment.assign(lit, Reason.none),
            .true => {},
        }
        return .consistent;
    }

    // Removes one copy of the 2-clause (a ∨ b) from both binary watch lists.
    pub fn removeBinary(self: *Solver, a: Literal, b: Literal) void {
        removeBinaryWatch(&self.bin_watchers[a.negate().raw], b);
        removeBinaryWatch(&self.bin_watchers[b.negate().raw], a);
    }

    pub fn hasBinary(self: *const Solver, a: Literal, b: Literal) bool {
        for (self.bin_watchers[a.negate().raw].items) |w| {
            if (w.other.eql(b)) return true;
        }
        return false;
    }

    pub fn bumpVarActivity(self: *Solver, var_idx: u32) void {
        self.activities[var_idx] += self.var_inc;
        if (self.activities[var_idx] > order_heap_mod.rescale_threshold) {
            for (self.activities) |*a| a.* *= 1.0 / order_heap_mod.rescale_threshold;
            self.var_inc *= 1.0 / order_heap_mod.rescale_threshold;
        }
        self.order_heap.update(var_idx);
    }

    pub fn decayVarActivity(self: *Solver) void {
        self.var_inc *= 1.0 / order_heap_mod.var_decay;
    }

    pub fn pickBranching(self: *Solver) ?Literal {
        while (!self.order_heap.isEmpty()) {
            const v = self.order_heap.popMax();
            // An eliminated variable's value comes from its witness frame;
            // branching on it would analyze clauses that no longer exist.
            if (self.eliminated.isSet(v)) continue;
            if (self.assignment.vars[v].value == .unassigned) {
                const neg = !self.assignment.saved_phases[v];
                return Literal.init(v, neg);
            }
        }
        return null;
    }

    // Rotate saved_phases through the rephase family. Called only at
    // level 0 — the search tree has already been torn down and we're
    // rebiasing the next descent, not perturbing an active trail.
    //
    // best    → copy the deepest-trail snapshot (best_phases) in.
    // original→ reset to the solver default (all-false).
    // inverse → flip every saved phase.
    // random  → deterministic PRNG seeded by conflict count.
    pub fn rephase(self: *Solver) void {
        std.debug.assert(self.assignment.level == 0);
        const saved = self.assignment.saved_phases;
        switch (self.rephase_kind) {
            .best => @memcpy(saved, self.assignment.best_phases),
            .original => @memset(saved, false),
            .inverse => {
                for (saved) |*b| b.* = !b.*;
            },
            .random => {
                var rng = std.Random.DefaultPrng.init(self.stats.conflicts);
                const r = rng.random();
                for (saved) |*b| b.* = r.boolean();
            },
        }
        self.rephase_kind = rephase_mod.next(self.rephase_kind);
        self.stats.rephases += 1;
    }
};

fn removeBinaryWatch(list: *std.ArrayList(BinaryWatch), other: Literal) void {
    for (list.items, 0..) |w, i| {
        if (w.other.eql(other)) {
            _ = list.swapRemove(i);
            return;
        }
    }
}

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

const heuristics = @import("heuristics");
const order_heap_mod = heuristics.order_heap;
const OrderHeap = order_heap_mod.OrderHeap;
const rephase_mod = heuristics.rephase;
const mode_mod = heuristics.mode;
const restart = heuristics.restart;
const Schedule = heuristics.schedule.Schedule;

const reduce_mod = @import("inprocess/reduce.zig");
const probe_mod = @import("inprocess/probe.zig");
const vivify_mod = @import("inprocess/vivify.zig");
const subsume_mod = @import("inprocess/subsume.zig");
const bve_mod = @import("inprocess/bve.zig");
const equiv_mod = @import("inprocess/equiv.zig");

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
// that satisfies all of them in reverse elimination order. The fields
// index clauses of `Solver.bve_witness`:
//   [pos_start .. neg_start)  — clauses containing +pivot
//   [neg_start .. end)        — clauses containing -pivot
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

pub const Schedules = struct {
    reduce: Schedule = reduce_mod.schedule,
    rephase: Schedule = rephase_mod.schedule,
    probe: Schedule = probe_mod.schedule,
    vivify: Schedule = vivify_mod.schedule,
    subsume: Schedule = subsume_mod.schedule,
    bve: Schedule = bve_mod.schedule,
    equiv: Schedule = equiv_mod.schedule,
    mode_switch: Schedule = mode_mod.schedule,
};

pub const Solver = struct {
    allocator: Allocator,
    num_vars: u32,

    // Every long (length >= 3) clause, original or learned.
    arena: clause_mod.ClauseArena,
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

    restarts: restart.RestartState,

    // When each periodic task next runs.
    schedules: Schedules,

    // Rephase state. `best_trail_len` tracks the longest partial
    // assignment seen at a conflict point — each new peak writes its
    // polarities into assignment.best_phases.
    best_trail_len: usize,
    rephase_kind: rephase_mod.RephaseKind,

    // Propagation counts when each budgeted pass last ran.
    props_at_last_probe: u64,
    props_at_last_vivify: u64,
    props_at_last_subsume: u64,

    // BVE — bit-indexed by variable. Eliminated variables must never be
    // branched on (pickBranching filters them), must never reappear as a
    // literal in a learned clause, and must have their values filled in
    // during the .sat reconstruction in model.zig.
    eliminated: std.DynamicBitSet,
    // The original clauses touching every eliminated variable. Each frame
    // in bve_witness_frames names the pivot and a range of these clauses.
    bve_witness: cnf.ClauseList,
    bve_witness_frames: std.ArrayList(WitnessFrame),
    props_at_last_bve: u64,

    // Equivalent-literal substitution witness.
    equiv_witness: std.ArrayList(EquivFrame),

    // Focused/stable alternation.
    search_mode: mode_mod.SearchMode,

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
    pub const probe = probe_mod.probe;
    pub const vivify = vivify_mod.vivify;
    pub const subsume = subsume_mod.subsume;
    pub const preprocessSubsume = subsume_mod.preprocessSubsume;
    pub const subsumeWithin = subsume_mod.subsumeWithin;
    pub const bve = bve_mod.bve;
    pub const preprocessBVE = bve_mod.preprocessBVE;
    pub const equiv = equiv_mod.equiv;
    pub const reduceDB = reduce_mod.reduceDB;
    pub const compact = reduce_mod.compact;

    pub fn init(allocator: Allocator, formula: *const Formula) !Solver {
        var self: Solver = .{
            .allocator = allocator,
            .num_vars = formula.num_vars,
            .arena = .{},
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
            .max_learned = @max(formula.clauseCount(), reduce_mod.min_max_learned),
            .proof = .{},
            .restarts = .{},
            .schedules = .{},
            .best_trail_len = 0,
            .rephase_kind = .best,
            .props_at_last_probe = 0,
            .props_at_last_vivify = 0,
            .props_at_last_subsume = 0,
            .eliminated = undefined,
            .bve_witness = .{},
            .bve_witness_frames = .empty,
            .props_at_last_bve = 0,
            .equiv_witness = .empty,
            .search_mode = .focused,
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
        for (0..formula.num_vars) |v| self.order_heap.insert(@intCast(v));

        try self.reserveClauseStorage(formula);
        errdefer self.arena.deinit(allocator);
        try self.loadClauses(formula);
        return self;
    }

    // Reserves the arena and every watch list at its exact final size.
    // Binaries live in bin_watchers, not in the arena.
    fn reserveClauseStorage(self: *Solver, formula: *const Formula) !void {
        const allocator = self.allocator;
        var long_clauses: usize = 0;
        var long_literals: usize = 0;
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
                long_clauses += 1;
                long_literals += lits.len;
                watch_counts[lits[0].negate().raw].long += 1;
                watch_counts[lits[1].negate().raw].long += 1;
            }
        }
        try self.arena.reserve(allocator, long_clauses, long_literals);
        errdefer self.arena.deinit(allocator);
        for (self.watchers, self.bin_watchers, watch_counts) |*w, *bw, counts| {
            try w.ensureTotalCapacityPrecise(allocator, counts.long);
            try bw.ensureTotalCapacityPrecise(allocator, counts.binary);
        }
    }

    fn loadClauses(self: *Solver, formula: *const Formula) !void {
        for (0..formula.clauseCount()) |i| {
            if (try self.installClause(formula.clause(i), .irredundant, 0) == .refuted) {
                self.unsat_at_init = true;
                return;
            }
        }
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
        self.bve_witness.deinit(self.allocator);
        self.bve_witness_frames.deinit(self.allocator);
        self.equiv_witness.deinit(self.allocator);
        self.assignment.deinit();
        self.* = undefined;
    }

    pub fn setProofWriter(self: *Solver, w: *std.Io.Writer) void {
        self.proof = io.drat.Writer.wrap(w);
    }

    // An active variable is neither assigned nor eliminated, so at level 0
    // it is one the formula still constrains.
    pub fn varIsActive(self: *const Solver, v: u32) bool {
        return self.assignment.vars[v].value == .unassigned and !self.eliminated.isSet(v);
    }

    // A locked clause is the reason for a level-0 assignment, so deleting
    // or rewriting it would break the reason chain analyze follows.
    pub fn clauseIsLocked(self: *Solver, cref: ClauseRef) bool {
        for (self.arena.literals(cref)) |lit| {
            const vi = self.assignment.vars[lit.variable()];
            if (vi.level != 0) continue;
            switch (vi.reason.decode()) {
                .clause => |reason| if (reason == cref) return true,
                .decision, .binary => {},
            }
        }
        return false;
    }

    // Drops watchers and learned-list entries whose clause was marked
    // deleted, so nothing dereferences a tombstoned arena slot, and drops
    // learned-list entries that subsumption promoted to irredundant.
    pub fn dropDeletedClauseRefs(self: *Solver) void {
        for (self.watchers) |*wlist| {
            var j: usize = 0;
            for (wlist.items) |w| {
                if (!self.arena.isDeleted(w.clause)) {
                    wlist.items[j] = w;
                    j += 1;
                }
            }
            wlist.shrinkRetainingCapacity(j);
        }

        var j: usize = 0;
        for (self.learned_clauses.items) |cref| {
            if (!self.arena.isDeleted(cref) and self.arena.isLearned(cref)) {
                self.learned_clauses.items[j] = cref;
                j += 1;
            }
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }

    pub fn binaryClauses(self: *const Solver) BinaryClauses {
        return .{ .solver = self };
    }

    pub fn attachWatches(self: *Solver, cref: ClauseRef) !void {
        const lits = self.arena.literals(cref);
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
                const cref = try self.arena.add(self.allocator, lits, kind, lbd);
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

    // Applies the next `RephaseKind` to saved_phases. Only at level 0, so
    // it biases the next descent rather than an active trail.
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

// Each binary clause once, as `{a, b}` with `a.raw < b.raw`, although the
// watch lists hold it twice.
pub const BinaryClauses = struct {
    solver: *const Solver,
    watched: usize = 0,
    entry: usize = 0,

    pub fn next(self: *BinaryClauses) ?[2]Literal {
        const lists = self.solver.bin_watchers;
        while (self.watched < lists.len) : ({
            self.watched += 1;
            self.entry = 0;
        }) {
            const a = Literal.fromIndex(self.watched).negate();
            const entries = lists[self.watched].items;
            while (self.entry < entries.len) {
                const b = entries[self.entry].other;
                self.entry += 1;
                if (a.raw < b.raw) return .{ a, b };
            }
        }
        return null;
    }
};

const std = @import("std");
const core = @import("core");
const Reason = core.assignment.Reason;
const Level = core.assignment.Level;
const Conflict = core.clause.Conflict;

const backtrack_mod = @import("backtrack.zig");
const state = @import("state.zig");
const Solver = state.Solver;
const solver_mod = @import("solver.zig");
const Result = solver_mod.Result;

const reduce_mod = @import("inprocess/reduce.zig");

pub fn solve(self: *Solver) !Result {
    if (self.unsat_at_init) {
        try self.proof.empty();
        return .unsat;
    }
    if (try self.propagateAtRoot()) |r| return r;
    if (try preprocess(self)) |r| return r;

    while (true) {
        if (solver_mod.interruptRequested()) return .unknown;
        if (try self.propagate()) |conflict| {
            if (try handleConflict(self, conflict)) |r| return r;
        } else {
            const lit = self.pickBranching() orelse return .sat;
            self.stats.decisions += 1;
            try self.assignment.pushDecisionLevel();
            try self.assignment.assign(lit, Reason.none);
        }
    }
}

fn preprocess(self: *Solver) !?Result {
    const passes = .{ Solver.preprocessSubsume, Solver.equiv, Solver.preprocessSubsume, Solver.preprocessBVE };
    inline for (passes) |pass| {
        if (try pass(self)) |r| return r;
        if (solver_mod.interruptRequested()) return .unknown;
    }
    if (self.arena.isMostlyHoles()) try self.compact();
    return null;
}

// Learns a clause from `conflict`, backjumps, asserts the clause's UIP
// and runs whatever restart or maintenance is due.
fn handleConflict(self: *Solver, conflict: Conflict) !?Result {
    self.stats.conflicts += 1;
    self.restarts.conflicts_since_restart += 1;
    const conflict_level = conflictLevel(self, conflict);
    if (conflict_level == .root) {
        try self.proof.empty();
        return .unsat;
    }

    const backjump_level = try self.analyze(conflict, conflict_level);
    // Backtracking resets the levels the LBD counts, so take it first.
    const lbd = learnedLbd(self);
    const conflict_trail_len: f64 = @floatFromInt(self.assignment.trail.items.len);
    saveBestPhases(self);
    self.backtrack(backtrackTarget(self, conflict_level, backjump_level));
    self.restarts.recordLbd(@floatFromInt(lbd));
    try learnClause(self, lbd, backjump_level);
    self.decayVarActivity();

    const should_restart = self.search_mode == .focused and self.restarts.isDue(conflict_trail_len);
    self.restarts.trail_fast.update(conflict_trail_len);
    return runDueTasks(self, dueTasks(self, should_restart));
}

// The highest level among the conflict's literals, which are all false.
fn conflictLevel(self: *Solver, conflict: Conflict) Level {
    const vars = self.assignment.vars;
    return switch (conflict) {
        .clause => |cref| blk: {
            var highest: Level = .root;
            for (self.arena.literals(cref)) |lit| highest = .max(highest, vars[lit.variable()].level);
            break :blk highest;
        },
        .binary => |two| .max(vars[two[0].variable()].level, vars[two[1].variable()].level),
    };
}

fn learnedLbd(self: *Solver) u32 {
    const learned = self.analyze_learned.items;
    return if (learned.len == 1) 1 else self.computeLbd(learned);
}

// Snapshots the polarities of the longest trail seen at a conflict, which
// rephasing and stable mode return to.
fn saveBestPhases(self: *Solver) void {
    const trail = self.assignment.trail.items;
    if (trail.len <= self.best_trail_len) return;
    for (trail) |lit| {
        const v = lit.variable();
        self.assignment.best_phases[v] = (self.assignment.vars[v].value == .true);
    }
    self.best_trail_len = trail.len;
}

// A backjump past `chrono_level_gap` levels pops only the conflict level.
fn backtrackTarget(self: *Solver, conflict_level: Level, backjump_level: Level) Level {
    if (conflict_level.int() <= backjump_level.int() + backtrack_mod.chrono_level_gap) return backjump_level;
    self.stats.chrono_backtracks += 1;
    return conflict_level.prev();
}

// Logs and installs the learned clause and asserts its UIP, which a unit
// clause asserts at level 0.
fn learnClause(self: *Solver, lbd: u32, backjump_level: Level) !void {
    const learned = self.analyze_learned.items;
    try self.proof.addClause(learned);
    switch (learned.len) {
        1 => try self.assignment.assignAtLevel(learned[0], Reason.none, .root),
        2 => {
            try self.addBinary(learned[0], learned[1]);
            try self.assignment.assignAtLevel(learned[0], Reason.fromBinary(learned[1]), backjump_level);
            self.stats.learned_clauses += 1;
        },
        else => {
            const cref = try self.arena.add(self.allocator, learned, .learned, lbd);
            try self.learned_clauses.append(self.allocator, cref);
            try self.attachWatches(cref);
            try self.assignment.assignAtLevel(learned[0], Reason.fromClause(cref), backjump_level);
            self.stats.learned_clauses += 1;
        },
    }
}

// The tasks due after one conflict, all decided before any of them runs.
const DueTasks = struct {
    restart: bool,
    reduce: bool,
    rephase: bool,
    probe: bool,
    vivify: bool,
    subsume: bool,
    bve: bool,
    equiv: bool,
    mode_switch: bool,

    fn any(self: DueTasks) bool {
        inline for (comptime std.meta.fieldNames(DueTasks)) |name| {
            if (@field(self, name)) return true;
        }
        return false;
    }
};

fn dueTasks(self: *const Solver, should_restart: bool) DueTasks {
    const conflicts = self.stats.conflicts;
    const schedules = &self.schedules;
    return .{
        .restart = should_restart,
        .reduce = schedules.reduce.isDue(conflicts) and self.learned_clauses.items.len > self.max_learned,
        .rephase = schedules.rephase.isDue(conflicts),
        .probe = schedules.probe.isDue(conflicts),
        .vivify = schedules.vivify.isDue(conflicts),
        .subsume = schedules.subsume.isDue(conflicts),
        .bve = schedules.bve.isDue(conflicts),
        .equiv = schedules.equiv.isDue(conflicts),
        .mode_switch = schedules.mode_switch.isDue(conflicts),
    };
}

// Every task runs at level 0, so any due task also restarts the search.
fn runDueTasks(self: *Solver, due: DueTasks) !?Result {
    if (!due.any()) return null;
    if (due.restart) {
        self.stats.restarts += 1;
        self.restarts.conflicts_since_restart = 0;
    }
    self.backtrack(.root);

    const schedules = &self.schedules;
    if (due.reduce) {
        try self.reduceDB();
        self.max_learned = (self.max_learned * reduce_mod.max_learned_grow_num) / reduce_mod.max_learned_grow_den;
        schedules.reduce.advance(self.stats.conflicts);
    }
    if (due.rephase) {
        self.rephase();
        schedules.rephase.advance(self.stats.conflicts);
    }
    if (due.probe) {
        if (try self.probe()) |r| return r;
        schedules.probe.advance(self.stats.conflicts);
    }
    if (due.vivify) {
        if (try self.vivify()) |r| return r;
        schedules.vivify.advance(self.stats.conflicts);
    }
    if (due.subsume) {
        if (try self.subsume()) |r| return r;
        schedules.subsume.advance(self.stats.conflicts);
    }
    if (due.bve) {
        if (try self.bve()) |r| return r;
        schedules.bve.advance(self.stats.conflicts);
    }
    if (due.equiv) {
        if (try self.equiv()) |r| return r;
        schedules.equiv.advance(self.stats.conflicts);
    }
    if (due.mode_switch) switchSearchMode(self);
    if (self.arena.isMostlyHoles()) try self.compact();
    return null;
}

// Stable mode starts from the best trail's polarities.
fn switchSearchMode(self: *Solver) void {
    self.search_mode = switch (self.search_mode) {
        .focused => .stable,
        .stable => .focused,
    };
    if (self.search_mode == .stable) @memcpy(self.assignment.saved_phases, self.assignment.best_phases);
    self.schedules.mode_switch.advance(self.stats.conflicts);
    self.stats.mode_switches += 1;
}

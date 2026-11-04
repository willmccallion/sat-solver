const core = @import("core");
const Reason = core.assignment.Reason;

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

    const preprocess_passes = .{ Solver.preprocessSubsume, Solver.equiv, Solver.preprocessSubsume, Solver.preprocessBVE };
    inline for (preprocess_passes) |pass| {
        if (try pass(self)) |r| return r;
        if (solver_mod.interruptRequested()) return .unknown;
    }
    if (self.arenaIsMostlyHoles()) try self.compact();

    while (true) {
        if (solver_mod.interruptRequested()) return .unknown;

        if (try self.propagate()) |conflict| {
            self.stats.conflicts += 1;
            self.restarts.conflicts_since_restart += 1;

            const conflict_level: u32 = switch (conflict) {
                .clause => |cref| blk: {
                    var m: u32 = 0;
                    for (self.clauseLits(cref)) |lit| {
                        const lv = self.assignment.vars[lit.variable()].level;
                        if (lv > m) m = lv;
                    }
                    break :blk m;
                },
                .binary => |two| @max(
                    self.assignment.vars[two[0].variable()].level,
                    self.assignment.vars[two[1].variable()].level,
                ),
            };
            if (conflict_level == 0) {
                try self.proof.empty();
                return .unsat;
            }

            const backjump_level = try self.analyze(conflict, conflict_level);
            // Backtracking resets the levels the LBD counts, so take it first.
            const learned_len = self.analyze_learned.items.len;
            const lbd: u32 = if (learned_len == 1)
                1
            else
                self.computeLbd(self.analyze_learned.items);

            const conflict_trail_len = self.assignment.trail.items.len;
            const conflict_trail_f: f64 = @floatFromInt(conflict_trail_len);

            if (conflict_trail_len > self.best_trail_len) {
                for (self.assignment.trail.items) |tl| {
                    const v = tl.variable();
                    self.assignment.best_phases[v] =
                        (self.assignment.vars[v].value == .true);
                }
                self.best_trail_len = conflict_trail_len;
            }

            const chrono = conflict_level > backjump_level + backtrack_mod.chrono_level_gap;
            const target_level: u32 = if (chrono)
                conflict_level - 1
            else
                backjump_level;
            if (chrono) self.stats.chrono_backtracks += 1;
            self.backtrack(target_level);

            self.restarts.recordLbd(@floatFromInt(lbd));

            if (learned_len == 1) {
                try self.proof.addClause(self.analyze_learned.items);
                try self.assignment.assignAtLevel(
                    self.analyze_learned.items[0],
                    Reason.none,
                    0,
                );
            } else if (learned_len == 2) {
                try self.proof.addClause(self.analyze_learned.items);
                const uip = self.analyze_learned.items[0];
                const other = self.analyze_learned.items[1];
                try self.addBinary(uip, other);
                try self.assignment.assignAtLevel(
                    uip,
                    Reason.fromBinary(other),
                    backjump_level,
                );
                self.stats.learned_clauses += 1;
            } else {
                try self.proof.addClause(self.analyze_learned.items);
                const cref = try self.addClauseToArena(
                    self.analyze_learned.items,
                    .learned,
                    lbd,
                );
                try self.learned_clauses.append(self.allocator, cref);
                try self.attachWatches(cref);
                try self.assignment.assignAtLevel(
                    self.analyze_learned.items[0],
                    Reason.fromClause(cref),
                    backjump_level,
                );
                self.stats.learned_clauses += 1;
            }

            self.decayVarActivity();

            const should_restart = self.search_mode == .focused and self.restarts.isDue(conflict_trail_f);
            self.restarts.trail_fast.update(conflict_trail_f);

            const conflicts = self.stats.conflicts;
            const schedules = &self.schedules;
            const should_reduce = schedules.reduce.isDue(conflicts) and
                self.learned_clauses.items.len > self.max_learned;
            const should_rephase = schedules.rephase.isDue(conflicts);
            const should_probe = schedules.probe.isDue(conflicts);
            const should_vivify = schedules.vivify.isDue(conflicts);
            const should_subsume = schedules.subsume.isDue(conflicts);
            const should_bve = schedules.bve.isDue(conflicts);
            const should_equiv = schedules.equiv.isDue(conflicts);
            const should_flip_mode = schedules.mode_switch.isDue(conflicts);

            if (should_restart or should_reduce or should_rephase or
                should_probe or should_vivify or should_subsume or
                should_bve or should_equiv or should_flip_mode)
            {
                if (should_restart) {
                    self.stats.restarts += 1;
                    self.restarts.conflicts_since_restart = 0;
                }
                self.backtrack(0);
                if (should_reduce) {
                    try self.reduceDB();
                    self.max_learned = (self.max_learned * reduce_mod.max_learned_grow_num) / reduce_mod.max_learned_grow_den;
                    schedules.reduce.advance(self.stats.conflicts);
                }
                if (should_rephase) {
                    self.rephase();
                    schedules.rephase.advance(self.stats.conflicts);
                }
                if (should_probe) {
                    if (try self.probe()) |r| return r;
                    schedules.probe.advance(self.stats.conflicts);
                }
                if (should_vivify) {
                    if (try self.vivify()) |r| return r;
                    schedules.vivify.advance(self.stats.conflicts);
                }
                if (should_subsume) {
                    if (try self.subsume()) |r| return r;
                    schedules.subsume.advance(self.stats.conflicts);
                }
                if (should_bve) {
                    if (try self.bve()) |r| return r;
                    schedules.bve.advance(self.stats.conflicts);
                }
                if (should_equiv) {
                    if (try self.equiv()) |r| return r;
                    schedules.equiv.advance(self.stats.conflicts);
                }
                if (should_flip_mode) {
                    self.search_mode = switch (self.search_mode) {
                        .focused => .stable,
                        .stable => .focused,
                    };
                    if (self.search_mode == .stable) {
                        @memcpy(
                            self.assignment.saved_phases,
                            self.assignment.best_phases,
                        );
                    }
                    schedules.mode_switch.advance(self.stats.conflicts);
                    self.stats.mode_switches += 1;
                }
                if (self.arenaIsMostlyHoles()) try self.compact();
            }
        } else {
            const lit = self.pickBranching() orelse return .sat;
            self.stats.decisions += 1;
            try self.assignment.pushDecisionLevel();
            try self.assignment.assign(lit, Reason.none);
        }
    }
}

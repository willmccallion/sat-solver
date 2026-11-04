const core = @import("core");
const Reason = core.assignment.Reason;

const heuristics = @import("heuristics");
const restart = heuristics.restart;
const rephase_mod = heuristics.rephase;
const mode_mod = heuristics.mode;

const state = @import("state.zig");
const Solver = state.Solver;
const solver_mod = @import("solver.zig");
const Result = solver_mod.Result;

const probe_mod = @import("inprocess/probe.zig");
const vivify_mod = @import("inprocess/vivify.zig");
const subsume_mod = @import("inprocess/subsume.zig");
const bve_mod = @import("inprocess/bve.zig");
const equiv_mod = @import("inprocess/equiv.zig");

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
            self.conflicts_since_restart += 1;

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

            const chrono = conflict_level > backjump_level + mode_mod.chrono_level_gap;
            const target_level: u32 = if (chrono)
                conflict_level - 1
            else
                backjump_level;
            if (chrono) self.stats.chrono_backtracks += 1;
            self.backtrack(target_level);

            const lbd_f: f64 = @floatFromInt(lbd);

            self.lbd_fast += restart.lbd_fast_alpha * (lbd_f - self.lbd_fast);
            self.lbd_fast_bc += restart.lbd_fast_alpha * (1 - self.lbd_fast_bc);
            self.lbd_slow += restart.lbd_slow_alpha * (lbd_f - self.lbd_slow);
            self.lbd_slow_bc += restart.lbd_slow_alpha * (1 - self.lbd_slow_bc);

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

            const ready = self.conflicts_since_restart >= restart.restart_min_conflicts;
            var should_restart = false;
            if (self.search_mode == .focused and
                ready and self.lbd_fast_bc > 0 and self.lbd_slow_bc > 0)
            {
                const fast_corrected = self.lbd_fast / self.lbd_fast_bc;
                const slow_corrected = self.lbd_slow / self.lbd_slow_bc;
                const trending_bad = fast_corrected > slow_corrected * restart.restart_ratio;

                var trail_blocks = false;
                if (self.trail_fast_bc > 0) {
                    const trail_corrected = self.trail_fast / self.trail_fast_bc;
                    trail_blocks = conflict_trail_f > trail_corrected * restart.trail_block_ratio;
                }
                should_restart = trending_bad and !trail_blocks;
            }

            self.trail_fast += restart.lbd_fast_alpha * (conflict_trail_f - self.trail_fast);
            self.trail_fast_bc += restart.lbd_fast_alpha * (1 - self.trail_fast_bc);

            const should_reduce = self.stats.conflicts >= self.next_reduce and
                self.learned_clauses.items.len > self.max_learned;
            const should_rephase = self.stats.conflicts >= self.rephase_next;
            const should_probe = self.stats.conflicts >= self.next_probe;
            const should_vivify = self.stats.conflicts >= self.next_vivify;
            const should_subsume = self.stats.conflicts >= self.next_subsume;
            const should_bve = self.stats.conflicts >= self.next_bve;
            const should_equiv = self.stats.conflicts >= self.next_equiv;
            const should_flip_mode = self.stats.conflicts >= self.next_mode_switch;

            if (should_restart or should_reduce or should_rephase or
                should_probe or should_vivify or should_subsume or
                should_bve or should_equiv or should_flip_mode)
            {
                if (should_restart) {
                    self.stats.restarts += 1;
                    self.conflicts_since_restart = 0;
                }
                self.backtrack(0);
                if (should_reduce) {
                    try self.reduceDB();
                    self.max_learned = (self.max_learned * 11) / 10;
                    self.reduce_interval += restart.reduce_grow;
                    self.next_reduce = self.stats.conflicts + self.reduce_interval;
                }
                if (should_rephase) {
                    self.rephase();
                    self.rephase_interval =
                        (self.rephase_interval * rephase_mod.rephase_grow_num) / rephase_mod.rephase_grow_den;
                    self.rephase_next = self.stats.conflicts + self.rephase_interval;
                }
                if (should_probe) {
                    if (try self.probe()) |r| return r;
                    self.probe_interval =
                        (self.probe_interval * probe_mod.grow_num) / probe_mod.grow_den;
                    self.next_probe = self.stats.conflicts + self.probe_interval;
                }
                if (should_vivify) {
                    if (try self.vivify()) |r| return r;
                    self.vivify_interval =
                        (self.vivify_interval * vivify_mod.grow_num) / vivify_mod.grow_den;
                    self.next_vivify = self.stats.conflicts + self.vivify_interval;
                }
                if (should_subsume) {
                    if (try self.subsume()) |r| return r;
                    self.subsume_interval =
                        (self.subsume_interval * subsume_mod.grow_num) / subsume_mod.grow_den;
                    self.next_subsume = self.stats.conflicts + self.subsume_interval;
                }
                if (should_bve) {
                    if (try self.bve()) |r| return r;
                    self.bve_interval =
                        (self.bve_interval * bve_mod.grow_num) / bve_mod.grow_den;
                    self.next_bve = self.stats.conflicts + self.bve_interval;
                }
                if (should_equiv) {
                    if (try self.equiv()) |r| return r;
                    self.equiv_interval =
                        (self.equiv_interval * equiv_mod.grow_num) / equiv_mod.grow_den;
                    self.next_equiv = self.stats.conflicts + self.equiv_interval;
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
                    self.mode_budget *= 2;
                    self.next_mode_switch = self.stats.conflicts + self.mode_budget;
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

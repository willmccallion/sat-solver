const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const Reason = core.assignment.Reason;

const common = @import("common.zig");
const state = @import("../state.zig");
const Solver = state.Solver;
const solver_mod = @import("../solver.zig");
const Result = solver_mod.Result;

// Failed literal probing (FLP) — cheapest inprocessing technique that
// actually derives new facts. At level 0, for a top-K slice of active
// unassigned variables, try both polarities at a throw-away decision
// level 1 and propagate. A conflict in that probe means the opposite
// polarity is implied by the formula, so we assert it as a root-level
// unit and DRAT-log the addition. Only runs at level 0 and only touches
// the level-1 scratch trail, so it slots cleanly between a restart and
// the next decision without disturbing the search state.
//
// `budget_share` controls how much work each probe call may do
// relative to the propagations accumulated since the last probe; the
// outer interval grows geometrically so inprocessing doesn't dominate
// on long searches.
pub const initial_interval: u64 = 10_000;
pub const grow_num: u64 = 3;
pub const grow_den: u64 = 2;
const budget_share: common.BudgetShare = .{ .num = 1, .den = 10 };
pub const max_vars: usize = 1024;

// Failed literal probing pass. Returns .unsat if the probe (or its
// follow-up propagation) derives an empty clause at level 0, otherwise
// null. Expects self.level == 0, and propagates to a fixed point first,
// since a probe at level 1 would claim any implication still pending.
pub fn probe(self: *Solver) !?Result {
    std.debug.assert(self.assignment.level == 0);
    if (try self.propagateAtRoot()) |r| return r;
    self.stats.probe_passes += 1;

    const props_start = self.stats.propagations;
    const budget = common.propagationBudget(props_start, &self.props_at_last_probe, budget_share);

    var candidates: std.ArrayList(u32) = .empty;
    defer candidates.deinit(self.allocator);
    try candidates.ensureTotalCapacity(self.allocator, self.num_vars);
    for (self.assignment.vars, 0..) |vi, idx| {
        if (vi.value == .unassigned and !self.eliminated.isSet(idx)) {
            candidates.appendAssumeCapacity(@intCast(idx));
        }
    }
    std.mem.sort(u32, candidates.items, self.activities, struct {
        fn lessThan(acts: []f64, a: u32, b: u32) bool {
            return acts[a] > acts[b];
        }
    }.lessThan);

    const k = @min(candidates.items.len, max_vars);

    var probed: usize = 0;
    while (probed < k) : (probed += 1) {
        if (self.stats.propagations - props_start > budget) break;
        if (solver_mod.interruptRequested()) break;

        const v = candidates.items[probed];

        // Try up to two polarities per variable. After the first succeeds
        // or fails, the second is attempted only if v is still unassigned
        // (a cascade from an earlier probe can have fixed it).
        var iter: u32 = 0;
        while (iter < 2) : (iter += 1) {
            if (self.assignment.vars[v].value != .unassigned) break;

            const first_neg = !self.assignment.saved_phases[v];
            const neg = if (iter == 0) first_neg else !first_neg;
            const probe_lit = Literal.init(v, neg);

            try self.assignment.pushDecisionLevel();
            try self.assignment.assign(probe_lit, Reason.none);
            const conflict = try self.propagate();
            self.backtrack(0);

            if (conflict != null) {
                const unit = probe_lit.negate();
                try self.proof.addClause(&.{unit});
                try self.assignment.assign(unit, Reason.none);
                self.stats.failed_literal_units += 1;
                if (try self.propagateAtRoot()) |r| return r;
            }
        }
    }

    return null;
}

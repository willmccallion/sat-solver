const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const Var = core.cnf.Var;
const Reason = core.assignment.Reason;

const Schedule = @import("heuristics").schedule.Schedule;

const common = @import("common.zig");
const solver_mod = @import("../solver.zig");
const Solver = solver_mod.Solver;
const Result = solver_mod.Result;

// Failed literal probing (FLP) — cheapest inprocessing technique that
// actually derives new facts. At level 0, for a top-K slice of active
// unassigned variables, try both polarities at a throw-away decision
// level 1 and propagate. A conflict in that probe means the opposite
// polarity is implied by the formula, so we assert it as a root-level
// unit and DRAT-log the addition. Only runs at level 0 and only touches
// the level-1 scratch trail, so it slots cleanly between a restart and
// the next decision without disturbing the search solver_mod.
//
// `budget_share` controls how much work each probe call may do
// relative to the propagations accumulated since the last probe; the
// outer interval grows geometrically so inprocessing doesn't dominate
// on long searches.
pub const schedule: Schedule = .every(10_000, .by_half);
const budget_share: common.BudgetShare = .{ .num = 1, .den = 10 };
const max_probed_vars: usize = 1024;

// Failed literal probing pass. Returns .unsat if the probe (or its
// follow-up propagation) derives an empty clause at level 0, otherwise
// null. Expects self.level == 0, and propagates to a fixed point first,
// since a probe at level 1 would claim any implication still pending.
pub fn probe(self: *Solver) solver_mod.Error!?Result {
    std.debug.assert(self.assignment.level == .root);
    if (try self.propagateAtRoot()) |r| return r;
    self.stats.probe_passes += 1;

    const props_start = self.stats.propagations;
    const budget = common.propagationBudget(props_start, &self.props_at_last_probe, budget_share);

    var candidates: std.ArrayList(Var) = .empty;
    defer candidates.deinit(self.allocator);
    try candidates.ensureTotalCapacity(self.allocator, self.num_vars);
    for (0..self.num_vars) |idx| {
        const v: Var = .fromIndex(idx);
        if (self.varIsActive(v)) candidates.appendAssumeCapacity(v);
    }
    std.mem.sort(Var, candidates.items, self.activities, struct {
        fn lessThan(acts: []f64, a: Var, b: Var) bool {
            return acts[a.index()] > acts[b.index()];
        }
    }.lessThan);

    const k = @min(candidates.items.len, max_probed_vars);

    var probed: usize = 0;
    while (probed < k) : (probed += 1) {
        if (self.stats.propagations - props_start > budget) break;
        if (self.isInterrupted()) break;

        const v = candidates.items[probed];

        // Both polarities, unless probing the first already fixed v.
        var attempt: u32 = 0;
        while (attempt < 2) : (attempt += 1) {
            if (self.assignment.vars[v.index()].value != .unassigned) break;

            const first_neg = !self.assignment.saved_phases[v.index()];
            const neg = if (attempt == 0) first_neg else !first_neg;
            const probe_lit = Literal.init(v, neg);

            try self.assignment.pushDecisionLevel();
            try self.assignment.assign(probe_lit, Reason.none);
            const conflict = try self.propagate();
            self.backtrack(.root);

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

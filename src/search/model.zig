const core = @import("core");
const Formula = core.cnf.Formula;

const state = @import("state.zig");
const Solver = state.Solver;
const bve = @import("inprocess/bve.zig");
const equiv = @import("inprocess/equiv.zig");

// Assigns every eliminated variable after a .sat result. BVE frames go
// first: equivalence substitution rewrites earlier BVE witnesses onto
// representatives, and a representative may itself be BVE-eliminated
// later, so equivalence copies must read final representative values.
pub fn extendModel(self: *Solver) void {
    bve.reconstructEliminatedVars(self);
    equiv.reconstructEquivVars(self);
}

// Index of the first clause of `formula` the current assignment leaves
// unsatisfied, or null when the assignment is a model of `formula`.
pub fn findFalsifiedClause(self: *const Solver, formula: *const Formula) ?usize {
    for (0..formula.clauseCount()) |i| {
        const satisfied = for (formula.clause(i)) |lit| {
            if (self.assignment.valueOfLiteral(lit) == .@"true") break true;
        } else false;
        if (!satisfied) return i;
    }
    return null;
}

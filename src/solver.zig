const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const Formula = cnf.Formula;
const Assignment = @import("assignment.zig").Assignment;

pub const Result = enum { sat, unsat, unknown };

pub const ConflictClause = []const Literal;

pub const Solver = struct {
    allocator: Allocator,
    formula: Formula,
    assignment: Assignment,

    pub fn init(allocator: Allocator, formula: Formula) !Solver {
        return .{
            .allocator = allocator,
            .formula = formula,
            .assignment = try Assignment.init(allocator, formula.num_vars),
        };
    }

    pub fn deinit(self: *Solver) void {
        self.assignment.deinit();
        self.formula.deinit();
        self.* = undefined;
    }

    // TODO: CDCL main loop. Pseudocode:
    //
    //   while (true) {
    //       if (propagate()) |conflict| {
    //           if (assignment.level == 0) return .unsat;
    //           const learned = analyze(conflict);
    //           const backjump_level = secondHighestLevel(learned);
    //           backtrack(backjump_level);
    //           addLearnedClause(learned);
    //           assert(learned);   // unit under new level
    //       } else {
    //           if (pickBranchingVariable()) |lit| {
    //               assignment.pushDecisionLevel();
    //               try assignment.assign(lit);
    //           } else {
    //               return .sat;
    //           }
    //       }
    //       maybeRestart();
    //   }
    pub fn solve(self: *Solver) Result {
        _ = self;
        return .unknown;
    }

    // TODO: boolean constraint propagation (BCP / unit propagation).
    // Walk newly assigned literals, fire any clauses that become unit,
    // return a conflict clause if one is falsified. Eventually this should
    // use two-watched literals for efficiency.
    pub fn propagate(self: *Solver) ?ConflictClause {
        _ = self;
        return null;
    }

    // TODO: decision heuristic. Start with a trivial pick (first unassigned),
    // eventually replace with VSIDS (variable state independent decaying sum).
    pub fn pickBranchingVariable(self: *Solver) ?Literal {
        _ = self;
        return null;
    }

    // TODO: undo assignments above `level`. Delegates to
    // Assignment.popToLevel, which in turn walks the trail.
    pub fn backtrack(self: *Solver, level: u32) void {
        _ = self;
        _ = level;
    }
};

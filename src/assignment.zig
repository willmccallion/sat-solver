const std = @import("std");
const Allocator = std.mem.Allocator;
const Literal = @import("cnf.zig").Literal;

pub const Value = enum { unassigned, @"true", @"false" };

pub const VarInfo = struct {
    value: Value = .unassigned,
    level: u32 = 0,
};

pub const Assignment = struct {
    allocator: Allocator,
    vars: []VarInfo,
    trail: std.ArrayList(Literal),
    level: u32,

    pub fn init(allocator: Allocator, num_vars: u32) !Assignment {
        const vars = try allocator.alloc(VarInfo, num_vars);
        @memset(vars, .{});
        return .{
            .allocator = allocator,
            .vars = vars,
            .trail = .empty,
            .level = 0,
        };
    }

    pub fn deinit(self: *Assignment) void {
        self.allocator.free(self.vars);
        self.trail.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn valueOfVar(self: *const Assignment, var_index: u32) Value {
        return self.vars[var_index].value;
    }

    pub fn valueOfLiteral(self: *const Assignment, lit: Literal) Value {
        const v = self.vars[lit.variable()].value;
        if (v == .unassigned) return .unassigned;
        if (lit.isNegative()) {
            return if (v == .@"true") .@"false" else .@"true";
        }
        return v;
    }

    pub fn assign(self: *Assignment, lit: Literal) !void {
        const var_index = lit.variable();
        std.debug.assert(self.vars[var_index].value == .unassigned);
        self.vars[var_index] = .{
            .value = if (lit.isNegative()) .@"false" else .@"true",
            .level = self.level,
        };
        try self.trail.append(self.allocator, lit);
    }

    pub fn unassign(self: *Assignment, var_index: u32) void {
        self.vars[var_index] = .{};
    }

    pub fn pushDecisionLevel(self: *Assignment) void {
        self.level += 1;
    }

    pub fn popToLevel(self: *Assignment, target_level: u32) void {
        // TODO: walk the trail backwards, unassigning literals whose level >
        // target_level, truncate the trail, and set self.level = target_level.
        // Needed before backtrack / backjump can work.
        _ = self;
        _ = target_level;
    }
};

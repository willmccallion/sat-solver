const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const ClauseRef = cnf.ClauseRef;
const null_clause = cnf.null_clause;

pub const Value = enum(u8) { unassigned, @"true", @"false" };

pub const VarInfo = struct {
    value: Value = .unassigned,
    level: u32 = 0,
    reason: ClauseRef = null_clause,
};

pub const Assignment = struct {
    allocator: Allocator,
    vars: []VarInfo,
    saved_phases: []bool,
    trail: std.ArrayList(Literal),
    trail_lim: std.ArrayList(u32),
    level: u32,
    propagation_head: usize,

    pub fn init(allocator: Allocator, num_vars: u32) !Assignment {
        const vars = try allocator.alloc(VarInfo, num_vars);
        errdefer allocator.free(vars);
        @memset(vars, .{});

        const saved = try allocator.alloc(bool, num_vars);
        errdefer allocator.free(saved);
        @memset(saved, false);

        return .{
            .allocator = allocator,
            .vars = vars,
            .saved_phases = saved,
            .trail = .empty,
            .trail_lim = .empty,
            .level = 0,
            .propagation_head = 0,
        };
    }

    pub fn deinit(self: *Assignment) void {
        self.allocator.free(self.vars);
        self.allocator.free(self.saved_phases);
        self.trail.deinit(self.allocator);
        self.trail_lim.deinit(self.allocator);
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

    pub fn assign(self: *Assignment, lit: Literal, reason: ClauseRef) !void {
        const var_index = lit.variable();
        std.debug.assert(self.vars[var_index].value == .unassigned);
        self.vars[var_index] = .{
            .value = if (lit.isNegative()) .@"false" else .@"true",
            .level = self.level,
            .reason = reason,
        };
        try self.trail.append(self.allocator, lit);
    }

    pub fn pushDecisionLevel(self: *Assignment) !void {
        try self.trail_lim.append(self.allocator, @intCast(self.trail.items.len));
        self.level += 1;
    }

    pub fn popToLevel(self: *Assignment, target_level: u32) void {
        if (self.level <= target_level) return;
        const trail_start: usize = self.trail_lim.items[target_level];
        var i: usize = self.trail.items.len;
        while (i > trail_start) {
            i -= 1;
            const lit = self.trail.items[i];
            const v = lit.variable();
            self.saved_phases[v] = (self.vars[v].value == .@"true");
            self.vars[v] = .{};
        }
        self.trail.shrinkRetainingCapacity(trail_start);
        self.trail_lim.shrinkRetainingCapacity(target_level);
        self.level = target_level;
        if (self.propagation_head > trail_start) self.propagation_head = trail_start;
    }
};

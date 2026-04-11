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

    // Literal-indexed value table. Length is 2 * num_vars. Lookup is a
    // single `lit_values[lit.raw]` load — no shift, no multiply, no
    // sign test, no if-then-else chain. Every `valueOfLiteral` call in
    // BCP and analyze collapses from an 8-instruction / 3-branch chain
    // down to one load + one compare. This is *the* reason propagate's
    // bad-speculation stall budget dropped.
    //
    // Invariant maintained by `assign` and `popToLevel`:
    //   lit_values[v*2 + 0]  is the truth value of the positive literal  v
    //   lit_values[v*2 + 1]  is the truth value of the negative literal ¬v
    // When v is unassigned, both slots are .unassigned.
    // When v is true:  positive slot is .true,  negative slot is .false.
    // When v is false: positive slot is .false, negative slot is .true.
    lit_values: []Value,

    saved_phases: []bool,
    trail: std.ArrayList(Literal),
    trail_lim: std.ArrayList(u32),
    level: u32,
    propagation_head: usize,

    pub fn init(allocator: Allocator, num_vars: u32) !Assignment {
        const vars = try allocator.alloc(VarInfo, num_vars);
        errdefer allocator.free(vars);
        @memset(vars, .{});

        const lit_values = try allocator.alloc(Value, @as(usize, num_vars) * 2);
        errdefer allocator.free(lit_values);
        @memset(lit_values, .unassigned);

        const saved = try allocator.alloc(bool, num_vars);
        errdefer allocator.free(saved);
        @memset(saved, false);

        return .{
            .allocator = allocator,
            .vars = vars,
            .lit_values = lit_values,
            .saved_phases = saved,
            .trail = .empty,
            .trail_lim = .empty,
            .level = 0,
            .propagation_head = 0,
        };
    }

    pub fn deinit(self: *Assignment) void {
        self.allocator.free(self.vars);
        self.allocator.free(self.lit_values);
        self.allocator.free(self.saved_phases);
        self.trail.deinit(self.allocator);
        self.trail_lim.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn valueOfVar(self: *const Assignment, var_index: u32) Value {
        return self.vars[var_index].value;
    }

    // Hot path: called many times per clause inside propagate. Should
    // compile to a single load + cmp on the caller side after inlining.
    pub inline fn valueOfLiteral(self: *const Assignment, lit: Literal) Value {
        return self.lit_values[lit.raw];
    }

    pub fn assign(self: *Assignment, lit: Literal, reason: ClauseRef) !void {
        const var_index = lit.variable();
        std.debug.assert(self.vars[var_index].value == .unassigned);
        const negative = lit.isNegative();
        self.vars[var_index] = .{
            .value = if (negative) .@"false" else .@"true",
            .level = self.level,
            .reason = reason,
        };
        // Update both literal slots at once. The compiler turns this
        // into two byte stores to adjacent addresses.
        const pos_slot = var_index << 1;
        self.lit_values[pos_slot] = if (negative) .@"false" else .@"true";
        self.lit_values[pos_slot | 1] = if (negative) .@"true" else .@"false";
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
            const pos_slot = v << 1;
            self.lit_values[pos_slot] = .unassigned;
            self.lit_values[pos_slot | 1] = .unassigned;
        }
        self.trail.shrinkRetainingCapacity(trail_start);
        self.trail_lim.shrinkRetainingCapacity(target_level);
        self.level = target_level;
        if (self.propagation_head > trail_start) self.propagation_head = trail_start;
    }
};

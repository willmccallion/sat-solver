const std = @import("std");
const Allocator = std.mem.Allocator;

pub const Literal = struct {
    raw: u32,

    pub fn init(var_index: u32, negated: bool) Literal {
        return .{ .raw = (var_index << 1) | @intFromBool(negated) };
    }

    pub fn variable(self: Literal) u32 {
        return self.raw >> 1;
    }

    pub fn isNegative(self: Literal) bool {
        return (self.raw & 1) == 1;
    }

    pub fn negate(self: Literal) Literal {
        return .{ .raw = self.raw ^ 1 };
    }

    pub fn fromDimacs(x: i32) Literal {
        std.debug.assert(x != 0);
        const magnitude: u32 = @intCast(if (x < 0) -x else x);
        return init(magnitude - 1, x < 0);
    }

    pub fn toDimacs(self: Literal) i32 {
        const v: i32 = @intCast(self.variable() + 1);
        return if (self.isNegative()) -v else v;
    }

    pub fn eql(a: Literal, b: Literal) bool {
        return a.raw == b.raw;
    }
};

pub const Clause = []Literal;

pub const Formula = struct {
    allocator: Allocator,
    num_vars: u32,
    clauses: std.ArrayList(Clause),

    pub fn init(allocator: Allocator) Formula {
        return .{
            .allocator = allocator,
            .num_vars = 0,
            .clauses = .empty,
        };
    }

    pub fn deinit(self: *Formula) void {
        for (self.clauses.items) |clause| {
            self.allocator.free(clause);
        }
        self.clauses.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addClause(self: *Formula, literals: []const Literal) !void {
        const owned = try self.allocator.dupe(Literal, literals);
        errdefer self.allocator.free(owned);
        try self.clauses.append(self.allocator, owned);
    }
};

const std = @import("std");
const Allocator = std.mem.Allocator;

pub const ClauseRef = u32;
pub const null_clause: ClauseRef = std.math.maxInt(u32);

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

    // Orders by raw encoding, so a literal and its negation sort adjacent.
    pub fn lessThan(_: void, a: Literal, b: Literal) bool {
        return a.raw < b.raw;
    }
};

pub const Clause = []Literal;

// Every stored clause is free of duplicate literals and is not a
// tautology. Inprocessing (subsumption, SSR, BVE) relies on both.
pub const Formula = struct {
    allocator: Allocator,
    num_vars: u32,
    clauses: std.ArrayList(Clause),
    sort_scratch: std.ArrayList(Literal),

    pub fn init(allocator: Allocator) Formula {
        return .{
            .allocator = allocator,
            .num_vars = 0,
            .clauses = .empty,
            .sort_scratch = .empty,
        };
    }

    pub fn deinit(self: *Formula) void {
        for (self.clauses.items) |clause| {
            self.allocator.free(clause);
        }
        self.clauses.deinit(self.allocator);
        self.sort_scratch.deinit(self.allocator);
        self.* = undefined;
    }

    // Stores `literals` with duplicates merged. A tautology (x and ¬x both
    // present) is satisfied by every assignment, so it is not stored.
    pub fn addClause(self: *Formula, literals: []const Literal) !void {
        const sorted = &self.sort_scratch;
        try sorted.resize(self.allocator, literals.len);
        @memcpy(sorted.items, literals);
        std.mem.sort(Literal, sorted.items, {}, Literal.lessThan);

        var has_duplicate = false;
        if (sorted.items.len > 1) {
            for (sorted.items[0 .. sorted.items.len - 1], sorted.items[1..]) |a, b| {
                if (a.eql(b)) {
                    has_duplicate = true;
                } else if (a.variable() == b.variable()) {
                    return;
                }
            }
        }

        const kept = if (has_duplicate) dedupeSorted(sorted.items) else literals;
        const owned = try self.allocator.dupe(Literal, kept);
        errdefer self.allocator.free(owned);
        try self.clauses.append(self.allocator, owned);
    }
};

fn dedupeSorted(lits: []Literal) []Literal {
    var kept: usize = 0;
    for (lits) |lit| {
        if (kept > 0 and lits[kept - 1].eql(lit)) continue;
        lits[kept] = lit;
        kept += 1;
    }
    return lits[0..kept];
}

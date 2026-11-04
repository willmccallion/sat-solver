const std = @import("std");
const Allocator = std.mem.Allocator;

pub const ClauseRef = u32;

// Literal.raw is var*2+sign and binary reasons tag it with bit 31, so
// every variable index must stay below 2^30.
pub const max_vars: u32 = 1 << 30;

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

// Clauses are stored back to back in one literal buffer; clause i spans
// literals[clause_ends[i - 1] .. clause_ends[i]]. Every stored clause is
// free of duplicate literals and is not a tautology. Inprocessing
// (subsumption, SSR, BVE) relies on both.
pub const Formula = struct {
    allocator: Allocator,
    num_vars: u32,
    literals: std.ArrayList(Literal),
    clause_ends: std.ArrayList(u32),
    sort_scratch: std.ArrayList(Literal),

    pub const AddClauseError = error{ OutOfMemory, FormulaTooLarge };

    pub fn init(allocator: Allocator, num_vars: u32) Formula {
        return .{
            .allocator = allocator,
            .num_vars = num_vars,
            .literals = .empty,
            .clause_ends = .empty,
            .sort_scratch = .empty,
        };
    }

    pub fn deinit(self: *Formula) void {
        self.literals.deinit(self.allocator);
        self.clause_ends.deinit(self.allocator);
        self.sort_scratch.deinit(self.allocator);
        self.* = undefined;
    }

    // Lowers num_vars to one past the highest variable a clause mentions.
    // A header's count is only a declaration, and the solver sizes every
    // per-variable array from num_vars, so an overstated header would
    // otherwise cost memory for variables that never occur.
    pub fn trimUnusedVars(self: *Formula) void {
        var end: u32 = 0;
        for (self.literals.items) |lit| end = @max(end, lit.variable() + 1);
        self.num_vars = end;
    }

    pub fn clauseCount(self: *const Formula) usize {
        return self.clause_ends.items.len;
    }

    pub fn clause(self: *const Formula, index: usize) []const Literal {
        const start: usize = if (index == 0) 0 else self.clause_ends.items[index - 1];
        return self.literals.items[start..self.clause_ends.items[index]];
    }

    // Stores `literals` with duplicates merged. A tautology (x and ¬x both
    // present) is satisfied by every assignment, so it is not stored.
    pub fn addClause(self: *Formula, literals: []const Literal) AddClauseError!void {
        const sorted = &self.sort_scratch;
        try sorted.resize(self.allocator, literals.len);
        @memcpy(sorted.items, literals);
        const distinct = sortedDistinct(sorted.items) orelse return;
        // The caller's literal order is kept unless duplicates were merged.
        const kept = if (distinct.len < literals.len) distinct else literals;
        const end = std.math.add(usize, self.literals.items.len, kept.len) catch
            return error.FormulaTooLarge;
        if (end > std.math.maxInt(u32)) return error.FormulaTooLarge;
        try self.clause_ends.ensureUnusedCapacity(self.allocator, 1);
        try self.literals.appendSlice(self.allocator, kept);
        self.clause_ends.appendAssumeCapacity(@intCast(end));
    }
};

// Sorts `lits` and merges duplicates in place; null when the clause is a
// tautology (holds some x and ¬x).
pub fn sortedDistinct(lits: []Literal) ?[]Literal {
    std.mem.sort(Literal, lits, {}, Literal.lessThan);
    var kept: usize = 0;
    for (lits) |lit| {
        if (kept > 0) {
            const prev = lits[kept - 1];
            if (prev.eql(lit)) continue;
            if (prev.variable() == lit.variable()) return null;
        }
        lits[kept] = lit;
        kept += 1;
    }
    return lits[0..kept];
}

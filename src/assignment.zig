const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const ClauseRef = cnf.ClauseRef;

pub const Value = enum(u8) { unassigned, @"true", @"false" };

// Why a literal on the trail was assigned.
//
// Three disjoint encodings share a single u32 so VarInfo stays 12 bytes
// (one cache line per four variables):
//
//   none              raw == max_u32            decision — no reason
//   clause(cref)      raw == cref               top bit clear, cref is an arena index
//   binary(other)     raw == binary_bit | L     top bit set, L is the partner literal
//
// Binary reasons inline their partner literal so BCP on 2-literal
// clauses never touches the clause arena: propagation, conflict analysis,
// and minimization reconstruct the 2-lit clause as [forced_lit, binaryOther].
// This is the single biggest reason modern solvers (Kissat, CaDiCaL)
// treat binaries separately — the arena cache miss per watcher is gone.
pub const Reason = struct {
    raw: u32,

    const binary_bit: u32 = 0x8000_0000;
    pub const none = Reason{ .raw = std.math.maxInt(u32) };

    pub fn fromClause(cref: ClauseRef) Reason {
        // The arena header steals bits 30–31 for the learned/deleted flags,
        // so ClauseRef indices are already capped below 2^30 in practice.
        // This assert guards the tagging invariant: `clause` encodings must
        // leave the top bit clear so `isBinary` can discriminate.
        std.debug.assert(cref < binary_bit);
        return .{ .raw = cref };
    }

    pub fn fromBinary(other: Literal) Reason {
        // Literal.raw = var_idx*2+sign ≤ 2*num_vars; fits under 2^31 for
        // any plausible instance.
        std.debug.assert(other.raw < binary_bit);
        return .{ .raw = binary_bit | other.raw };
    }

    pub inline fn isNone(self: Reason) bool {
        return self.raw == none.raw;
    }

    pub inline fn isBinary(self: Reason) bool {
        // `none` has the top bit set too, so filter it out first.
        return self.raw != none.raw and (self.raw & binary_bit) != 0;
    }

    pub inline fn clauseRef(self: Reason) ClauseRef {
        std.debug.assert(!self.isNone() and (self.raw & binary_bit) == 0);
        return self.raw;
    }

    pub inline fn binaryOther(self: Reason) Literal {
        std.debug.assert(self.isBinary());
        return .{ .raw = self.raw & ~binary_bit };
    }
};

pub const VarInfo = struct {
    value: Value = .unassigned,
    level: u32 = 0,
    reason: Reason = Reason.none,
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

    pub fn assign(self: *Assignment, lit: Literal, reason: Reason) !void {
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

const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const Var = core.cnf.Var;
const ClauseList = core.cnf.ClauseList;
const ClauseRef = core.cnf.ClauseRef;
const clause_mod = core.clause;

const Schedule = @import("heuristics").schedule.Schedule;

const common = @import("common.zig");
const state = @import("../state.zig");
const Solver = state.Solver;
const solver_mod = @import("../solver.zig");
const Result = solver_mod.Result;

// Equivalent-literal substitution via binary-implication-graph SCC.
//
// Build a digraph on 2*num_vars literal nodes where `l → other` is an
// edge iff `bin_watchers[l.raw]` holds a `{other}` entry — equivalently,
// the binary clause `(¬l ∨ other)` is in the formula. Run Tarjan's SCC
// iteratively; two literals in the same SCC are provably equivalent. If
// an SCC contains both `l` and `¬l` the formula is unsat. Otherwise pick
// a representative per SCC (min raw) and substitute every non-rep
// occurrence across the arena and bin_watchers.
//
// After substitution a long clause may collapse to a unit, a binary, a
// shorter long, or a tautology; binaries may collapse to a unit or a
// tautology. Duplicates are merged by sort+dedupe before classification.
//
// DRAT ordering: emit ALL add-new clauses first, then ALL delete-old
// clauses. The equivalence-edge binaries that justify each add under
// RUP are still in the formula during every add, so every emitted add
// validates. The delete phase then strips both the originals and the
// tautologized equivalence binaries.
//
// Model reconstruction: each eliminated variable pushes a frame onto
// `equiv_witness`; `reconstructEquivVars` walks the stack in reverse
// and copies each variable's value from the current valueOfLiteral of
// its representative.

pub const schedule: Schedule = .every(10_000, .by_half);

pub fn equiv(self: *Solver) !?Result {
    std.debug.assert(self.assignment.level == .root);
    if (try self.propagateAtRoot()) |r| return r;
    if (self.num_vars == 0) return null;

    const component = try self.allocator.alloc(?u32, @as(usize, self.num_vars) * 2);
    defer self.allocator.free(component);
    const component_count = try findComponents(self, component);
    if (contradictedVariable(component)) |v| {
        // x reaches ¬x, so the unit ¬x is RUP; only after it is the empty
        // clause RUP as well.
        try self.proof.addClause(&.{Literal.init(v, true)});
        try self.proof.empty();
        return .unsat;
    }

    const lit_remap = try representatives(self.allocator, component, component_count);
    defer self.allocator.free(lit_remap);
    if (!substitutesAnyVariable(self, lit_remap)) return null;

    var rewrite: Rewrite = .{ .solver = self, .lit_remap = lit_remap };
    defer rewrite.deinit();
    try rewrite.collect();
    if (rewrite.isEmpty()) return null;

    try recordSubstitutions(self, lit_remap);
    // BVE's witness may name variables substituted here, and BVE
    // reconstruction runs before equiv's, so it must see their representatives.
    for (self.bve_witness.literals.items) |*lit| lit.* = lit_remap[lit.raw];

    try rewrite.logProof();
    if (try rewrite.apply() == .refuted) {
        try self.proof.empty();
        return .unsat;
    }
    if (rewrite.long.items.len > 0) self.dropDeletedClauseRefs();

    if (try self.propagateAtRoot()) |r| return r;
    self.stats.equiv_passes += 1;
    return null;
}

// Labels each literal with its strongly connected component in the binary
// implication graph, where an entry `other` in bin_watchers[l] is the edge
// l → other, and returns how many components there are. Literals of
// inactive variables, whose bin_watchers entries may be stale, stay null.
fn findComponents(solver: *const Solver, component: []?u32) !u32 {
    @memset(component, null);
    var tarjan = try Tarjan.init(solver, component);
    defer tarjan.deinit();
    for (0..component.len) |start| {
        const lit_raw: u32 = @intCast(start);
        if (tarjan.index[lit_raw] == null and tarjan.isActive(lit_raw)) try tarjan.visitFrom(lit_raw);
    }
    return tarjan.component_count;
}

// Iterative Tarjan over literal indices.
const Tarjan = struct {
    solver: *const Solver,
    component: []?u32,
    index: []?u32,
    lowlink: []u32,
    on_stack: []bool,
    stack: std.ArrayList(u32) = .empty,
    // The depth-first path, each node with the next of its edges to follow.
    path: std.ArrayList(PathEntry) = .empty,
    next_index: u32 = 0,
    component_count: u32 = 0,

    const PathEntry = struct { node: u32, next_edge: u32 = 0 };

    fn init(solver: *const Solver, component: []?u32) !Tarjan {
        const allocator = solver.allocator;
        const index = try allocator.alloc(?u32, component.len);
        errdefer allocator.free(index);
        const lowlink = try allocator.alloc(u32, component.len);
        errdefer allocator.free(lowlink);
        const on_stack = try allocator.alloc(bool, component.len);
        @memset(index, null);
        @memset(on_stack, false);
        return .{ .solver = solver, .component = component, .index = index, .lowlink = lowlink, .on_stack = on_stack };
    }

    fn deinit(self: *Tarjan) void {
        const allocator = self.solver.allocator;
        allocator.free(self.index);
        allocator.free(self.lowlink);
        allocator.free(self.on_stack);
        self.stack.deinit(allocator);
        self.path.deinit(allocator);
    }

    fn isActive(self: *const Tarjan, lit_raw: u32) bool {
        return self.solver.varIsActive(Literal.fromIndex(lit_raw).variable());
    }

    fn visitFrom(self: *Tarjan, start: u32) !void {
        try self.enter(start);
        while (self.path.items.len > 0) {
            if (!try self.descend()) self.leave();
        }
    }

    fn enter(self: *Tarjan, node: u32) !void {
        const allocator = self.solver.allocator;
        self.index[node] = self.next_index;
        self.lowlink[node] = self.next_index;
        self.next_index += 1;
        try self.stack.append(allocator, node);
        self.on_stack[node] = true;
        try self.path.append(allocator, .{ .node = node });
    }

    // Enters the path's last node's next unvisited successor, lowering its
    // lowlink for successors still on the stack; false once none is left.
    fn descend(self: *Tarjan) !bool {
        const top = &self.path.items[self.path.items.len - 1];
        const node = top.node;
        const successors = self.solver.bin_watchers[node].items;
        while (top.next_edge < successors.len) {
            const next = successors[top.next_edge].other.raw;
            top.next_edge += 1;
            if (next == node or !self.isActive(next)) continue;
            if (self.index[next]) |next_index| {
                if (self.on_stack[next]) self.lowlink[node] = @min(self.lowlink[node], next_index);
            } else {
                try self.enter(next);
                return true;
            }
        }
        return false;
    }

    // Leaves the path's last node, closing its component if it is the
    // component's root, and passes its lowlink up to its parent.
    fn leave(self: *Tarjan) void {
        const node = self.path.pop().?.node;
        if (self.lowlink[node] == self.index[node].?) {
            while (self.stack.pop()) |member| {
                self.on_stack[member] = false;
                self.component[member] = self.component_count;
                if (member == node) break;
            }
            self.component_count += 1;
        }
        if (self.path.items.len > 0) {
            const parent = self.path.items[self.path.items.len - 1].node;
            self.lowlink[parent] = @min(self.lowlink[parent], self.lowlink[node]);
        }
    }
};

// The first variable whose two literals share a component, which makes
// the formula unsatisfiable.
fn contradictedVariable(component: []const ?u32) ?Var {
    for (0..component.len / 2) |idx| {
        const v: Var = .fromIndex(idx);
        const pos_id = component[Literal.init(v, false).raw] orelse continue;
        const neg_id = component[Literal.init(v, true).raw] orelse continue;
        if (pos_id == neg_id) return v;
    }
    return null;
}

// Maps each literal to the smallest literal of its component, and a
// literal in no component to itself.
fn representatives(allocator: std.mem.Allocator, component: []const ?u32, component_count: u32) ![]Literal {
    const smallest = try allocator.alloc(?Literal, component_count);
    defer allocator.free(smallest);
    @memset(smallest, null);
    const lit_remap = try allocator.alloc(Literal, component.len);
    for (component, 0..) |id_or_null, idx| {
        const lit = Literal.fromIndex(idx);
        const id = id_or_null orelse {
            lit_remap[idx] = lit;
            continue;
        };
        // Literals are visited in increasing order, so the first is smallest.
        if (smallest[id] == null) smallest[id] = lit;
        lit_remap[idx] = smallest[id].?;
    }
    return lit_remap;
}

fn substitutesAnyVariable(solver: *const Solver, lit_remap: []const Literal) bool {
    for (0..solver.num_vars) |idx| {
        const v: Var = .fromIndex(idx);
        const pos = Literal.init(v, false);
        if (solver.varIsActive(v) and !lit_remap[pos.raw].eql(pos)) return true;
    }
    return false;
}

// Marks each substituted variable eliminated, with a witness frame naming
// its representative.
fn recordSubstitutions(solver: *Solver, lit_remap: []const Literal) !void {
    for (0..solver.num_vars) |idx| {
        const v: Var = .fromIndex(idx);
        if (!solver.varIsActive(v)) continue;
        const pos = Literal.init(v, false);
        const rep = lit_remap[pos.raw];
        if (rep.eql(pos)) continue;
        try solver.equiv_witness.append(solver.allocator, .{ .eliminated_var = v, .rep_lit = rep });
        solver.eliminated.set(v.index());
        solver.stats.equiv_substituted_vars += 1;
    }
}

const LongRewrite = struct {
    old_cref: ClauseRef,
    kind: clause_mod.ClauseKind,
    // The rewritten clause in `Rewrite.new_clauses`; null when the rewrite
    // is a tautology or already satisfied, so the clause is just dropped.
    new_index: ?u32,
};

const BinaryRewrite = struct {
    old: [2]Literal,
    new: union(enum) {
        tautology,
        unit: Literal,
        binary: [2]Literal,
    },
};

// Every clause change one substitution makes, collected before any is
// applied: the proof logs each addition while the equivalence binaries
// that justify it under RUP are still in the formula, then every deletion.
const Rewrite = struct {
    solver: *Solver,
    lit_remap: []const Literal,
    long: std.ArrayList(LongRewrite) = .empty,
    // The long clauses' old literals, index-aligned with `long`.
    old_clauses: ClauseList = .{},
    new_clauses: ClauseList = .{},
    binaries: std.ArrayList(BinaryRewrite) = .empty,
    scratch: std.ArrayList(Literal) = .empty,

    fn deinit(self: *Rewrite) void {
        const allocator = self.solver.allocator;
        self.long.deinit(allocator);
        self.old_clauses.deinit(allocator);
        self.new_clauses.deinit(allocator);
        self.binaries.deinit(allocator);
        self.scratch.deinit(allocator);
    }

    fn isEmpty(self: *const Rewrite) bool {
        return self.long.items.len == 0 and self.binaries.items.len == 0;
    }

    fn collect(self: *Rewrite) !void {
        var live = self.solver.arena.liveClauses();
        while (live.next()) |cref| try self.collectLong(cref);
        var binaries = self.solver.binaryClauses();
        while (binaries.next()) |pair| try self.collectBinary(pair);
    }

    fn collectLong(self: *Rewrite, cref: ClauseRef) !void {
        const solver = self.solver;
        const allocator = solver.allocator;
        const lits = solver.arena.literals(cref);
        if (lits.len < 3) return;
        const changes = for (lits) |lit| {
            if (!self.lit_remap[lit.raw].eql(lit)) break true;
        } else false;
        if (!changes or solver.clauseIsLocked(cref)) return;

        self.scratch.clearRetainingCapacity();
        for (lits) |lit| try self.scratch.append(allocator, self.lit_remap[lit.raw]);
        var new_index: ?u32 = null;
        if (common.normalizeAtRoot(&solver.assignment, self.scratch.items)) |new_lits| {
            new_index = @intCast(self.new_clauses.count());
            try self.new_clauses.append(allocator, new_lits);
        }
        try self.old_clauses.append(allocator, lits);
        try self.long.append(allocator, .{ .old_cref = cref, .kind = solver.arena.kind(cref), .new_index = new_index });
    }

    fn collectBinary(self: *Rewrite, old: [2]Literal) !void {
        const a = self.lit_remap[old[0].raw];
        const b = self.lit_remap[old[1].raw];
        if (a.eql(old[0]) and b.eql(old[1])) return;
        try self.binaries.append(self.solver.allocator, .{
            .old = old,
            .new = if (a.eql(b.negate())) .tautology else if (a.eql(b)) .{ .unit = a } else .{ .binary = .{ a, b } },
        });
    }

    fn logProof(self: *const Rewrite) !void {
        const proof = &self.solver.proof;
        for (0..self.new_clauses.count()) |i| try proof.addClause(self.new_clauses.get(i));
        for (self.binaries.items) |rewrite| {
            switch (rewrite.new) {
                .tautology => {},
                .unit => |unit| try proof.addClause(&.{unit}),
                .binary => |new| try proof.addClause(&new),
            }
        }
        for (0..self.old_clauses.count()) |i| try proof.deleteClause(self.old_clauses.get(i));
        for (self.binaries.items) |rewrite| try proof.deleteClause(&rewrite.old);
    }

    fn apply(self: *const Rewrite) !state.RootUnit {
        const solver = self.solver;
        for (self.long.items) |rewrite| {
            solver.arena.markDeleted(rewrite.old_cref);
            const new_index = rewrite.new_index orelse continue;
            const new_lits = self.new_clauses.get(new_index);
            const lbd = clause_mod.rewrittenLbd(solver.arena.lbd(rewrite.old_cref), new_lits.len);
            if (try solver.installClause(new_lits, rewrite.kind, lbd) == .refuted) return .refuted;
        }
        for (self.binaries.items) |rewrite| {
            solver.removeBinary(rewrite.old[0], rewrite.old[1]);
            switch (rewrite.new) {
                .tautology => {},
                .unit => |unit| if (try solver.assertRootUnit(unit) == .refuted) return .refuted,
                .binary => |new| try solver.addBinary(new[0], new[1]),
            }
        }
        return .consistent;
    }
};

// Walk `equiv_witness` in reverse and synthesize a value for every
// equiv-substituted variable from the current value of its representative.
// An unassigned rep (the rep variable was never branched or propagated)
// defaults to `true`. This runs only on .sat, before the model is checked
// against the formula, when every non-eliminated variable has a value.
pub fn reconstructEquivVars(self: *Solver) void {
    const frames = self.equiv_witness.items;
    if (frames.len == 0) return;

    var idx: usize = frames.len;
    while (idx > 0) {
        idx -= 1;
        const frame = frames[idx];
        const rep_value = self.assignment.valueOfLiteral(frame.rep_lit);
        self.assignment.setValue(frame.eliminated_var, rep_value != .false);
    }
}

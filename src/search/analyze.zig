const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const Conflict = core.clause.Conflict;
const Reason = core.assignment.Reason;

const state = @import("state.zig");
const Solver = state.Solver;

// The false literals whose assignment forced the literal that `reason`
// implies: every literal of the reason clause after the implied one at
// index 0, or a binary reason's partner, copied into `scratch`.
inline fn antecedents(self: *Solver, reason: Reason, scratch: *[1]Literal) []const Literal {
    if (reason.isBinary()) {
        scratch[0] = reason.binaryOther();
        return scratch;
    }
    return self.arena.literals(reason.clauseRef())[1..];
}

// One bit per decision level, folded mod 64: a cheap superset test for
// "some learned literal has this level".
inline fn levelBit(level: u32) u64 {
    return @as(u64, 1) << @intCast(level & 63);
}

// 1-UIP conflict analysis. Builds the learned clause into
// analyze_learned, asserting literal at index 0, next-highest-level
// literal at index 1 (ready to be the second watch). Returns the
// backjump level.
//
// `conflict_level` is the maximum level of any literal in the initial
// conflict. Under classical backtracking it equals the current decision
// level; under chronological backtracking the trail may be out-of-order
// and the conflict can fire at a level below self.level, so the caller
// computes it from the conflict lits.
pub fn analyze(self: *Solver, conflict: Conflict, conflict_level: u32) !u32 {
    self.analyze_learned.clearRetainingCapacity();
    self.analyze_levels.clearRetainingCapacity();
    try self.analyze_learned.append(self.allocator, undefined);
    const uip = try resolveToFirstUip(self, conflict, conflict_level);
    self.analyze_learned.items[0] = uip.negate();
    minimizeLearned(self);
    return placeBackjumpLiteral(self);
}

// Resolves the conflict with the reasons of its conflict-level literals,
// latest first, until one such literal is left: the first UIP, which it
// returns. The learned clause's other literals are appended as found.
fn resolveToFirstUip(self: *Solver, conflict: Conflict, conflict_level: u32) !Literal {
    var counter: u32 = 0;
    var trail_idx: isize = @as(isize, @intCast(self.assignment.trail.items.len)) - 1;
    var binary_scratch: [2]Literal = undefined;
    var antecedent_scratch: [1]Literal = undefined;
    var lits: []const Literal = switch (conflict) {
        .clause => |cref| self.arena.literals(cref),
        .binary => |two| blk: {
            binary_scratch = two;
            break :blk &binary_scratch;
        },
    };

    while (true) {
        for (lits) |q| {
            const v = q.variable();
            if (self.analyze_seen[v]) continue;
            const q_level = self.assignment.vars[v].level;
            if (q_level == 0) continue;

            self.analyze_seen[v] = true;
            self.bumpVarActivity(v);
            if (q_level >= conflict_level) {
                counter += 1;
            } else {
                try self.analyze_learned.append(self.allocator, q);
            }
        }

        // Under chrono, seen variables below the conflict level can sit
        // among its trail entries; they are already in the learned clause.
        while (trail_idx >= 0) {
            const tv = self.assignment.trail.items[@intCast(trail_idx)].variable();
            if (self.analyze_seen[tv] and self.assignment.vars[tv].level == conflict_level) break;
            trail_idx -= 1;
        }
        std.debug.assert(trail_idx >= 0);
        const resolved = self.assignment.trail.items[@intCast(trail_idx)];
        const rv = resolved.variable();
        self.analyze_seen[rv] = false;
        counter -= 1;
        trail_idx -= 1;
        if (counter == 0) return resolved;

        const reason = self.assignment.vars[rv].reason;
        std.debug.assert(!reason.isNone());
        lits = antecedents(self, reason, &antecedent_scratch);
    }
}

// Recursive clause minimization (MiniSat 2.2): drops each learned literal
// implied by the others through reason chains. Shorter learned clauses
// mean shorter watch lists and cheaper propagation.
fn minimizeLearned(self: *Solver) void {
    const learned = &self.analyze_learned;
    self.analyze_seen[learned.items[0].variable()] = true;

    var abstract_levels: u64 = 0;
    for (learned.items) |lit| abstract_levels |= levelBit(self.assignment.vars[lit.variable()].level);

    self.analyze_to_clear.clearRetainingCapacity();
    var kept: usize = 1;
    for (learned.items[1..]) |lit| {
        const v = lit.variable();
        if (self.assignment.vars[v].reason.isNone() or !litRedundant(self, v, abstract_levels)) {
            learned.items[kept] = lit;
            kept += 1;
        } else {
            self.analyze_to_clear.appendAssumeCapacity(v);
        }
    }
    learned.shrinkRetainingCapacity(kept);

    for (learned.items) |lit| self.analyze_seen[lit.variable()] = false;
    for (self.analyze_to_clear.items) |v| self.analyze_seen[v] = false;
}

// Iterative MiniSat-2.2 redundancy check. Returns true if the literal of
// `start_var` (which is in the learned clause, with a non-null reason)
// is implied by the rest of the learned clause — i.e. can be removed by
// self-subsuming resolution.
//
// Walks back through reason chains; a literal `q` in some reason is
// acceptable if it is already `seen` OR has a reason whose decision
// level falls in `abstract_levels`, in which case we recurse. Any other
// case — a decision, a level-0 literal, or a literal whose level isn't
// in the mask — aborts the probe and rolls back any seen flags set
// since entering this call.
//
// Precondition: `self.assignment.vars[start_var].reason` is non-none
// and `analyze_stack` / `analyze_to_clear` have capacity >= num_vars.
fn litRedundant(self: *Solver, start_var: u32, abstract_levels: u64) bool {
    self.analyze_stack.clearRetainingCapacity();
    self.analyze_stack.appendAssumeCapacity(start_var);
    const top = self.analyze_to_clear.items.len;
    var antecedent_scratch: [1]Literal = undefined;

    while (self.analyze_stack.pop()) |v| {
        const reason = self.assignment.vars[v].reason;
        std.debug.assert(!reason.isNone());
        for (antecedents(self, reason, &antecedent_scratch)) |q| {
            const qv = q.variable();
            const q_level = self.assignment.vars[qv].level;
            if (self.analyze_seen[qv] or q_level == 0) continue;

            if (!self.assignment.vars[qv].reason.isNone() and (abstract_levels & levelBit(q_level)) != 0) {
                self.analyze_seen[qv] = true;
                self.analyze_stack.appendAssumeCapacity(qv);
                self.analyze_to_clear.appendAssumeCapacity(qv);
            } else {
                for (self.analyze_to_clear.items[top..]) |cv| self.analyze_seen[cv] = false;
                self.analyze_to_clear.shrinkRetainingCapacity(top);
                return false;
            }
        }
    }
    return true;
}

// Moves the highest-level literal after the UIP to index 1, where it will
// be watched, and returns its level: the backjump level.
fn placeBackjumpLiteral(self: *Solver) u32 {
    const learned = self.analyze_learned.items;
    if (learned.len == 1) return 0;
    var highest_index: usize = 1;
    var highest_level = self.assignment.vars[learned[1].variable()].level;
    for (learned[2..], 2..) |lit, k| {
        const level = self.assignment.vars[lit.variable()].level;
        if (level > highest_level) {
            highest_level = level;
            highest_index = k;
        }
    }
    std.mem.swap(Literal, &learned[1], &learned[highest_index]);
    return highest_level;
}

pub fn computeLbd(self: *Solver, lits: []const Literal) u32 {
    self.analyze_levels.clearRetainingCapacity();
    outer: for (lits) |lit| {
        const lv = self.assignment.vars[lit.variable()].level;
        if (lv == 0) continue;
        for (self.analyze_levels.items) |existing| {
            if (existing == lv) continue :outer;
        }
        self.analyze_levels.appendAssumeCapacity(lv);
    }
    return @intCast(self.analyze_levels.items.len);
}

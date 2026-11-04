const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const Conflict = core.clause.Conflict;

const state = @import("state.zig");
const Solver = state.Solver;

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

    // Scratch for synthesizing the 2-lit view of a binary reason. lits[0]
    // is the forced literal (which we skip below), so we leave it
    // undefined and only populate lits[1].
    var binary_scratch: [2]Literal = undefined;

    while (self.analyze_stack.items.len > 0) {
        const v = self.analyze_stack.pop().?;
        const reason = self.assignment.vars[v].reason;
        std.debug.assert(!reason.isNone());

        const lits: []const Literal = if (reason.isBinary()) blk: {
            binary_scratch[1] = reason.binaryOther();
            break :blk binary_scratch[0..2];
        } else self.clauseLits(reason.clauseRef());

        var k: usize = 1;
        while (k < lits.len) : (k += 1) {
            const q = lits[k];
            const qv = q.variable();
            const qlevel = self.assignment.vars[qv].level;
            if (self.analyze_seen[qv] or qlevel == 0) continue;

            if (!self.assignment.vars[qv].reason.isNone() and
                (abstract_levels & (@as(u64, 1) << @intCast(qlevel & 63))) != 0)
            {
                self.analyze_seen[qv] = true;
                self.analyze_stack.appendAssumeCapacity(qv);
                self.analyze_to_clear.appendAssumeCapacity(qv);
            } else {
                for (self.analyze_to_clear.items[top..]) |cv| {
                    self.analyze_seen[cv] = false;
                }
                self.analyze_to_clear.shrinkRetainingCapacity(top);
                return false;
            }
        }
    }
    return true;
}

// 1-UIP conflict analysis. Builds the learned clause into
// analyze_learned, asserting literal at index 0, next-highest-level
// literal at index 1 (ready to be the second watch). Returns the
// backjump level.
//
// Accepts both arena-backed (long) and implicit (binary) conflicts.
// When walking the reason chain, a binary reason is synthesized on the
// fly into a 2-lit view [forced_lit, binaryOther] so the outer loop is
// oblivious to the clause representation.
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

    var counter: u32 = 0;
    var resolved: Literal = undefined;
    var has_resolved = false;
    var trail_idx: isize = @as(isize, @intCast(self.assignment.trail.items.len)) - 1;

    var binary_scratch: [2]Literal = undefined;

    var lits: []const Literal = switch (conflict) {
        .clause => |cref| self.clauseLits(cref),
        .binary => |two| blk: {
            binary_scratch = two;
            break :blk binary_scratch[0..2];
        },
    };

    while (true) {
        const start: usize = if (has_resolved) 1 else 0;
        for (lits[start..]) |q| {
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
            const tl = self.assignment.trail.items[@intCast(trail_idx)];
            const tv = tl.variable();
            if (self.analyze_seen[tv] and
                self.assignment.vars[tv].level == conflict_level)
            {
                break;
            }
            trail_idx -= 1;
        }
        std.debug.assert(trail_idx >= 0);
        resolved = self.assignment.trail.items[@intCast(trail_idx)];
        has_resolved = true;
        const rv = resolved.variable();
        self.analyze_seen[rv] = false;
        counter -= 1;
        trail_idx -= 1;

        if (counter == 0) break;

        const reason = self.assignment.vars[rv].reason;
        std.debug.assert(!reason.isNone());
        if (reason.isBinary()) {
            binary_scratch[0] = resolved;
            binary_scratch[1] = reason.binaryOther();
            lits = binary_scratch[0..2];
        } else {
            lits = self.clauseLits(reason.clauseRef());
        }
    }

    self.analyze_learned.items[0] = resolved.negate();

    // Recursive clause minimization (MiniSat 2.2 litRedundant)
    // A literal p in the learned clause is redundant if it is implied
    // by the other literals — checked via iterative self-subsuming
    // resolution over reason chains. Shorter learned clauses mean
    // shorter watch lists and cheaper propagation.
    {
        self.analyze_seen[self.analyze_learned.items[0].variable()] = true;

        var abstract_levels: u64 = 0;
        for (self.analyze_learned.items) |lit| {
            const lv = self.assignment.vars[lit.variable()].level;
            abstract_levels |= @as(u64, 1) << @intCast(lv & 63);
        }

        self.analyze_to_clear.clearRetainingCapacity();

        const original_len = self.analyze_learned.items.len;
        var wj: usize = 1;
        var wk: usize = 1;
        while (wk < original_len) : (wk += 1) {
            const lit = self.analyze_learned.items[wk];
            const lv = lit.variable();
            if (self.assignment.vars[lv].reason.isNone() or
                !litRedundant(self, lv, abstract_levels))
            {
                self.analyze_learned.items[wj] = lit;
                wj += 1;
            } else {
                self.analyze_to_clear.appendAssumeCapacity(lv);
            }
        }
        self.analyze_learned.shrinkRetainingCapacity(wj);

        for (self.analyze_learned.items) |lit| {
            self.analyze_seen[lit.variable()] = false;
        }
        for (self.analyze_to_clear.items) |cv| {
            self.analyze_seen[cv] = false;
        }
    }

    var backjump: u32 = 0;
    if (self.analyze_learned.items.len > 1) {
        var max_i: usize = 1;
        var max_level = self.assignment.vars[self.analyze_learned.items[1].variable()].level;
        var k: usize = 2;
        while (k < self.analyze_learned.items.len) : (k += 1) {
            const lv = self.assignment.vars[self.analyze_learned.items[k].variable()].level;
            if (lv > max_level) {
                max_level = lv;
                max_i = k;
            }
        }
        const tmp = self.analyze_learned.items[1];
        self.analyze_learned.items[1] = self.analyze_learned.items[max_i];
        self.analyze_learned.items[max_i] = tmp;
        backjump = max_level;
    }

    return backjump;
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

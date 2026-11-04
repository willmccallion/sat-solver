const std = @import("std");
const core = @import("core");
const clause_mod = core.clause;
const Conflict = clause_mod.Conflict;
const Watcher = clause_mod.Watcher;
const Reason = core.assignment.Reason;

const state = @import("state.zig");
const Solver = state.Solver;
const Result = @import("solver.zig").Result;

// Two-watched-literal propagation with a specialized binary-clause fast
// path. Processes the trail from propagation_head to the end, firing
// unit clauses as they appear. Returns a Conflict on conflict or null on
// clean completion.
//
// For each trail literal p we first sweep bin_watchers[p.raw]: every
// entry is a 2-clause (¬p ∨ other), so a single lit_values load on
// `other` resolves it — no arena touch, no compaction, no inner search
// loop. Only after binaries are exhausted do we fall through to the
// long-clause loop with its full two-watched dance.
pub fn propagate(self: *Solver) !?Conflict {
    // Neither buffer moves during propagate, so both pointers stay in registers.
    const lit_values = self.assignment.lit_values.ptr;
    const arena_ptr = self.arena.base();

    while (self.assignment.propagation_head < self.assignment.trail.items.len) {
        const p = self.assignment.trail.items[self.assignment.propagation_head];
        self.assignment.propagation_head += 1;
        self.stats.propagations += 1;

        // Under chrono a forced literal holds at the highest level of its
        // clause's false literals; for a binary (¬p ∨ b) that is p's level.
        const p_level = self.assignment.vars[p.variable()].level;

        const bws = self.bin_watchers[p.raw].items;
        for (bws) |b| {
            const v = lit_values[b.other.raw];
            if (v == .true) continue;
            if (v == .false) {
                @branchHint(.cold);
                self.assignment.propagation_head = self.assignment.trail.items.len;
                return Conflict{ .binary = .{ p.negate(), b.other } };
            }
            try self.assignment.assignAtLevel(
                b.other,
                Reason.fromBinary(p.negate()),
                p_level,
            );
        }

        const ws = &self.watchers[p.raw];
        var i: usize = 0;
        var j: usize = 0;
        const end = ws.items.len;

        outer: while (i < end) {
            const w = ws.items[i];
            i += 1;

            // A true blocker is the most common exit.
            if (lit_values[w.blocker.raw] == .true) {
                @branchHint(.likely);
                ws.items[j] = w;
                j += 1;
                continue;
            }

            // Prefetching the next watcher's clause hides its cache miss
            // behind this iteration's work.
            if (i < end) {
                const next_cref = ws.items[i].clause;
                @prefetch(arena_ptr + next_cref, .{ .locality = 3 });
            }

            const lits = self.arena.literals(w.clause);
            const false_lit = p.negate();

            if (lits[0].eql(false_lit)) {
                lits[0] = lits[1];
                lits[1] = false_lit;
            }
            std.debug.assert(lits[1].eql(false_lit));

            const other = lits[0];
            const new_w: Watcher = .{ .clause = w.clause, .blocker = other };

            if (!other.eql(w.blocker) and lit_values[other.raw] == .true) {
                ws.items[j] = new_w;
                j += 1;
                continue;
            }

            var k: usize = 2;
            while (k < lits.len) : (k += 1) {
                if (lit_values[lits[k].raw] != .false) {
                    lits[1] = lits[k];
                    lits[k] = false_lit;
                    const target = &self.watchers[lits[1].negate().raw];
                    try clause_mod.reserveSlot(Watcher, target, self.allocator);
                    target.appendAssumeCapacity(.{
                        .clause = w.clause,
                        .blocker = other,
                    });
                    continue :outer;
                }
            }

            // No replacement — clause is unit or conflicting.
            ws.items[j] = new_w;
            j += 1;

            if (lit_values[other.raw] == .false) {
                @branchHint(.cold);
                while (i < end) : ({
                    i += 1;
                    j += 1;
                }) {
                    ws.items[j] = ws.items[i];
                }
                ws.shrinkRetainingCapacity(j);
                self.assignment.propagation_head = self.assignment.trail.items.len;
                return Conflict{ .clause = w.clause };
            } else {
                // The highest level among the clause's false literals. A
                // helper call here costs 4% more instructions on the bench.
                var force_level: u32 = p_level;
                var lit_idx: usize = 2;
                while (lit_idx < lits.len) : (lit_idx += 1) {
                    const level = self.assignment.vars[lits[lit_idx].variable()].level;
                    if (level > force_level) force_level = level;
                }
                try self.assignment.assignAtLevel(
                    other,
                    Reason.fromClause(w.clause),
                    force_level,
                );
            }
        }

        ws.shrinkRetainingCapacity(j);
    }

    return null;
}

// Propagates at level 0, where a conflict refutes the formula: logs the
// empty clause and returns .unsat.
pub fn propagateAtRoot(self: *Solver) !?Result {
    std.debug.assert(self.assignment.level == 0);
    if ((try self.propagate()) == null) return null;
    try self.proof.empty();
    return .unsat;
}

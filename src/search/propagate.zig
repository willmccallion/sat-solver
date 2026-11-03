const core = @import("core");
const clause_mod = core.clause;
const Conflict = clause_mod.Conflict;
const Watcher = clause_mod.Watcher;
const Reason = core.assignment.Reason;

const state = @import("state.zig");
const Solver = state.Solver;

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
    // Hoist into register-friendly locals. Neither pointer changes
    // across the body of propagate: assign() writes into lit_values
    // through the same allocation, and the arena is never grown from
    // inside propagate. Pinning them here keeps both in a register.
    const lit_values = self.assignment.lit_values.ptr;
    const arena_ptr = self.arena.items.ptr;

    while (self.assignment.propagation_head < self.assignment.trail.items.len) {
        const p = self.assignment.trail.items[self.assignment.propagation_head];
        self.assignment.propagation_head += 1;
        self.stats.propagations += 1;

        // Under chronological backtracking the trail is not monotonic in
        // level, so the level at which a forced literal "naturally"
        // holds is max over the falsified clause lits rather than the
        // current decision level. For a binary (¬p ∨ b) the only
        // falsified lit is ¬p, so the force level is simply p's level.
        // For long clauses we compute the max when we hit the unit case.
        const p_level = self.assignment.vars[p.variable()].level;

        // Binary fast path
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

        // Long-clause path
        const ws = &self.watchers[p.raw];
        var i: usize = 0;
        var j: usize = 0;
        const end = ws.items.len;

        outer: while (i < end) {
            const w = ws.items[i];
            i += 1;

            // Blocker-satisfied is the dominant exit on the bench (~70%).
            if (lit_values[w.blocker.raw] == .true) {
                @branchHint(.likely);
                ws.items[j] = w;
                j += 1;
                continue;
            }

            // Prefetch the next watcher's clause line before we touch
            // this one's. The clause-body load was 12% in the old perf
            // profile; issuing this prefetch hides its L2/L3 latency
            // behind the current iteration's arithmetic.
            if (i < end) {
                const next_cref = ws.items[i].clause;
                @prefetch(arena_ptr + next_cref, .{ .locality = 3 });
            }

            const lits = self.clauseLits(w.clause);
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
                // Natural force level = max level of the other lits in
                // the clause (all currently false). Classical trail ⇒
                // collapses to self.level, so the expense only shows up
                // on genuine chrono paths.
                var force_level: u32 = p_level;
                var m: usize = 2;
                while (m < lits.len) : (m += 1) {
                    const lv = self.assignment.vars[lits[m].variable()].level;
                    if (lv > force_level) force_level = lv;
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

const std = @import("std");

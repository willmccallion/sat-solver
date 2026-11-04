const solver_mod = @import("solver.zig");
const Solver = solver_mod.Solver;
const Level = @import("core").assignment.Level;

// Chronological backtracking gate (Möhle/Biere 2018, Kissat default).
// When a learned clause would jump more than this many levels down from
// the conflict point we backtrack by exactly one decision level instead —
// long jumps destroy useful assignments and the chronological path
// re-derives the same learned clause on the way down. The UIP is still
// asserted at its natural (resolution) level via assignAtLevel, so the
// trail goes out-of-order; analyze and backtrack are level-aware rather
// than position-aware to accommodate this.
pub const chrono_level_gap: u32 = 100;

// Compacting backtrack. Starts at trail_lim[target_level] — a valid lower
// bound because every entry below that index was assigned before level
// target+1 was first entered — and walks forward. Each entry at
// vars[v.index()].level > target is popped (its value cleared, phase saved, heap
// re-inserted); each entry ≤ target is kept and shifted left into the
// compacted region.
//
// Under classical CDCL the trail is monotonic in level, so this
// collapses to the old "slice off the tail" behaviour. Under
// chronological backtracking, where earlier chrono-asserted literals
// can live at lower levels than their trail neighbours, the compact
// pass is required for correctness.
pub fn backtrack(self: *Solver, target_level: Level) void {
    const assignment = &self.assignment;
    if (!assignment.level.isAbove(target_level)) return;
    const scan_start = assignment.trail_lim.items[target_level.int()];
    var j: usize = scan_start;
    var i: usize = scan_start;
    const trail_items = assignment.trail.items;
    while (i < trail_items.len) : (i += 1) {
        const lit = trail_items[i];
        const v = lit.variable();
        if (assignment.vars[v.index()].level.isAbove(target_level)) {
            assignment.saved_phases[v.index()] = (assignment.vars[v.index()].value == .true);
            assignment.unassign(v);
            self.order_heap.insert(@backingInt(v));
        } else {
            trail_items[j] = lit;
            j += 1;
        }
    }
    assignment.trail.shrinkRetainingCapacity(j);
    assignment.trail_lim.shrinkRetainingCapacity(target_level.int());
    assignment.level = target_level;
    // Kept literals past the boundary may still have watches to visit, and
    // the next asserted literal lands at exactly this index.
    if (assignment.propagation_head > scan_start) assignment.propagation_head = scan_start;
}

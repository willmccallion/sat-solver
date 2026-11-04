const state = @import("state.zig");
const Solver = state.Solver;

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
// vars[v].level > target is popped (its value cleared, phase saved, heap
// re-inserted); each entry ≤ target is kept and shifted left into the
// compacted region.
//
// Under classical CDCL the trail is monotonic in level, so this
// collapses to the old "slice off the tail" behaviour. Under
// chronological backtracking, where earlier chrono-asserted literals
// can live at lower levels than their trail neighbours, the compact
// pass is required for correctness.
pub fn backtrack(self: *Solver, target_level: u32) void {
    const a = &self.assignment;
    if (a.level <= target_level) return;
    const scan_start = a.trail_lim.items[target_level];
    var j: usize = scan_start;
    var i: usize = scan_start;
    const trail_items = a.trail.items;
    while (i < trail_items.len) : (i += 1) {
        const lit = trail_items[i];
        const v = lit.variable();
        if (a.vars[v].level > target_level) {
            a.saved_phases[v] = (a.vars[v].value == .true);
            a.unassign(v);
            self.order_heap.insert(v);
        } else {
            trail_items[j] = lit;
            j += 1;
        }
    }
    a.trail.shrinkRetainingCapacity(j);
    a.trail_lim.shrinkRetainingCapacity(target_level);
    a.level = target_level;
    // Re-propagate everything from the compact boundary on. Kept
    // literals at the current level may still have watcher work to do
    // against the new trail shape, and the UIP we're about to
    // chrono-assert will land at exactly this index.
    if (a.propagation_head > scan_start) a.propagation_head = scan_start;
}

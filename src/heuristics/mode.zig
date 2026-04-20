// Focused/stable mode alternation (CaDiCaL, Kissat). Focused runs the
// Glucose restart strategy; stable suppresses restarts and re-biases
// saved_phases to the trail-peak snapshot on entry so the solver can push
// deeper on the structural branch it has found. Each chunk doubles in
// length so late search runs in long coherent bursts.
pub const stable_initial_budget: u64 = 1000;

pub const Solve = enum { focused, stable };

// Chronological backtracking gate (Möhle/Biere 2018, Kissat default).
// When a learned clause would jump more than this many levels down from
// the conflict point we backtrack by exactly one decision level instead —
// long jumps destroy useful assignments and the chronological path
// re-derives the same learned clause on the way down. The UIP is still
// asserted at its natural (resolution) level via assignAtLevel, so the
// trail goes out-of-order; analyze and backtrack are level-aware rather
// than position-aware to accommodate this.
pub const chrono_level_gap: u32 = 100;

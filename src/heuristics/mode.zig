// Focused/stable mode alternation (CaDiCaL, Kissat). Focused runs the
// Glucose restart strategy; stable suppresses restarts and re-biases
// saved_phases to the trail-peak snapshot on entry so the solver can push
// deeper on the structural branch it has found. Each chunk doubles in
// length so late search runs in long coherent bursts.
pub const stable_initial_budget: u64 = 1000;

pub const SearchMode = enum { focused, stable };

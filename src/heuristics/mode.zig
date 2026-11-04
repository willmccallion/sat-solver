const Schedule = @import("schedule.zig").Schedule;

// Focused/stable mode alternation (CaDiCaL, Kissat). Focused runs the
// Glucose restart strategy; stable suppresses restarts and re-biases
// saved_phases to the trail-peak snapshot on entry so the solver can push
// deeper on the structural branch it has found. Each chunk doubles in
// length so late search runs in long coherent bursts.
pub const schedule: Schedule = .every(1000, .{ .geometric = .{ .num = 2, .den = 1 } });

pub const SearchMode = enum { focused, stable };

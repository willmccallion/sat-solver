const Schedule = @import("schedule.zig").Schedule;

// Rephase cadence. On schedule the solver backtracks to level 0 and
// rotates `saved_phases` through a small family of polarities (best /
// original / inverse / random) so phase saving can escape local minima.
// The interval grows geometrically so late search doesn't thrash the
// branching heuristic.
pub const schedule: Schedule = .every(1000, .by_half);

// Which polarity strategy the next rephase will apply. We cycle through
// the four in order; `.best` copies the trail-peak snapshot, `.original`
// resets to the solver's default (all-false), `.inverse` flips every
// current saved phase, and `.random` seeds a fresh set from a
// deterministic PRNG so reruns are reproducible.
pub const RephaseKind = enum { best, original, inverse, random };

pub fn next(kind: RephaseKind) RephaseKind {
    return switch (kind) {
        .best => .original,
        .original => .inverse,
        .inverse => .random,
        .random => .best,
    };
}

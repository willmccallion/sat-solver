// Rephase cadence. Every `rephase_next` conflicts the solver backtracks
// to level 0 and rotates `saved_phases` through a small family of
// polarities (best / original / inverse / random) so phase saving can
// escape local minima. The interval grows geometrically so late search
// doesn't thrash the branching heuristic.
pub const rephase_initial: u64 = 1000;
pub const rephase_grow_num: u64 = 3;
pub const rephase_grow_den: u64 = 2;

// Which polarity strategy the next rephase will apply. We cycle through
// the four in order; `.best` copies the trail-peak snapshot, `.original`
// resets to the solver's default (all-false), `.inverse` flips every
// current saved phase, and `.random` seeds a fresh set from a
// deterministic PRNG so reruns are reproducible.
pub const Mode = enum { best, original, inverse, random };

pub fn next(m: Mode) Mode {
    return switch (m) {
        .best => .original,
        .original => .inverse,
        .inverse => .random,
        .random => .best,
    };
}

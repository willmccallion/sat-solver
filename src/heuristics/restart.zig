// Glucose-style adaptive restart tunings.
//
// Two EMAs of learned-clause LBD (fast = recent window, slow = long-run
// baseline) plus a "trail" EMA of the trail length at conflict time.
// Restart when recent LBD trends worse than the long-run average — unless
// the current stack is much deeper than the recent trail average, meaning
// search is clearly making progress and we shouldn't throw it away.
//
// Canonical Glucose tunings: fast window ~50, slow window ~10_000, ratio
// 1.25 (equivalent to Glucose's K=0.8 on the inverse form), blocker R=1.4.
// Both EMAs are bias-corrected (Adam style) so the ratio is meaningful
// from the very first conflict — without the correction, slow_raw <<
// fast_raw during the first ~1/alpha_slow conflicts and the ratio runs
// away, causing a restart storm on short searches.
pub const lbd_fast_alpha: f64 = 1.0 / 50.0;
pub const lbd_slow_alpha: f64 = 1.0 / 10_000.0;
pub const restart_ratio: f64 = 1.25;
pub const trail_block_ratio: f64 = 1.4;
pub const restart_min_conflicts: u64 = 50;

pub const var_decay: f64 = 0.95;
pub const rescale_threshold: f64 = 1e100;

// ReduceDB cadence — fires on its own conflict-count budget, independent
// of restarts. The interval grows by `reduce_grow` each trigger so long
// searches don't pay a log-N reduce every few thousand conflicts.
pub const reduce_initial: u64 = 2000;
pub const reduce_grow: u64 = 300;

// Arena compaction cadence. Every N reduceDB calls rebuild the arena
// without deleted-clause holes — vivify's shrink-then-mark-dead path
// leaves one hole per vivified clause, and reduceDB doubles that count
// every few thousand conflicts; without compaction the arena grows
// unboundedly even as the live-clause set stays bounded.
pub const compact_every_reductions: u64 = 4;

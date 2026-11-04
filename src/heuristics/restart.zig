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
const fast_alpha: f64 = 1.0 / 50.0;
const slow_alpha: f64 = 1.0 / 10_000.0;
const restart_ratio: f64 = 1.25;
const trail_block_ratio: f64 = 1.4;
const restart_min_conflicts: u64 = 50;

pub const RestartState = struct {
    lbd_fast: Ema = .init(fast_alpha),
    lbd_slow: Ema = .init(slow_alpha),
    trail_fast: Ema = .init(fast_alpha),
    conflicts_since_restart: u64 = 0,

    pub fn recordLbd(self: *RestartState, lbd: f64) void {
        self.lbd_fast.update(lbd);
        self.lbd_slow.update(lbd);
    }

    pub fn isDue(self: *const RestartState, conflict_trail_len: f64) bool {
        if (self.conflicts_since_restart < restart_min_conflicts) return false;
        const fast = self.lbd_fast.estimate() orelse return false;
        const slow = self.lbd_slow.estimate() orelse return false;
        if (!(fast > slow * restart_ratio)) return false;
        const trail = self.trail_fast.estimate() orelse return true;
        return !(conflict_trail_len > trail * trail_block_ratio);
    }
};

pub const Ema = struct {
    alpha: f64,
    value: f64 = 0,
    // Rises from 0 towards 1; value / bias is the corrected estimate.
    bias: f64 = 0,

    pub fn init(alpha: f64) Ema {
        return .{ .alpha = alpha };
    }

    pub inline fn update(self: *Ema, sample: f64) void {
        self.value += self.alpha * (sample - self.value);
        self.bias += self.alpha * (1 - self.bias);
    }

    // Null until the first sample.
    pub inline fn estimate(self: Ema) ?f64 {
        if (!(self.bias > 0)) return null;
        return self.value / self.bias;
    }
};

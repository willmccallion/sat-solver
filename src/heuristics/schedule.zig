// When a periodic task next runs, counted in conflicts, and how the gap to
// the run after grows so long searches spend less of their time on it.
pub const Schedule = struct {
    next: u64,
    interval: u64,
    growth: Growth,

    pub const Growth = union(enum) {
        geometric: struct { num: u64, den: u64 },
        additive: u64,

        pub const by_half: Growth = .{ .geometric = .{ .num = 3, .den = 2 } };
    };

    pub fn every(initial_interval: u64, growth: Growth) Schedule {
        return .{ .next = initial_interval, .interval = initial_interval, .growth = growth };
    }

    pub inline fn isDue(self: Schedule, conflicts: u64) bool {
        return conflicts >= self.next;
    }

    // Grows the interval and schedules the next run that far past `conflicts`.
    pub fn advance(self: *Schedule, conflicts: u64) void {
        self.interval = switch (self.growth) {
            .geometric => |ratio| (self.interval * ratio.num) / ratio.den,
            .additive => |step| self.interval + step,
        };
        self.next = conflicts + self.interval;
    }
};

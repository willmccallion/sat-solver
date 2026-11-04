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

const testing = @import("std").testing;

test "a schedule is due once the conflict count reaches its next run" {
    const schedule: Schedule = .every(10, .by_half);

    try testing.expect(!schedule.isDue(9));
    try testing.expect(schedule.isDue(10));
}

test "advancing a schedule grows its interval from the current conflict count" {
    var geometric: Schedule = .every(10, .by_half);
    var additive: Schedule = .every(10, .{ .additive = 4 });

    geometric.advance(12);
    additive.advance(12);

    try testing.expectEqual(@as(u64, 15), geometric.interval);
    try testing.expectEqual(@as(u64, 27), geometric.next);
    try testing.expectEqual(@as(u64, 14), additive.interval);
    try testing.expectEqual(@as(u64, 26), additive.next);
}

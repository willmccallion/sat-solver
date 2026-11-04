// Box-drawn, colored report tables, and parsers for the perf stat and
// sat-bench output that sat-profile and sat-compete summarize.

const std = @import("std");
const SolverStats = @import("search").solver.Stats;

pub const Color = struct {
    pub const reset = "\x1b[0m";
    pub const bold = "\x1b[1m";
    pub const dim = "\x1b[2m";
    pub const red = "\x1b[31m";
    pub const green = "\x1b[32m";
    pub const yellow = "\x1b[33m";
    pub const cyan = "\x1b[36m";
    pub const gray = "\x1b[90m";
};

pub const box = struct {
    pub const tl = "╭";
    pub const tr = "╮";
    pub const bl = "╰";
    pub const br = "╯";
    pub const lt = "├";
    pub const rt = "┤";
    const h = "─";
    const v = "│";
};

// Rows `width` columns wide between two borders. A row is written as
// startRow, its text, then endRow with the text's visible width.
pub const Table = struct {
    writer: *std.Io.Writer,
    width: usize,

    pub fn rule(self: Table, left: []const u8, right: []const u8) !void {
        try self.writer.print("{s}{s}", .{ Color.gray, left });
        for (0..self.width - 2) |_| try self.writer.writeAll(box.h);
        try self.writer.print("{s}{s}\n", .{ right, Color.reset });
    }

    pub fn startRow(self: Table) !void {
        try self.writer.print("{s}{s}{s}  ", .{ Color.gray, box.v, Color.reset });
    }

    pub fn endRow(self: Table, visible_cols: usize) !void {
        const used = 2 + visible_cols;
        if (used < self.width - 1) try self.writer.splatByteAll(' ', self.width - 1 - used);
        try self.writer.print("{s}{s}{s}\n", .{ Color.gray, box.v, Color.reset });
    }

    // A row holding just `text`, written in `style`.
    pub fn textRow(self: Table, style: []const u8, text: []const u8) !void {
        try self.startRow();
        try self.writer.print("{s}{s}{s}", .{ style, text, Color.reset });
        try self.endRow(text.len);
    }

    pub fn blankRow(self: Table) !void {
        try self.startRow();
        try self.endRow(0);
    }

    // Writes `text` in `color`, cut to `max_cols` with an ellipsis, and
    // returns the columns it took.
    pub fn writeTruncated(self: Table, color: []const u8, text: []const u8, max_cols: usize) !usize {
        if (text.len <= max_cols) {
            try self.writer.print("{s}{s}{s}", .{ color, text, Color.reset });
            return text.len;
        }
        try self.writer.print("{s}{s}{s}…", .{ color, text[0 .. max_cols - 1], Color.reset });
        return max_cols;
    }

    pub fn sectionHeader(self: Table, text: []const u8) !void {
        try self.rule(box.lt, box.rt);
        try self.blankRow();
        try self.startRow();
        try self.writer.print("{s}{s}{s}", .{ Color.bold, text, Color.reset });
        try self.endRow(text.len);
        try self.blankRow();
    }
};

// The perf stat counters and topdown metrics the reports use.
pub const PerfStat = struct {
    cycles: u64 = 0,
    instructions: u64 = 0,
    branches: u64 = 0,
    branch_misses: u64 = 0,
    cache_references: u64 = 0,
    cache_misses: u64 = 0,
    l1d_loads: u64 = 0,
    l1d_load_misses: u64 = 0,
    llc_loads: u64 = 0,
    llc_load_misses: u64 = 0,
    // Intel topdown level 1, in percent.
    topdown_retiring: f64 = 0,
    topdown_bad_spec: f64 = 0,
    topdown_fe_bound: f64 = 0,
    topdown_be_bound: f64 = 0,

    // Parses `perf stat -x,` output. Hybrid Intel CPUs report every event
    // and the topdown group once per PMU; single-threaded work runs on
    // cpu_core, so cpu_atom rows are skipped. A row with no event column
    // continues the previous row's PMU. Non-hybrid CPUs name no PMU.
    pub fn parse(csv: []const u8) PerfStat {
        var stat: PerfStat = .{};
        var is_atom_pmu = false;
        var lines = std.mem.splitScalar(u8, csv, '\n');
        while (lines.next()) |raw_line| {
            const line = std.mem.trim(u8, raw_line, " \t\r");
            if (line.len == 0 or line[0] == '#') continue;
            const row = Row.parse(line) orelse continue;
            if (std.mem.startsWith(u8, row.event, "cpu_atom/")) is_atom_pmu = true;
            if (std.mem.startsWith(u8, row.event, "cpu_core/")) is_atom_pmu = false;
            if (is_atom_pmu) continue;
            // `<not counted>` and `<not supported>` carry no value.
            if (std.fmt.parseInt(u64, row.value, 10)) |value| stat.addCounter(eventName(row.event), value) else |_| {}
            if (std.fmt.parseFloat(f64, row.metric_value)) |percent| stat.addMetric(metricName(row.metric_unit), percent) else |_| {}
        }
        return stat;
    }

    pub fn ipc(self: PerfStat) f64 {
        if (self.cycles == 0) return 0;
        return @as(f64, @floatFromInt(self.instructions)) / @as(f64, @floatFromInt(self.cycles));
    }

    pub fn branchMissPercent(self: PerfStat) f64 {
        if (self.branches == 0) return 0;
        return @as(f64, @floatFromInt(self.branch_misses)) * 100.0 / @as(f64, @floatFromInt(self.branches));
    }

    fn addCounter(self: *PerfStat, event: []const u8, value: u64) void {
        const fields = .{
            .{ "cycles", "cycles" },
            .{ "instructions", "instructions" },
            .{ "branches", "branches" },
            .{ "branch-misses", "branch_misses" },
            .{ "cache-references", "cache_references" },
            .{ "cache-misses", "cache_misses" },
            .{ "L1-dcache-loads", "l1d_loads" },
            .{ "L1-dcache-load-misses", "l1d_load_misses" },
            .{ "LLC-loads", "llc_loads" },
            .{ "LLC-load-misses", "llc_load_misses" },
        };
        inline for (fields) |field| {
            if (std.mem.eql(u8, event, field[0])) @field(self, field[1]) += value;
        }
    }

    fn addMetric(self: *PerfStat, metric: []const u8, percent: f64) void {
        const fields = .{
            .{ "tma_retiring", "topdown_retiring" },
            .{ "tma_bad_speculation", "topdown_bad_spec" },
            .{ "tma_frontend_bound", "topdown_fe_bound" },
            .{ "tma_backend_bound", "topdown_be_bound" },
        };
        inline for (fields) |field| {
            if (std.mem.eql(u8, metric, field[0])) @field(self, field[1]) += percent;
        }
    }

    // value, unit, event, run time, run percent, metric value, metric unit.
    const Row = struct {
        value: []const u8,
        event: []const u8,
        metric_value: []const u8,
        metric_unit: []const u8,

        fn parse(line: []const u8) ?Row {
            var fields = std.mem.splitScalar(u8, line, ',');
            const value = fields.next() orelse return null;
            _ = fields.next() orelse return null;
            const event = fields.next() orelse return null;
            _ = fields.next() orelse return null;
            _ = fields.next() orelse return null;
            return .{
                .value = value,
                .event = event,
                .metric_value = fields.next() orelse "",
                .metric_unit = fields.next() orelse "",
            };
        }
    };

    // `cpu_core/cycles/u` and `cycles:u` both name `cycles`.
    fn eventName(event: []const u8) []const u8 {
        var name = event;
        for ([_][]const u8{ "cpu_core/", "cpu_atom/" }) |pmu| {
            if (std.mem.startsWith(u8, name, pmu)) name = name[pmu.len..];
        }
        for ([_][]const u8{ "/u", "/", ":u" }) |suffix| {
            if (std.mem.endsWith(u8, name, suffix)) name = name[0 .. name.len - suffix.len];
        }
        return name;
    }

    // `%  tma_retiring` names `tma_retiring`.
    fn metricName(unit: []const u8) []const u8 {
        const trimmed = std.mem.trim(u8, unit, " \t");
        const without_percent = if (std.mem.startsWith(u8, trimmed, "%")) trimmed[1..] else trimmed;
        return std.mem.trim(u8, without_percent, " \t");
    }
};

// The summary sat-bench prints after a run; see the format in bench.zig.
pub const BenchSummary = struct {
    instance_count: u64 = 0,
    sat_count: u64 = 0,
    unsat_count: u64 = 0,
    unknown_count: u64 = 0,
    elapsed_ns: u64 = 0,
    dist_min_ms: f64 = 0,
    dist_p50_ms: f64 = 0,
    dist_p90_ms: f64 = 0,
    dist_p99_ms: f64 = 0,
    dist_max_ms: f64 = 0,
    solver: SolverStats = .{},
    peak_rss_kb: u64 = 0,
    par2_s: f64 = 0,
    timeout_s: u64 = 0,

    pub const ParseError = error{MalformedBenchSummary};

    // A line that does not match the format is an error rather than a
    // zero, so a change to sat-bench's output cannot pass unnoticed.
    pub fn parse(output: []const u8) ParseError!BenchSummary {
        var summary: BenchSummary = .{};
        var lines = std.mem.splitScalar(u8, output, '\n');
        while (lines.next()) |raw_line| {
            const line = std.mem.trim(u8, raw_line, " \t\r");
            if (std.mem.startsWith(u8, line, "solved ")) {
                try summary.parseSolved(line["solved ".len..]);
            } else if (std.mem.startsWith(u8, line, "total ")) {
                var words = std.mem.tokenizeScalar(u8, line["total ".len..], ' ');
                summary.elapsed_ns = @intFromFloat(try parseFloat(words.next()) * 1e6);
            } else if (std.mem.startsWith(u8, line, "dist_ms:")) {
                try summary.parseDistribution(line["dist_ms:".len..]);
            } else if (std.mem.startsWith(u8, line, "stats:")) {
                try summary.parseSolverStats(line["stats:".len..]);
            } else if (std.mem.startsWith(u8, line, "peak_rss_kb:")) {
                summary.peak_rss_kb = try parseInt(std.mem.trim(u8, line["peak_rss_kb:".len..], " "));
            } else if (std.mem.startsWith(u8, line, "par2_s:")) {
                summary.par2_s = try parseFloat(std.mem.trim(u8, line["par2_s:".len..], " "));
            } else if (std.mem.startsWith(u8, line, "timeout_s:")) {
                summary.timeout_s = try parseInt(std.mem.trim(u8, line["timeout_s:".len..], " "));
            }
        }
        return summary;
    }

    // "N instances: X SAT, Y UNSAT, Z unknown"
    fn parseSolved(self: *BenchSummary, text: []const u8) ParseError!void {
        var words = std.mem.tokenizeScalar(u8, text, ' ');
        self.instance_count = try parseInt(words.next());
        try expectWord(words.next(), "instances:");
        self.sat_count = try parseInt(words.next());
        try expectWord(words.next(), "SAT,");
        self.unsat_count = try parseInt(words.next());
        try expectWord(words.next(), "UNSAT,");
        self.unknown_count = try parseInt(words.next());
        try expectWord(words.next(), "unknown");
    }

    fn parseDistribution(self: *BenchSummary, text: []const u8) ParseError!void {
        var pairs = std.mem.tokenizeScalar(u8, text, ' ');
        while (pairs.next()) |pair| {
            const key, const value = try splitPair(pair);
            const ms = try parseFloat(value);
            inline for (.{ "min", "p50", "p90", "p99", "max" }) |name| {
                if (std.mem.eql(u8, key, name)) @field(self, "dist_" ++ name ++ "_ms") = ms;
            }
        }
    }

    fn parseSolverStats(self: *BenchSummary, text: []const u8) ParseError!void {
        var pairs = std.mem.tokenizeScalar(u8, text, ' ');
        while (pairs.next()) |pair| {
            const key, const value = try splitPair(pair);
            const count = try parseInt(value);
            inline for (comptime std.meta.fieldNames(SolverStats)) |name| {
                if (std.mem.eql(u8, key, name)) @field(self.solver, name) = count;
            }
        }
    }

    fn splitPair(pair: []const u8) ParseError!struct { []const u8, []const u8 } {
        const eq = std.mem.indexOfScalar(u8, pair, '=') orelse return error.MalformedBenchSummary;
        return .{ pair[0..eq], pair[eq + 1 ..] };
    }

    fn expectWord(word: ?[]const u8, expected: []const u8) ParseError!void {
        if (!std.mem.eql(u8, word orelse "", expected)) return error.MalformedBenchSummary;
    }

    fn parseInt(text: ?[]const u8) ParseError!u64 {
        return std.fmt.parseInt(u64, text orelse "", 10) catch error.MalformedBenchSummary;
    }

    fn parseFloat(text: ?[]const u8) ParseError!f64 {
        return std.fmt.parseFloat(f64, text orelse "") catch error.MalformedBenchSummary;
    }
};

const testing = std.testing;

test "perf stat parsing keeps cpu_core counters and topdown metrics" {
    const stat = PerfStat.parse(@embedFile("testdata/perf_stat.txt"));

    try testing.expectEqual(@as(u64, 379675393), stat.cycles);
    try testing.expectEqual(@as(u64, 808507626), stat.instructions);
    try testing.expectEqual(@as(u64, 5380043), stat.branch_misses);
    try testing.expectEqual(@as(u64, 206243), stat.l1d_load_misses);
    try testing.expectEqual(@as(u64, 107), stat.llc_load_misses);
    try testing.expectEqual(@as(f64, 31.5), stat.topdown_retiring);
    try testing.expectEqual(@as(f64, 31.9), stat.topdown_bad_spec);
    try testing.expectEqual(@as(f64, 24.7), stat.topdown_fe_bound);
    try testing.expectEqual(@as(f64, 11.9), stat.topdown_be_bound);
}

test "perf stat parsing reads events with a :u modifier" {
    const stat = PerfStat.parse("1200,,cycles:u,10,100.00,,\n3000,,instructions:u,10,100.00,,\n");

    try testing.expectEqual(@as(f64, 2.5), stat.ipc());
}

test "bench summary parsing reads every line sat-bench prints" {
    const summary = try BenchSummary.parse(@embedFile("testdata/bench_summary.txt"));

    try testing.expectEqual(@as(u64, 1000), summary.instance_count);
    try testing.expectEqual(@as(u64, 1000), summary.sat_count);
    try testing.expectEqual(@as(u64, 72_000_000), summary.elapsed_ns);
    try testing.expectEqual(@as(f64, 0.074), summary.dist_p99_ms);
    try testing.expectEqual(@as(u64, 5661), summary.solver.conflicts);
    try testing.expectEqual(@as(u64, 2316), summary.solver.resolvents_added);
    try testing.expectEqual(@as(u64, 4724), summary.peak_rss_kb);
    try testing.expectEqual(@as(f64, 0.056), summary.par2_s);
}

test "bench summary parsing rejects a malformed count" {
    try testing.expectError(error.MalformedBenchSummary, BenchSummary.parse("solved many instances: 1 SAT, 0 UNSAT, 0 unknown\n"));
}

test "bench summary parsing rejects a stats pair without a value" {
    try testing.expectError(error.MalformedBenchSummary, BenchSummary.parse("stats: conflicts\n"));
}

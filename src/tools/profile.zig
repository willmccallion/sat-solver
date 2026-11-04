const std = @import("std");
const Allocator = std.mem.Allocator;
const SolverStats = @import("search").solver.Stats;
const report = @import("report.zig");
const Color = report.Color;
const box = report.box;
const Table = report.Table;

// sat-profile — orchestrator for `zig build bench`. Spawns sat-bench
// under `perf stat` (counters + Intel topdown metrics) and `perf
// record` (call-graph sampling), parses both, then prints a dense
// colored summary table. Also runs `perf annotate` on the hottest
// function to show per-instruction hotspots — that's how you find
// which specific loads/stores inside propagate are stalling.
//
// Invocation (normally called via `zig build bench`):
//   sat-profile <sat-bench-binary> <dir> [dir ...]

const events_list =
    "cycles,instructions,branches,branch-misses," ++
    "cache-references,cache-misses," ++
    "L1-dcache-loads,L1-dcache-load-misses," ++
    "LLC-loads,LLC-load-misses";

const width: usize = 68;

// perf entries below this share of samples are noise.
const min_percent: f64 = 0.5;
const min_percent_arg = std.fmt.comptimePrint("{d}", .{min_percent});
// How many hot functions and instructions the report keeps.
const top_n = 8;
// The topdown metrics sum to about 100% when perf reports them at all.
const min_topdown_total_percent: f64 = 0.5;

const Stats = struct {
    perf: report.PerfStat = .{},
    bench: report.BenchSummary = .{},
};

const Hotspot = struct {
    percent: f64,
    symbol: []const u8,
};

const HotInsn = struct {
    percent: f64,
    text: []const u8,
};

const Verdict = enum { good, warn, bad };

// What sat-bench is run on: its own flags, such as `--timeout-sec 30`,
// and the instance directories, which the report also lists.
const Workload = struct {
    sat_bench: []const u8,
    flags: []const []const u8,
    dirs: []const []const u8,

    // sat-bench's command line after `prefix`.
    fn argv(self: Workload, gpa: Allocator, prefix: []const []const u8) ![]const []const u8 {
        var list: std.ArrayList([]const u8) = .empty;
        errdefer list.deinit(gpa);
        try list.appendSlice(gpa, prefix);
        try list.append(gpa, self.sat_bench);
        try list.appendSlice(gpa, self.flags);
        try list.appendSlice(gpa, self.dirs);
        return list.toOwnedSlice(gpa);
    }
};

const perf_data = "bench/.cache/perf.data";

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;

    var stdout_buffer: [8192]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writer(io, &stdout_buffer);
    const stdout = &stdout_writer.interface;
    defer stdout.flush() catch {};

    var stderr_buffer: [1024]u8 = undefined;
    var stderr_writer = std.Io.File.stderr().writer(io, &stderr_buffer);
    const stderr = &stderr_writer.interface;
    defer stderr.flush() catch {};

    const arena = init.arena.allocator();
    const workload = try parseArgs(arena, try init.minimal.args.toSlice(arena), stderr);
    checkPerf(gpa, io, stderr);

    try stdout.print(
        "{s}[1/3] perf stat with topdown (this takes ~7 min, no output until done)...{s}\n",
        .{ Color.dim, Color.reset },
    );
    try stdout.flush();
    const stats = try countEvents(gpa, io, workload, stderr);

    try stdout.print("{s}[2/3] perf record (call-graph sampling)...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();
    try recordSamples(gpa, io, workload, stderr);

    var hotspots: std.ArrayList(Hotspot) = .empty;
    defer {
        for (hotspots.items) |h| gpa.free(h.symbol);
        hotspots.deinit(gpa);
    }
    try findHotspots(gpa, io, &hotspots, stderr);

    var hot_insns: std.ArrayList(HotInsn) = .empty;
    defer {
        for (hot_insns.items) |h| gpa.free(h.text);
        hot_insns.deinit(gpa);
    }
    if (hotspots.items.len > 0) {
        try stdout.print(
            "{s}[3/3] perf annotate `{s}`...{s}\n",
            .{ Color.dim, hotspots.items[0].symbol, Color.reset },
        );
        try stdout.flush();
        try annotateHottest(gpa, io, hotspots.items[0].symbol, &hot_insns, stderr);
    }

    try stdout.writeAll("\n");
    try printReport(.{ .writer = stdout, .width = width }, workload.dirs, &stats, hotspots.items, hot_insns.items);
}

// Prints the message and exits; with stderr failing too there is nowhere
// left to report that.
fn fatal(stderr: *std.Io.Writer, comptime fmt: []const u8, args: anytype) noreturn {
    stderr.print(fmt, args) catch {};
    stderr.flush() catch {};
    std.process.exit(1);
}

// The caller (build.zig) passes sat-bench flags and directories after the
// binary; flags are forwarded, and only directories label the report.
fn parseArgs(arena: Allocator, args: []const []const u8, stderr: *std.Io.Writer) !Workload {
    if (args.len < 3) fatal(stderr, "usage: sat-profile <sat-bench-binary> <dir> [dir ...]\n", .{});
    var flags: std.ArrayList([]const u8) = .empty;
    var dirs: std.ArrayList([]const u8) = .empty;
    var i: usize = 2;
    while (i < args.len) : (i += 1) {
        const arg = args[i];
        if (std.mem.eql(u8, arg, "--timeout-sec")) {
            i += 1;
            if (i >= args.len) fatal(stderr, "sat-profile: --timeout-sec requires a value\n", .{});
            try flags.appendSlice(arena, &.{ arg, args[i] });
        } else if (arg.len > 0 and arg[0] == '-') {
            try flags.append(arena, arg);
        } else {
            try dirs.append(arena, arg);
        }
    }
    return .{ .sat_bench = args[1], .flags = flags.items, .dirs = dirs.items };
}

fn checkPerf(gpa: Allocator, io: std.Io, stderr: *std.Io.Writer) void {
    if (!perfAvailable(gpa, io)) {
        fatal(stderr, "error: `perf` not found. install it (`perf` or `linux-tools` package) and retry.\n", .{});
    }
    const paranoid = readPerfEventParanoid(io) orelse return;
    if (paranoid > 1) fatal(
        stderr,
        "error: /proc/sys/kernel/perf_event_paranoid = {d} (hardware counters require ≤ 1)\n" ++
            "fix:   echo 1 | sudo tee /proc/sys/kernel/perf_event_paranoid\n",
        .{paranoid},
    );
}

// Runs sat-bench under perf stat for the counters and TopdownL1 metrics.
fn countEvents(gpa: Allocator, io: std.Io, workload: Workload, stderr: *std.Io.Writer) !Stats {
    const argv = try workload.argv(gpa, &.{ "perf", "stat", "-x", ",", "-e", events_list, "-M", "TopdownL1", "--" });
    defer gpa.free(argv);
    const result = try std.process.run(gpa, io, .{
        .argv = argv,
        .stdout_limit = .limited(1 << 22),
        .stderr_limit = .limited(1 << 22),
    });
    defer gpa.free(result.stdout);
    defer gpa.free(result.stderr);
    if (result.term != .exited or result.term.exited != 0) {
        fatal(stderr, "perf stat failed (exit code): \n{s}\n", .{result.stderr});
    }
    const bench = report.BenchSummary.parse(result.stdout) catch
        fatal(stderr, "sat-profile: cannot read the sat-bench summary:\n{s}\n", .{result.stdout});
    return .{ .perf = .parse(result.stderr), .bench = bench };
}

fn recordSamples(gpa: Allocator, io: std.Io, workload: Workload, stderr: *std.Io.Writer) !void {
    try std.Io.Dir.cwd().createDirPath(io, "bench/.cache");
    const argv = try workload.argv(gpa, &.{ "perf", "record", "-F", "999", "--call-graph", "dwarf", "-o", perf_data, "--" });
    defer gpa.free(argv);
    var child = try std.process.spawn(io, .{
        .argv = argv,
        .stdin = .ignore,
        .stdout = .inherit,
        .stderr = .inherit,
    });
    const term = try child.wait(io);
    if (term != .exited or term.exited != 0) fatal(stderr, "perf record exited non-zero\n", .{});
}

fn findHotspots(gpa: Allocator, io: std.Io, hotspots: *std.ArrayList(Hotspot), stderr: *std.Io.Writer) !void {
    const result = try std.process.run(gpa, io, .{
        .argv = &.{
            "perf",            "report",
            "-i",              perf_data,
            "--stdio",         "--no-children",
            "--percent-limit", min_percent_arg,
        },
        .stdout_limit = .limited(1 << 22),
        .stderr_limit = .limited(1 << 22),
    });
    defer gpa.free(result.stdout);
    defer gpa.free(result.stderr);
    if (result.term != .exited or result.term.exited != 0) {
        fatal(stderr, "perf report failed:\n{s}\n", .{result.stderr});
    }
    try parsePerfReport(gpa, result.stdout, hotspots);
}

// The report still prints without hot instructions if this fails.
fn annotateHottest(
    gpa: Allocator,
    io: std.Io,
    symbol: []const u8,
    hot_insns: *std.ArrayList(HotInsn),
    stderr: *std.Io.Writer,
) !void {
    const result = try std.process.run(gpa, io, .{
        .argv = &.{
            "perf",            "annotate",
            "-i",              perf_data,
            "--stdio",         "--no-source",
            "--percent-limit", min_percent_arg,
            symbol,
        },
        .stdout_limit = .limited(1 << 23),
        .stderr_limit = .limited(1 << 23),
    });
    defer gpa.free(result.stdout);
    defer gpa.free(result.stderr);
    if (result.term != .exited or result.term.exited != 0) {
        try stderr.print("sat-profile: perf annotate failed, so the report has no hot instructions:\n{s}\n", .{result.stderr});
        return;
    }
    try parsePerfAnnotate(gpa, result.stdout, hot_insns);
}

fn readPerfEventParanoid(io: std.Io) ?i32 {
    var buf: [16]u8 = undefined;
    const contents = std.Io.Dir.cwd().readFile(io, "/proc/sys/kernel/perf_event_paranoid", &buf) catch return null;
    const trimmed = std.mem.trim(u8, contents, " \t\r\n");
    return std.fmt.parseInt(i32, trimmed, 10) catch null;
}

fn perfAvailable(gpa: Allocator, io: std.Io) bool {
    const r = std.process.run(gpa, io, .{
        .argv = &.{ "perf", "--version" },
        .stdout_limit = .limited(1024),
        .stderr_limit = .limited(1024),
    }) catch return false;
    defer gpa.free(r.stdout);
    defer gpa.free(r.stderr);
    return r.term == .exited and r.term.exited == 0;
}

fn parsePerfReport(
    gpa: Allocator,
    output: []const u8,
    hotspots: *std.ArrayList(Hotspot),
) !void {
    var section_is_core = false;
    var saw_core_section = false;
    var it = std.mem.splitScalar(u8, output, '\n');
    while (it.next()) |line| {
        if (std.mem.startsWith(u8, line, "# Samples:")) {
            if (std.mem.indexOf(u8, line, "cpu_core") != null) {
                section_is_core = true;
                saw_core_section = true;
                for (hotspots.items) |h| gpa.free(h.symbol);
                hotspots.clearRetainingCapacity();
            } else if (saw_core_section) {
                section_is_core = false;
            } else {
                section_is_core = true;
            }
            continue;
        }
        if (!section_is_core) continue;
        if (line.len == 0 or line[0] == '#') continue;

        const trimmed = std.mem.trimStart(u8, line, " \t");
        const pct_end = std.mem.indexOfScalar(u8, trimmed, '%') orelse continue;
        const pct = std.fmt.parseFloat(f64, trimmed[0..pct_end]) catch continue;

        const marker = "[.] ";
        const marker_idx = std.mem.indexOf(u8, line, marker) orelse continue;
        const sym = std.mem.trim(u8, line[marker_idx + marker.len ..], " \t\r");
        if (sym.len == 0) continue;

        try hotspots.append(gpa, .{
            .percent = pct,
            .symbol = try gpa.dupe(u8, sym),
        });
        if (hotspots.items.len >= top_n) section_is_core = false;
    }
}

// Parses `perf annotate --stdio --no-source` output for the top
// function. Each assembly line looks like:
//   <spaces><percent> : <addr>: <instruction>
// We match the percent, keep the instruction text, return the top N.
fn parsePerfAnnotate(
    gpa: Allocator,
    output: []const u8,
    hot_insns: *std.ArrayList(HotInsn),
) !void {
    var it = std.mem.splitScalar(u8, output, '\n');
    while (it.next()) |raw_line| {
        // Find ` : ` which separates the percent column from the rest.
        const colon_sep = std.mem.indexOf(u8, raw_line, " : ") orelse continue;
        const pct_part = std.mem.trim(u8, raw_line[0..colon_sep], " \t");
        if (pct_part.len == 0) continue;
        const pct = std.fmt.parseFloat(f64, pct_part) catch continue;
        if (pct < min_percent) continue;

        // Everything after " : " is "<addr>: <instruction>". Split on
        // the first ": " within to drop the address column.
        const rest = raw_line[colon_sep + 3 ..];
        const addr_end = std.mem.indexOf(u8, rest, ": ") orelse continue;
        const insn_raw = std.mem.trim(u8, rest[addr_end + 2 ..], " \t\r");
        if (insn_raw.len == 0) continue;

        // Collapse internal whitespace for a cleaner display.
        var cleaned: std.ArrayList(u8) = .empty;
        defer cleaned.deinit(gpa);
        var prev_space = false;
        for (insn_raw) |c| {
            if (c == '\t' or c == ' ') {
                if (!prev_space) try cleaned.append(gpa, ' ');
                prev_space = true;
            } else {
                try cleaned.append(gpa, c);
                prev_space = false;
            }
        }

        try hot_insns.append(gpa, .{
            .percent = pct,
            .text = try gpa.dupe(u8, cleaned.items),
        });
    }

    // Keep only the top `top_n` by percent.
    std.mem.sort(HotInsn, hot_insns.items, {}, struct {
        fn lessThan(_: void, a: HotInsn, b: HotInsn) bool {
            return a.percent > b.percent;
        }
    }.lessThan);
    while (hot_insns.items.len > top_n) {
        gpa.free(hot_insns.items[hot_insns.items.len - 1].text);
        _ = hot_insns.pop();
    }
}

fn ipcVerdict(ipc: f64) Verdict {
    if (ipc >= 2.5) return .good;
    if (ipc >= 1.5) return .warn;
    return .bad;
}
fn brMissVerdict(pct: f64) Verdict {
    if (pct < 1.0) return .good;
    if (pct < 5.0) return .warn;
    return .bad;
}
fn l1dMissVerdict(pct: f64) Verdict {
    if (pct < 1.0) return .good;
    if (pct < 3.0) return .warn;
    return .bad;
}

fn verdictColor(v: Verdict) []const u8 {
    return switch (v) {
        .good => Color.green,
        .warn => Color.yellow,
        .bad => Color.red,
    };
}

fn verdictLabel(v: Verdict) []const u8 {
    return switch (v) {
        .good => " OK ",
        .warn => "WARN",
        .bad => "BAD ",
    };
}

fn formatCount(buf: []u8, n: u64) []const u8 {
    const nf: f64 = @floatFromInt(n);
    if (n >= 1_000_000_000) return std.fmt.bufPrint(buf, "{d:.2}B", .{nf / 1e9}) catch buf[0..0];
    if (n >= 1_000_000) return std.fmt.bufPrint(buf, "{d:.2}M", .{nf / 1e6}) catch buf[0..0];
    if (n >= 1_000) return std.fmt.bufPrint(buf, "{d:.2}k", .{nf / 1e3}) catch buf[0..0];
    return std.fmt.bufPrint(buf, "{d}", .{n}) catch buf[0..0];
}

fn formatTime(buf: []u8, ns: f64) []const u8 {
    if (ns >= 1e9) return std.fmt.bufPrint(buf, "{d:.2} s", .{ns / 1e9}) catch buf[0..0];
    if (ns >= 1e6) return std.fmt.bufPrint(buf, "{d:.1} ms", .{ns / 1e6}) catch buf[0..0];
    if (ns >= 1e3) return std.fmt.bufPrint(buf, "{d:.1} µs", .{ns / 1e3}) catch buf[0..0];
    return std.fmt.bufPrint(buf, "{d:.0} ns", .{ns}) catch buf[0..0];
}

fn printReport(
    t: Table,
    dirs: []const []const u8,
    stats: *const Stats,
    hotspots: []const Hotspot,
    hot_insns: []const HotInsn,
) !void {
    const elapsed_ns: f64 = @floatFromInt(stats.bench.elapsed_ns);
    try t.rule(box.tl, box.tr);
    try printWorkload(t, dirs, &stats.bench);
    try printDistribution(t, &stats.bench);
    if (hasTopdown(&stats.perf)) try printTopdown(t, &stats.perf);
    try printHardware(t, &stats.perf, elapsed_ns, stats.bench.peak_rss_kb);
    try printSolverActivity(t, &stats.bench);
    try printThroughput(t, elapsed_ns, &stats.bench.solver);
    try printHotspots(t, hotspots, elapsed_ns);
    if (hotspots.len > 0 and hot_insns.len > 0) try printHotInstructions(t, hotspots[0].symbol, hot_insns);
    try t.rule(box.bl, box.br);
}

// `label` padded to `label_cols`, then `value` in cyan and `note` dimmed.
fn valueRow(t: Table, label_cols: usize, label: []const u8, value: []const u8, note: []const u8) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    try t.writer.splatByteAll(' ', label_cols -| label.len);
    try t.writer.print("{s}{s}{s}", .{ Color.cyan, value, Color.reset });
    if (note.len > 0) try t.writer.print("{s}{s}{s}", .{ Color.dim, note, Color.reset });
    try t.endRow(@max(label.len, label_cols) + report.displayWidth(value) + report.displayWidth(note));
}

const workload_label_cols = 11;

fn printWorkload(t: Table, dirs: []const []const u8, bench: *const report.BenchSummary) !void {
    try t.startRow();
    try t.writer.print("{s}{s}sat-bench perf baseline{s}", .{ Color.bold, Color.cyan, Color.reset });
    try t.endRow("sat-bench perf baseline".len);
    try t.blankRow();

    for (dirs, 0..) |dir, i| try valueRow(t, workload_label_cols, if (i == 0) "workload" else "", dir, "");
    var count_buf: [32]u8 = undefined;
    try valueRow(t, workload_label_cols, "instances", try std.fmt.bufPrint(&count_buf, "{d}", .{bench.instance_count}), "");
    try printSolved(t, bench);

    const elapsed_ms = @as(f64, @floatFromInt(bench.elapsed_ns)) / 1e6;
    const per_inst_ms: f64 = if (bench.instance_count > 0) elapsed_ms / @as(f64, @floatFromInt(bench.instance_count)) else 0;
    var value_buf: [32]u8 = undefined;
    var note_buf: [32]u8 = undefined;
    try valueRow(
        t,
        workload_label_cols,
        "wall time",
        try std.fmt.bufPrint(&value_buf, "{d:.1} ms", .{elapsed_ms}),
        try std.fmt.bufPrint(&note_buf, "  ({d:.3} ms / instance)", .{per_inst_ms}),
    );
    // PAR-2, the SAT Competition ranking metric, charges each unsolved
    // instance twice the cap, so it only means something under one.
    if (bench.timeout_s > 0) {
        try valueRow(
            t,
            workload_label_cols,
            "PAR-2",
            try std.fmt.bufPrint(&value_buf, "{d:.2} s", .{bench.par2_s}),
            try std.fmt.bufPrint(&note_buf, "  (cap {d} s/inst)", .{bench.timeout_s}),
        );
    }
    try t.blankRow();
}

// Solved out of attempted, which matters most on a timed bench where not
// every instance finishes.
fn printSolved(t: Table, bench: *const report.BenchSummary) !void {
    try t.startRow();
    try t.writer.writeAll("solved     ");
    var count_buf: [64]u8 = undefined;
    const solved = bench.sat_count + bench.unsat_count;
    const count = try std.fmt.bufPrint(&count_buf, "{d} / {d}", .{ solved, bench.instance_count });
    const color = if (bench.unknown_count == 0)
        Color.green
    else if (solved * 2 >= bench.instance_count)
        Color.yellow
    else
        Color.red;
    try t.writer.print("{s}{s}{s}", .{ color, count, Color.reset });
    var detail_buf: [64]u8 = undefined;
    const detail = try std.fmt.bufPrint(
        &detail_buf,
        "  ({d} SAT, {d} UNSAT, {d} timeout)",
        .{ bench.sat_count, bench.unsat_count, bench.unknown_count },
    );
    try t.writer.print("{s}{s}{s}", .{ Color.dim, detail, Color.reset });
    try t.endRow("solved     ".len + count.len + detail.len);
}

fn printDistribution(t: Table, bench: *const report.BenchSummary) !void {
    try t.sectionHeader("per-instance distribution");
    try distRow(t, "min", bench.dist_min_ms);
    try distRow(t, "p50", bench.dist_p50_ms);
    try distRow(t, "p90", bench.dist_p90_ms);
    try distRow(t, "p99", bench.dist_p99_ms);
    try distRow(t, "max", bench.dist_max_ms);
    try t.blankRow();
}

fn printTopdown(t: Table, perf: *const report.PerfStat) !void {
    try t.sectionHeader("cpu (intel topdown L1)");
    try topdownRow(t, "retiring", perf.topdown_retiring, "doing useful work");
    try topdownRow(t, "bad-speculation", perf.topdown_bad_spec, "branch miss waste");
    try topdownRow(t, "frontend-bound", perf.topdown_fe_bound, "fetch/decode stall");
    try topdownRow(t, "backend-bound", perf.topdown_be_bound, "memory / execute stall");
    try t.blankRow();
}

const metric_label_cols = 20;

fn printHardware(t: Table, perf: *const report.PerfStat, elapsed_ns: f64, peak_rss_kb: u64) !void {
    const cycles: f64 = @floatFromInt(perf.cycles);
    const insns: f64 = @floatFromInt(perf.instructions);
    const l1d_loads: f64 = @floatFromInt(perf.l1d_loads);
    const l1d_miss: f64 = @floatFromInt(perf.l1d_load_misses);
    const ipc = perf.ipc();
    const br_pct = perf.branchMissPercent();
    const l1d_pct: f64 = if (l1d_loads > 0) l1d_miss * 100.0 / l1d_loads else 0;
    const l1d_mpki: f64 = if (insns > 0) l1d_miss * 1000.0 / insns else 0;
    const effective_ghz: f64 = if (elapsed_ns > 0) cycles / elapsed_ns else 0;
    var value_buf: [32]u8 = undefined;

    try t.sectionHeader("hardware metrics");
    try metricRow(t, "IPC", "{d:.2}", .{ipc}, ipcVerdict(ipc), perf.instructions, perf.cycles);
    try valueRow(t, metric_label_cols, "effective clock", try std.fmt.bufPrint(&value_buf, "{d:.2} GHz", .{effective_ghz}), "");
    try metricRow(t, "branch-miss rate", "{d:.1}%", .{br_pct}, brMissVerdict(br_pct), perf.branch_misses, perf.branches);
    try metricRow(t, "L1d miss rate", "{d:.2}%", .{l1d_pct}, l1dMissVerdict(l1d_pct), perf.l1d_load_misses, perf.l1d_loads);
    try valueRow(t, metric_label_cols, "L1d MPKI", try std.fmt.bufPrint(&value_buf, "{d:.1}", .{l1d_mpki}), "   misses per 1k instructions");
    try valueRow(t, metric_label_cols, "LLC absolute misses", formatCount(&value_buf, perf.llc_load_misses), "");
    const rss_mb = @as(f64, @floatFromInt(peak_rss_kb)) / 1024.0;
    try valueRow(t, metric_label_cols, "peak RSS", try std.fmt.bufPrint(&value_buf, "{d:.1} MB", .{rss_mb}), "");
    try t.blankRow();
}

fn printSolverActivity(t: Table, bench: *const report.BenchSummary) !void {
    try t.sectionHeader("solver activity");
    inline for (comptime std.meta.fieldNames(SolverStats)) |name| {
        try solverRow(t, comptime spacedName(name), @field(bench.solver, name), bench.instance_count);
    }
    try t.blankRow();
}

fn printThroughput(t: Table, elapsed_ns: f64, solver: *const SolverStats) !void {
    try t.sectionHeader("throughput (wall time / event)");
    try throughputRow(t, "per decision", elapsed_ns, solver.decisions);
    try throughputRow(t, "per conflict", elapsed_ns, solver.conflicts);
    try throughputRow(t, "per propagation", elapsed_ns, solver.propagations);
    try t.blankRow();
}

fn printHotspots(t: Table, hotspots: []const Hotspot, elapsed_ns: f64) !void {
    try t.sectionHeader("hotspots (self time)");
    if (hotspots.len == 0) {
        try t.textRow(Color.yellow, "(no samples — did perf record succeed?)");
    }
    for (hotspots) |h| try hotspotRow(t, h, elapsed_ns);
    try t.blankRow();
}

fn printHotInstructions(t: Table, symbol: []const u8, hot_insns: []const HotInsn) !void {
    var title_buf: [128]u8 = undefined;
    try t.sectionHeader(try std.fmt.bufPrint(&title_buf, "hot instructions in {s}", .{symbol}));
    for (hot_insns) |h| try hotInsnRow(t, h);
    try t.blankRow();
}

fn hasTopdown(perf: *const report.PerfStat) bool {
    const total = perf.topdown_retiring + perf.topdown_bad_spec +
        perf.topdown_fe_bound + perf.topdown_be_bound;
    return total > min_topdown_total_percent;
}

fn distRow(t: Table, label: []const u8, ms: f64) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    try t.writer.writeAll("  ");
    var vb: [32]u8 = undefined;
    const vstr = formatTime(&vb, ms * 1e6);
    try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
    try t.endRow(label.len + 2 + report.displayWidth(vstr));
}

fn topdownRow(t: Table, label: []const u8, pct: f64, note: []const u8) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    try t.writer.splatByteAll(' ', 20 -| label.len);
    var vb: [32]u8 = undefined;
    const vstr = try std.fmt.bufPrint(&vb, "{d:>5.1}%", .{pct});

    // Colorize based on which bucket: retiring green, others warning-yellow
    const col = if (std.mem.eql(u8, label, "retiring")) Color.green else Color.yellow;
    try t.writer.print("{s}{s}{s}", .{ col, vstr, Color.reset });
    try t.writer.print("   {s}{s}{s}", .{ Color.dim, note, Color.reset });
    try t.endRow(20 + vstr.len + 3 + note.len);
}

fn metricRow(
    t: Table,
    label: []const u8,
    comptime value_fmt: []const u8,
    value_args: anytype,
    v: Verdict,
    hits: u64,
    total: u64,
) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    const label_pad = 20 -| label.len;
    try t.writer.splatByteAll(' ', label_pad);
    var visible: usize = label.len + label_pad;

    var vbuf: [64]u8 = undefined;
    const value_str = try std.fmt.bufPrint(&vbuf, value_fmt, value_args);
    try t.writer.print("{s}{s}{s}", .{ Color.cyan, value_str, Color.reset });
    visible += value_str.len;

    const value_pad: usize = if (value_str.len < 10) 10 - value_str.len else 1;
    try t.writer.splatByteAll(' ', value_pad);
    visible += value_pad;

    try t.writer.print("{s}{s}{s}{s}", .{ verdictColor(v), Color.bold, verdictLabel(v), Color.reset });
    visible += verdictLabel(v).len;

    try t.writer.writeAll("   ");
    visible += 3;

    var hbuf: [32]u8 = undefined;
    const hstr = formatCount(&hbuf, hits);
    var tbuf: [32]u8 = undefined;
    const tstr = formatCount(&tbuf, total);
    try t.writer.print("{s}{s} / {s}{s}", .{ Color.dim, hstr, tstr, Color.reset });
    visible += hstr.len + 3 + tstr.len;

    try t.endRow(visible);
}

/// Width of the label column in the solver activity rows.
const solver_label_width = 24;

/// A `SolverStats` field name as a row label: `chrono_backtracks` reads
/// "chrono backtracks".
fn spacedName(comptime name: []const u8) []const u8 {
    comptime {
        var label: [name.len]u8 = name[0..name.len].*;
        std.mem.replaceScalar(u8, &label, '_', ' ');
        const final = label;
        return &final;
    }
}

fn solverRow(t: Table, label: []const u8, count: u64, instances: u64) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    try t.writer.splatByteAll(' ', solver_label_width -| label.len);

    var cbuf: [32]u8 = undefined;
    const cstr = formatCount(&cbuf, count);
    try t.writer.print("{s}{s}{s}", .{ Color.cyan, cstr, Color.reset });

    const count_pad: usize = if (cstr.len < 10) 10 - cstr.len else 1;
    try t.writer.splatByteAll(' ', count_pad);
    var vis: usize = solver_label_width + cstr.len + count_pad;

    if (instances > 0) {
        var ab: [32]u8 = undefined;
        const avg: f64 = @as(f64, @floatFromInt(count)) / @as(f64, @floatFromInt(instances));
        const avg_u: u64 = @intFromFloat(@round(avg));
        const astr = formatCount(&ab, avg_u);
        try t.writer.print("{s}{s}{s} / instance", .{ Color.dim, astr, Color.reset });
        vis += astr.len + " / instance".len;
    }

    try t.endRow(vis);
}

fn throughputRow(t: Table, label: []const u8, wall_ns: f64, events: u64) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    try t.writer.splatByteAll(' ', 20 -| label.len);

    if (events == 0) {
        try t.writer.print("{s}n/a{s}", .{ Color.dim, Color.reset });
        try t.endRow(20 + 3);
        return;
    }
    const per: f64 = wall_ns / @as(f64, @floatFromInt(events));
    var vb: [32]u8 = undefined;
    const vstr = formatTime(&vb, per);
    try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
    try t.endRow(20 + report.displayWidth(vstr));
}

fn hotspotRow(t: Table, h: Hotspot, wall_ns: f64) !void {
    try t.startRow();

    // Absolute time: percent × wall time.
    var tb: [32]u8 = undefined;
    const ns_in_func = (h.percent / 100.0) * wall_ns;
    const tstr = formatTime(&tb, ns_in_func);
    // Pad tstr to width 9 (right-aligned) for column alignment.
    const tstr_cols = report.displayWidth(tstr);
    const tpad = 9 -| tstr_cols;
    try t.writer.splatByteAll(' ', tpad);
    try t.writer.print("{s}{s}{s}   ", .{ Color.cyan, tstr, Color.reset });

    var pb: [16]u8 = undefined;
    const pstr = try std.fmt.bufPrint(&pb, "{d:>5.1}%", .{h.percent});
    try t.writer.print("{s}{s}{s}   ", .{ Color.yellow, pstr, Color.reset });

    const used = tpad + tstr_cols + 3 + pstr.len + 3;
    const visible = used + try t.writeTruncated(Color.cyan, h.symbol, used);
    try t.endRow(visible);
}

fn hotInsnRow(t: Table, h: HotInsn) !void {
    try t.startRow();
    var pb: [16]u8 = undefined;
    const pstr = try std.fmt.bufPrint(&pb, "{d:>5.1}%", .{h.percent});
    try t.writer.print("{s}{s}{s}   ", .{ Color.yellow, pstr, Color.reset });

    const used = pstr.len + 3;
    const visible = used + try t.writeTruncated(Color.cyan, h.text, used);
    try t.endRow(visible);
}

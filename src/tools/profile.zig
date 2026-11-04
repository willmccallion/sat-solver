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

    const args = try init.minimal.args.toSlice(init.arena.allocator());

    if (args.len < 3) {
        try stderr.writeAll("usage: sat-profile <sat-bench-binary> <dir> [dir ...]\n");
        try stderr.flush();
        std.process.exit(1);
    }

    const sat_bench = args[1];

    // The caller (build.zig) sends a mix of sat-bench flags (e.g.
    // `--timeout-sec 30`) and directory paths after the binary. Split
    // them: forward everything to sat-bench, but only use real dir
    // paths in the "workload" row of the report table.
    var bench_args: std.ArrayList([]const u8) = .empty;
    defer bench_args.deinit(gpa);
    var dirs_list: std.ArrayList([]const u8) = .empty;
    defer dirs_list.deinit(gpa);
    {
        var ai: usize = 2;
        while (ai < args.len) : (ai += 1) {
            const a = args[ai];
            if (std.mem.eql(u8, a, "--timeout-sec")) {
                try bench_args.append(gpa, a);
                ai += 1;
                if (ai >= args.len) {
                    try stderr.writeAll("sat-profile: --timeout-sec requires a value\n");
                    try stderr.flush();
                    std.process.exit(1);
                }
                try bench_args.append(gpa, args[ai]);
            } else if (a.len > 0 and a[0] == '-') {
                try bench_args.append(gpa, a);
            } else {
                try dirs_list.append(gpa, a);
            }
        }
    }
    const dirs = dirs_list.items;

    if (!perfAvailable(gpa, io)) {
        try stderr.writeAll(
            "error: `perf` not found. install it (`perf` or `linux-tools` package) and retry.\n",
        );
        try stderr.flush();
        std.process.exit(1);
    }

    if (readPerfEventParanoid(io)) |paranoid| {
        if (paranoid > 1) {
            try stderr.print(
                "error: /proc/sys/kernel/perf_event_paranoid = {d} (hardware counters require ≤ 1)\n" ++
                    "fix:   echo 1 | sudo tee /proc/sys/kernel/perf_event_paranoid\n",
                .{paranoid},
            );
            try stderr.flush();
            std.process.exit(1);
        }
    }

    try stdout.print(
        "{s}[1/3] perf stat with topdown (this takes ~7 min, no output until done)...{s}\n",
        .{ Color.dim, Color.reset },
    );
    try stdout.flush();

    var stats: Stats = .{};

    // Perf stat pass (counters + TopdownL1)
    {
        var argv: std.ArrayList([]const u8) = .empty;
        defer argv.deinit(gpa);
        try argv.appendSlice(gpa, &.{
            "perf", "stat",
            "-x",   ",",
            "-e",   events_list,
            "-M",   "TopdownL1",
            "--",   sat_bench,
        });
        try argv.appendSlice(gpa, bench_args.items);
        try argv.appendSlice(gpa, dirs);

        const result = try std.process.run(gpa, io, .{
            .argv = argv.items,
            .stdout_limit = .limited(1 << 22),
            .stderr_limit = .limited(1 << 22),
        });
        defer gpa.free(result.stdout);
        defer gpa.free(result.stderr);

        if (result.term != .exited or result.term.exited != 0) {
            try stderr.print("perf stat failed (exit code): \n{s}\n", .{result.stderr});
            try stderr.flush();
            std.process.exit(1);
        }

        stats.bench = report.BenchSummary.parse(result.stdout) catch {
            try stderr.print("sat-profile: cannot read the sat-bench summary:\n{s}\n", .{result.stdout});
            try stderr.flush();
            std.process.exit(1);
        };
        stats.perf = .parse(result.stderr);
    }

    try stdout.print("{s}[2/3] perf record (call-graph sampling)...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();

    const perf_data = "bench/.cache/perf.data";
    try std.Io.Dir.cwd().createDirPath(io, "bench/.cache");

    var hotspots: std.ArrayList(Hotspot) = .empty;
    defer {
        for (hotspots.items) |h| gpa.free(h.symbol);
        hotspots.deinit(gpa);
    }

    var hot_insns: std.ArrayList(HotInsn) = .empty;
    defer {
        for (hot_insns.items) |h| gpa.free(h.text);
        hot_insns.deinit(gpa);
    }

    // Perf record pass
    {
        var argv: std.ArrayList([]const u8) = .empty;
        defer argv.deinit(gpa);
        try argv.appendSlice(gpa, &.{
            "perf",         "record",
            "-F",           "999",
            "--call-graph", "dwarf",
            "-o",           perf_data,
            "--",           sat_bench,
        });
        try argv.appendSlice(gpa, bench_args.items);
        try argv.appendSlice(gpa, dirs);

        var child = try std.process.spawn(io, .{
            .argv = argv.items,
            .stdin = .ignore,
            .stdout = .inherit,
            .stderr = .inherit,
        });
        const term = try child.wait(io);
        if (term != .exited or term.exited != 0) {
            try stderr.writeAll("perf record exited non-zero\n");
            try stderr.flush();
            std.process.exit(1);
        }
    }

    // Perf report (hotspot extraction)
    {
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
            try stderr.print("perf report failed:\n{s}\n", .{result.stderr});
            try stderr.flush();
            std.process.exit(1);
        }
        try parsePerfReport(gpa, result.stdout, &hotspots);
    }

    // Perf annotate on top hot function
    if (hotspots.items.len > 0) {
        try stdout.print(
            "{s}[3/3] perf annotate `{s}`...{s}\n",
            .{ Color.dim, hotspots.items[0].symbol, Color.reset },
        );
        try stdout.flush();

        const result = try std.process.run(gpa, io, .{
            .argv = &.{
                "perf",                   "annotate",
                "-i",                     perf_data,
                "--stdio",                "--no-source",
                "--percent-limit",        min_percent_arg,
                hotspots.items[0].symbol,
            },
            .stdout_limit = .limited(1 << 23),
            .stderr_limit = .limited(1 << 23),
        });
        defer gpa.free(result.stdout);
        defer gpa.free(result.stderr);
        if (result.term == .exited and result.term.exited == 0) {
            try parsePerfAnnotate(gpa, result.stdout, &hot_insns);
        }
    }

    try stdout.writeAll("\n");
    try printReport(.{ .writer = stdout, .width = width }, dirs, &stats, hotspots.items, hot_insns.items);
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
    const cycles: f64 = @floatFromInt(stats.perf.cycles);
    const insns: f64 = @floatFromInt(stats.perf.instructions);
    const branches: f64 = @floatFromInt(stats.perf.branches);
    const brmisses: f64 = @floatFromInt(stats.perf.branch_misses);
    const l1d_loads: f64 = @floatFromInt(stats.perf.l1d_loads);
    const l1d_miss: f64 = @floatFromInt(stats.perf.l1d_load_misses);

    const ipc: f64 = if (cycles > 0) insns / cycles else 0;
    const br_pct: f64 = if (branches > 0) brmisses * 100.0 / branches else 0;
    const l1d_pct: f64 = if (l1d_loads > 0) l1d_miss * 100.0 / l1d_loads else 0;
    const l1d_mpki: f64 = if (insns > 0) l1d_miss * 1000.0 / insns else 0;

    const elapsed_ns_f: f64 = @floatFromInt(stats.bench.elapsed_ns);
    const elapsed_ms = elapsed_ns_f / 1e6;
    const per_inst_ms: f64 = if (stats.bench.instance_count > 0)
        elapsed_ms / @as(f64, @floatFromInt(stats.bench.instance_count))
    else
        0;

    const effective_ghz: f64 = if (elapsed_ns_f > 0) cycles / elapsed_ns_f else 0;

    try t.rule(box.tl, box.tr);
    try t.startRow();
    try t.writer.print("{s}{s}sat-bench perf baseline{s}", .{ Color.bold, Color.cyan, Color.reset });
    try t.endRow("sat-bench perf baseline".len);
    try t.blankRow();

    for (dirs, 0..) |d, i| {
        try t.startRow();
        if (i == 0) try t.writer.writeAll("workload   ") else try t.writer.writeAll("           ");
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, d, Color.reset });
        try t.endRow("workload   ".len + d.len);
    }

    {
        try t.startRow();
        try t.writer.writeAll("instances  ");
        var nb: [32]u8 = undefined;
        const nstr = try std.fmt.bufPrint(&nb, "{d}", .{stats.bench.instance_count});
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, nstr, Color.reset });
        try t.endRow("instances  ".len + nstr.len);
    }
    {
        // solved N/M with a SAT/UNSAT breakdown — the first thing you
        // want to see when switching to a timed industrial bench where
        // not every instance finishes.
        try t.startRow();
        try t.writer.writeAll("solved     ");
        var nb: [64]u8 = undefined;
        const solved = stats.bench.sat_count + stats.bench.unsat_count;
        const nstr = try std.fmt.bufPrint(
            &nb,
            "{d} / {d}",
            .{ solved, stats.bench.instance_count },
        );
        const solved_color = if (stats.bench.unknown_count == 0)
            Color.green
        else if (solved * 2 >= stats.bench.instance_count)
            Color.yellow
        else
            Color.red;
        try t.writer.print("{s}{s}{s}", .{ solved_color, nstr, Color.reset });
        var db: [64]u8 = undefined;
        const dstr = try std.fmt.bufPrint(
            &db,
            "  ({d} SAT, {d} UNSAT, {d} timeout)",
            .{ stats.bench.sat_count, stats.bench.unsat_count, stats.bench.unknown_count },
        );
        try t.writer.print("{s}{s}{s}", .{ Color.dim, dstr, Color.reset });
        try t.endRow("solved     ".len + nstr.len + dstr.len);
    }
    {
        try t.startRow();
        try t.writer.writeAll("wall time  ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.1} ms", .{elapsed_ms});
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        var pb: [32]u8 = undefined;
        const pstr = try std.fmt.bufPrint(&pb, "  ({d:.3} ms / instance)", .{per_inst_ms});
        try t.writer.print("{s}{s}{s}", .{ Color.dim, pstr, Color.reset });
        try t.endRow("wall time  ".len + vstr.len + pstr.len);
    }
    if (stats.bench.timeout_s > 0) {
        // PAR-2 is the actual SAT Competition ranking metric: every
        // solved instance costs its wall time, every unsolved one costs
        // 2× the cap. Only meaningful when a per-instance cap was set.
        try t.startRow();
        try t.writer.writeAll("PAR-2      ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.2} s", .{stats.bench.par2_s});
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        var db: [32]u8 = undefined;
        const dstr = try std.fmt.bufPrint(&db, "  (cap {d} s/inst)", .{stats.bench.timeout_s});
        try t.writer.print("{s}{s}{s}", .{ Color.dim, dstr, Color.reset });
        try t.endRow("PAR-2      ".len + vstr.len + dstr.len);
    }
    try t.blankRow();

    // Per-instance distribution
    try t.sectionHeader("per-instance distribution");
    try distRow(t, "min", stats.bench.dist_min_ms);
    try distRow(t, "p50", stats.bench.dist_p50_ms);
    try distRow(t, "p90", stats.bench.dist_p90_ms);
    try distRow(t, "p99", stats.bench.dist_p99_ms);
    try distRow(t, "max", stats.bench.dist_max_ms);
    try t.blankRow();

    // CPU topdown
    if (hasTopdown(stats)) {
        try t.sectionHeader("cpu (intel topdown L1)");
        try topdownRow(t, "retiring", stats.perf.topdown_retiring, "doing useful work");
        try topdownRow(t, "bad-speculation", stats.perf.topdown_bad_spec, "branch miss waste");
        try topdownRow(t, "frontend-bound", stats.perf.topdown_fe_bound, "fetch/decode stall");
        try topdownRow(t, "backend-bound", stats.perf.topdown_be_bound, "memory / execute stall");
        try t.blankRow();
    }

    // Hardware metrics
    try t.sectionHeader("hardware metrics");
    try metricRow(t, "IPC", "{d:.2}", .{ipc}, ipcVerdict(ipc), stats.perf.instructions, stats.perf.cycles);
    {
        try t.startRow();
        try t.writer.writeAll("effective clock     ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.2} GHz", .{effective_ghz});
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try t.endRow("effective clock     ".len + vstr.len);
    }
    try metricRow(t, "branch-miss rate", "{d:.1}%", .{br_pct}, brMissVerdict(br_pct), stats.perf.branch_misses, stats.perf.branches);
    try metricRow(t, "L1d miss rate", "{d:.2}%", .{l1d_pct}, l1dMissVerdict(l1d_pct), stats.perf.l1d_load_misses, stats.perf.l1d_loads);
    {
        try t.startRow();
        try t.writer.writeAll("L1d MPKI            ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.1}", .{l1d_mpki});
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try t.writer.print("{s}   misses per 1k instructions{s}", .{ Color.dim, Color.reset });
        try t.endRow("L1d MPKI            ".len + vstr.len + "   misses per 1k instructions".len);
    }
    {
        try t.startRow();
        try t.writer.writeAll("LLC absolute misses ");
        var vb: [32]u8 = undefined;
        const vstr = formatCount(&vb, stats.perf.llc_load_misses);
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try t.endRow("LLC absolute misses ".len + vstr.len);
    }
    {
        try t.startRow();
        try t.writer.writeAll("peak RSS            ");
        var vb: [32]u8 = undefined;
        const mb = @as(f64, @floatFromInt(stats.bench.peak_rss_kb)) / 1024.0;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.1} MB", .{mb});
        try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try t.endRow("peak RSS            ".len + vstr.len);
    }
    try t.blankRow();

    // Solver activity
    try t.sectionHeader("solver activity");
    inline for (comptime std.meta.fieldNames(SolverStats)) |name| {
        try solverRow(t, comptime spacedName(name), @field(stats.bench.solver, name), stats.bench.instance_count);
    }
    try t.blankRow();

    // Throughput
    try t.sectionHeader("throughput (wall time / event)");
    try throughputRow(t, "per decision", elapsed_ns_f, stats.bench.solver.decisions);
    try throughputRow(t, "per conflict", elapsed_ns_f, stats.bench.solver.conflicts);
    try throughputRow(t, "per propagation", elapsed_ns_f, stats.bench.solver.propagations);
    try t.blankRow();

    // Hotspots (self time)
    try t.sectionHeader("hotspots (self time)");
    if (hotspots.len == 0) {
        try t.startRow();
        try t.writer.print("{s}(no samples — did perf record succeed?){s}", .{ Color.yellow, Color.reset });
        try t.endRow("(no samples — did perf record succeed?)".len);
    } else {
        for (hotspots) |h| try hotspotRow(t, h, elapsed_ns_f);
    }
    try t.blankRow();

    // Hot instructions inside top function
    if (hotspots.len > 0 and hot_insns.len > 0) {
        var title_buf: [128]u8 = undefined;
        const title = try std.fmt.bufPrint(&title_buf, "hot instructions in {s}", .{hotspots[0].symbol});
        try t.sectionHeader(title);
        for (hot_insns) |h| try hotInsnRow(t, h);
        try t.blankRow();
    }

    try t.rule(box.bl, box.br);
}

fn hasTopdown(s: *const Stats) bool {
    const total = s.perf.topdown_retiring + s.perf.topdown_bad_spec +
        s.perf.topdown_fe_bound + s.perf.topdown_be_bound;
    return total > min_topdown_total_percent;
}

fn distRow(t: Table, label: []const u8, ms: f64) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    try t.writer.writeAll("  ");
    var vb: [32]u8 = undefined;
    const vstr = formatTime(&vb, ms * 1e6);
    try t.writer.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
    try t.endRow(label.len + 2 + vstr.len);
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
    try t.endRow(20 + vstr.len);
}

fn hotspotRow(t: Table, h: Hotspot, wall_ns: f64) !void {
    try t.startRow();

    // Absolute time: percent × wall time.
    var tb: [32]u8 = undefined;
    const ns_in_func = (h.percent / 100.0) * wall_ns;
    const tstr = formatTime(&tb, ns_in_func);
    // Pad tstr to width 9 (right-aligned) for column alignment.
    const tpad = 9 -| tstr.len;
    try t.writer.splatByteAll(' ', tpad);
    try t.writer.print("{s}{s}{s}   ", .{ Color.cyan, tstr, Color.reset });

    var pb: [16]u8 = undefined;
    const pstr = try std.fmt.bufPrint(&pb, "{d:>5.1}%", .{h.percent});
    try t.writer.print("{s}{s}{s}   ", .{ Color.yellow, pstr, Color.reset });

    const max_sym_len: usize = t.width - 2 - tpad - tstr.len - 3 - pstr.len - 3 - 1;
    const sym_cols = try t.writeTruncated(Color.cyan, h.symbol, max_sym_len);
    const visible = tpad + tstr.len + 3 + pstr.len + 3 + sym_cols;
    try t.endRow(visible);
}

fn hotInsnRow(t: Table, h: HotInsn) !void {
    try t.startRow();
    var pb: [16]u8 = undefined;
    const pstr = try std.fmt.bufPrint(&pb, "{d:>5.1}%", .{h.percent});
    try t.writer.print("{s}{s}{s}   ", .{ Color.yellow, pstr, Color.reset });

    const max_text_len: usize = t.width - 2 - pstr.len - 3 - 1;
    const text_cols = try t.writeTruncated(Color.cyan, h.text, max_text_len);
    const visible = pstr.len + 3 + text_cols;
    try t.endRow(visible);
}

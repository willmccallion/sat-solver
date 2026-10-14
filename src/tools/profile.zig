const std = @import("std");
const Allocator = std.mem.Allocator;

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

const Color = struct {
    const reset = "\x1b[0m";
    const bold = "\x1b[1m";
    const dim = "\x1b[2m";
    const red = "\x1b[31m";
    const green = "\x1b[32m";
    const yellow = "\x1b[33m";
    const cyan = "\x1b[36m";
    const gray = "\x1b[90m";
};

const width: usize = 68;

const Stats = struct {
    // hardware counters (summed across cpu_core + cpu_atom on hybrid)
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

    // intel topdown L1 (percentages; summed across PMUs because only one is active)
    topdown_retiring: f64 = 0,
    topdown_bad_spec: f64 = 0,
    topdown_fe_bound: f64 = 0,
    topdown_be_bound: f64 = 0,

    // from sat-bench stdout
    elapsed_ns: u64 = 0,
    instance_count: u64 = 0,
    sat_count: u64 = 0,
    unsat_count: u64 = 0,
    unknown_count: u64 = 0,
    dist_min_ms: f64 = 0,
    dist_p50_ms: f64 = 0,
    dist_p90_ms: f64 = 0,
    dist_p99_ms: f64 = 0,
    dist_max_ms: f64 = 0,
    solver_decisions: u64 = 0,
    solver_conflicts: u64 = 0,
    solver_propagations: u64 = 0,
    solver_restarts: u64 = 0,
    solver_reductions: u64 = 0,
    solver_learned: u64 = 0,
    solver_rephases: u64 = 0,
    solver_chronos: u64 = 0,
    solver_probings: u64 = 0,
    solver_flp_units: u64 = 0,
    solver_vivifies: u64 = 0,
    solver_vivified: u64 = 0,
    solver_subsumes: u64 = 0,
    solver_subsumed: u64 = 0,
    solver_strengthened: u64 = 0,
    solver_mode_switches: u64 = 0,
    solver_compactions: u64 = 0,
    solver_bves: u64 = 0,
    solver_eliminated: u64 = 0,
    solver_resolvents_added: u64 = 0,
    peak_rss_kb: u64 = 0,
    par2_s: f64 = 0,
    timeout_s: u64 = 0,
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

    // --- perf stat pass (counters + TopdownL1) ---------------------------
    {
        var argv: std.ArrayList([]const u8) = .empty;
        defer argv.deinit(gpa);
        try argv.appendSlice(gpa, &.{
            "perf",             "stat",
            "-x",               ",",
            "-e",               events_list,
            "-M",               "TopdownL1",
            "--",               sat_bench,
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

        parseBenchOutput(result.stdout, &stats);
        parsePerfStat(result.stderr, &stats);
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

    // --- perf record pass ------------------------------------------------
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

    // --- perf report (hotspot extraction) --------------------------------
    {
        const result = try std.process.run(gpa, io, .{
            .argv = &.{
                "perf",            "report",
                "-i",              perf_data,
                "--stdio",
                "--no-children",
                "--percent-limit", "0.5",
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

    // --- perf annotate on top hot function -------------------------------
    if (hotspots.items.len > 0) {
        try stdout.print(
            "{s}[3/3] perf annotate `{s}`...{s}\n",
            .{ Color.dim, hotspots.items[0].symbol, Color.reset },
        );
        try stdout.flush();

        const result = try std.process.run(gpa, io, .{
            .argv = &.{
                "perf",      "annotate",
                "-i",        perf_data,
                "--stdio",
                "--no-source",
                "--percent-limit", "0.5",
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
    try printReport(stdout, dirs, &stats, hotspots.items, hot_insns.items);
}

// =======================================================================
// process + counter helpers
// =======================================================================

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

fn parseBenchOutput(output: []const u8, stats: *Stats) void {
    var it = std.mem.splitScalar(u8, output, '\n');
    while (it.next()) |raw_line| {
        const line = std.mem.trim(u8, raw_line, " \t\r");
        if (std.mem.startsWith(u8, line, "solved ")) {
            // Line shape: "solved N instances: X SAT, Y UNSAT, Z unknown"
            const rest = line["solved ".len..];
            const space = std.mem.indexOfScalar(u8, rest, ' ') orelse continue;
            stats.instance_count = std.fmt.parseInt(u64, rest[0..space], 10) catch 0;
            stats.sat_count = extractCountBefore(line, " SAT");
            stats.unsat_count = extractCountBefore(line, " UNSAT");
            stats.unknown_count = extractCountBefore(line, " unknown");
        } else if (std.mem.startsWith(u8, line, "total ")) {
            const rest = line["total ".len..];
            const space = std.mem.indexOfScalar(u8, rest, ' ') orelse continue;
            const ms = std.fmt.parseFloat(f64, rest[0..space]) catch continue;
            stats.elapsed_ns = @intFromFloat(ms * 1e6);
        } else if (std.mem.startsWith(u8, line, "dist_ms:")) {
            parseKeyValuePairs(line["dist_ms:".len..], struct {
                fn apply(dst: *Stats, key: []const u8, val: []const u8) void {
                    const f = std.fmt.parseFloat(f64, val) catch return;
                    if (std.mem.eql(u8, key, "min")) dst.dist_min_ms = f;
                    if (std.mem.eql(u8, key, "p50")) dst.dist_p50_ms = f;
                    if (std.mem.eql(u8, key, "p90")) dst.dist_p90_ms = f;
                    if (std.mem.eql(u8, key, "p99")) dst.dist_p99_ms = f;
                    if (std.mem.eql(u8, key, "max")) dst.dist_max_ms = f;
                }
            }.apply, stats);
        } else if (std.mem.startsWith(u8, line, "stats:")) {
            parseKeyValuePairs(line["stats:".len..], struct {
                fn apply(dst: *Stats, key: []const u8, val: []const u8) void {
                    const n = std.fmt.parseInt(u64, val, 10) catch return;
                    if (std.mem.eql(u8, key, "decisions")) dst.solver_decisions = n;
                    if (std.mem.eql(u8, key, "conflicts")) dst.solver_conflicts = n;
                    if (std.mem.eql(u8, key, "propagations")) dst.solver_propagations = n;
                    if (std.mem.eql(u8, key, "restarts")) dst.solver_restarts = n;
                    if (std.mem.eql(u8, key, "reductions")) dst.solver_reductions = n;
                    if (std.mem.eql(u8, key, "learned")) dst.solver_learned = n;
                    if (std.mem.eql(u8, key, "rephases")) dst.solver_rephases = n;
                    if (std.mem.eql(u8, key, "chronos")) dst.solver_chronos = n;
                    if (std.mem.eql(u8, key, "probings")) dst.solver_probings = n;
                    if (std.mem.eql(u8, key, "flp_units")) dst.solver_flp_units = n;
                    if (std.mem.eql(u8, key, "vivifies")) dst.solver_vivifies = n;
                    if (std.mem.eql(u8, key, "vivified")) dst.solver_vivified = n;
                    if (std.mem.eql(u8, key, "subsumes")) dst.solver_subsumes = n;
                    if (std.mem.eql(u8, key, "subsumed")) dst.solver_subsumed = n;
                    if (std.mem.eql(u8, key, "strengthened")) dst.solver_strengthened = n;
                    if (std.mem.eql(u8, key, "mode_switches")) dst.solver_mode_switches = n;
                    if (std.mem.eql(u8, key, "compactions")) dst.solver_compactions = n;
                    if (std.mem.eql(u8, key, "bves")) dst.solver_bves = n;
                    if (std.mem.eql(u8, key, "eliminated")) dst.solver_eliminated = n;
                    if (std.mem.eql(u8, key, "resolvents_added")) dst.solver_resolvents_added = n;
                }
            }.apply, stats);
        } else if (std.mem.startsWith(u8, line, "peak_rss_kb:")) {
            const rest = std.mem.trim(u8, line["peak_rss_kb:".len..], " \t");
            stats.peak_rss_kb = std.fmt.parseInt(u64, rest, 10) catch 0;
        } else if (std.mem.startsWith(u8, line, "par2_s:")) {
            const rest = std.mem.trim(u8, line["par2_s:".len..], " \t");
            stats.par2_s = std.fmt.parseFloat(f64, rest) catch 0;
        } else if (std.mem.startsWith(u8, line, "timeout_s:")) {
            const rest = std.mem.trim(u8, line["timeout_s:".len..], " \t");
            stats.timeout_s = std.fmt.parseInt(u64, rest, 10) catch 0;
        }
    }
}

// Pulls the integer immediately preceding `needle` in the line.
// Given "solved 400 instances: 237 SAT, 150 UNSAT, 13 unknown"
// and needle " SAT", returns 237. Used to avoid writing a regex
// for the three-token result tally.
fn extractCountBefore(line: []const u8, needle: []const u8) u64 {
    const idx = std.mem.indexOf(u8, line, needle) orelse return 0;
    var end = idx;
    while (end > 0 and (line[end - 1] == ' ' or line[end - 1] == '\t')) end -= 1;
    var start = end;
    while (start > 0 and std.ascii.isDigit(line[start - 1])) start -= 1;
    return std.fmt.parseInt(u64, line[start..end], 10) catch 0;
}

// Parses space-separated `key=value` pairs. Callback receives a pointer
// to Stats so it can mutate fields directly. Simple, no allocation.
fn parseKeyValuePairs(
    payload: []const u8,
    comptime apply: fn (dst: *Stats, key: []const u8, val: []const u8) void,
    stats: *Stats,
) void {
    var it = std.mem.tokenizeAny(u8, payload, " \t");
    while (it.next()) |token| {
        const eq = std.mem.indexOfScalar(u8, token, '=') orelse continue;
        apply(stats, token[0..eq], token[eq + 1 ..]);
    }
}

fn parsePerfStat(output: []const u8, stats: *Stats) void {
    // Hybrid Intel CPUs report the same events (and the same topdown
    // metric group) twice — once for cpu_core and once for cpu_atom.
    // Summing both inflates cycle counts and doubles the topdown
    // percentages. The kernel scheduler parks single-threaded compute
    // workloads on cpu_core almost exclusively, so we track the PMU
    // of the current line and only accept values from cpu_core. On
    // non-hybrid CPUs the event column has no cpu_* prefix and we
    // accept everything.
    var pmu_is_atom: bool = false;

    var it = std.mem.splitScalar(u8, output, '\n');
    while (it.next()) |raw_line| {
        const line = std.mem.trim(u8, raw_line, " \t\r");
        if (line.len == 0 or line[0] == '#') continue;

        var fields = std.mem.splitScalar(u8, line, ',');
        const value_str = fields.next() orelse continue;
        _ = fields.next() orelse continue; // unit
        const event_raw = fields.next() orelse continue;
        _ = fields.next() orelse continue; // runtime
        _ = fields.next() orelse continue; // pct
        const metric_value = fields.next() orelse "";
        const metric_unit = fields.next() orelse "";

        // If this row names an event, use it to update our PMU state.
        // Metric continuation rows (empty event column) inherit the
        // PMU of the most recent event row.
        if (event_raw.len > 0) {
            if (std.mem.startsWith(u8, event_raw, "cpu_atom/")) {
                pmu_is_atom = true;
            } else if (std.mem.startsWith(u8, event_raw, "cpu_core/")) {
                pmu_is_atom = false;
            }
            // No prefix → not a hybrid CPU; treat as accepted.
        }

        if (pmu_is_atom) continue;

        // Counter line: parse the numeric value column if present.
        if (value_str.len > 0 and value_str[0] != '<') {
            if (std.fmt.parseInt(u64, value_str, 10)) |value| {
                const event = stripEventName(event_raw);
                addCounter(stats, event, value);
            } else |_| {}
        }

        // Topdown metric line: metric_unit names the metric, metric_value
        // holds the percentage. These appear on topdown group rows —
        // sometimes the counter value is `<not counted>` because the
        // group uses shared slots.
        if (metric_unit.len > 0 and metric_value.len > 0) {
            const mu = std.mem.trim(u8, metric_unit, " \t");
            var name = mu;
            if (std.mem.startsWith(u8, name, "%")) name = name[1..];
            name = std.mem.trim(u8, name, " \t");
            const mv = std.fmt.parseFloat(f64, metric_value) catch continue;
            if (std.mem.eql(u8, name, "tma_retiring")) stats.topdown_retiring += mv //
            else if (std.mem.eql(u8, name, "tma_bad_speculation")) stats.topdown_bad_spec += mv //
            else if (std.mem.eql(u8, name, "tma_frontend_bound")) stats.topdown_fe_bound += mv //
            else if (std.mem.eql(u8, name, "tma_backend_bound")) stats.topdown_be_bound += mv;
        }
    }
}

fn addCounter(stats: *Stats, event: []const u8, value: u64) void {
    if (std.mem.eql(u8, event, "cycles")) stats.cycles += value //
    else if (std.mem.eql(u8, event, "instructions")) stats.instructions += value //
    else if (std.mem.eql(u8, event, "branches")) stats.branches += value //
    else if (std.mem.eql(u8, event, "branch-misses")) stats.branch_misses += value //
    else if (std.mem.eql(u8, event, "cache-references")) stats.cache_references += value //
    else if (std.mem.eql(u8, event, "cache-misses")) stats.cache_misses += value //
    else if (std.mem.eql(u8, event, "L1-dcache-loads")) stats.l1d_loads += value //
    else if (std.mem.eql(u8, event, "L1-dcache-load-misses")) stats.l1d_load_misses += value //
    else if (std.mem.eql(u8, event, "LLC-loads")) stats.llc_loads += value //
    else if (std.mem.eql(u8, event, "LLC-load-misses")) stats.llc_load_misses += value;
}

fn stripEventName(event_in: []const u8) []const u8 {
    var e = event_in;
    if (std.mem.startsWith(u8, e, "cpu_core/")) e = e["cpu_core/".len..];
    if (std.mem.startsWith(u8, e, "cpu_atom/")) e = e["cpu_atom/".len..];
    if (std.mem.endsWith(u8, e, "/u")) e = e[0 .. e.len - 2];
    if (std.mem.endsWith(u8, e, "/")) e = e[0 .. e.len - 1];
    if (std.mem.endsWith(u8, e, ":u")) e = e[0 .. e.len - 2];
    return e;
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
        if (hotspots.items.len >= 8) section_is_core = false;
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
        if (pct < 0.5) continue;

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

    // Keep only the top 8 by percent.
    std.mem.sort(HotInsn, hot_insns.items, {}, struct {
        fn lessThan(_: void, a: HotInsn, b: HotInsn) bool {
            return a.percent > b.percent;
        }
    }.lessThan);
    while (hot_insns.items.len > 8) {
        gpa.free(hot_insns.items[hot_insns.items.len - 1].text);
        _ = hot_insns.pop();
    }
}

// =======================================================================
// verdicts
// =======================================================================

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

// =======================================================================
// report printing
// =======================================================================

const box_tl = "╭";
const box_tr = "╮";
const box_bl = "╰";
const box_br = "╯";
const box_h = "─";
const box_v = "│";
const box_lt = "├";
const box_rt = "┤";

fn hrule(w: *std.Io.Writer, left: []const u8, right: []const u8) !void {
    try w.print("{s}{s}", .{ Color.gray, left });
    var i: usize = 0;
    while (i < width - 2) : (i += 1) try w.writeAll(box_h);
    try w.print("{s}{s}\n", .{ right, Color.reset });
}

fn startRow(w: *std.Io.Writer) !void {
    try w.print("{s}{s}{s}  ", .{ Color.gray, box_v, Color.reset });
}

fn endRow(w: *std.Io.Writer, visible_cols: usize) !void {
    var pad: usize = 0;
    if (2 + visible_cols < width - 1) pad = (width - 1) - (2 + visible_cols);
    var i: usize = 0;
    while (i < pad) : (i += 1) try w.writeAll(" ");
    try w.print("{s}{s}{s}\n", .{ Color.gray, box_v, Color.reset });
}

fn blankRow(w: *std.Io.Writer) !void {
    try startRow(w);
    try endRow(w, 0);
}

fn sectionHeader(w: *std.Io.Writer, text: []const u8) !void {
    try hrule(w, box_lt, box_rt);
    try blankRow(w);
    try startRow(w);
    try w.print("{s}{s}{s}", .{ Color.bold, text, Color.reset });
    try endRow(w, text.len);
    try blankRow(w);
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
    w: *std.Io.Writer,
    dirs: []const []const u8,
    stats: *const Stats,
    hotspots: []const Hotspot,
    hot_insns: []const HotInsn,
) !void {
    const cycles: f64 = @floatFromInt(stats.cycles);
    const insns: f64 = @floatFromInt(stats.instructions);
    const branches: f64 = @floatFromInt(stats.branches);
    const brmisses: f64 = @floatFromInt(stats.branch_misses);
    const l1d_loads: f64 = @floatFromInt(stats.l1d_loads);
    const l1d_miss: f64 = @floatFromInt(stats.l1d_load_misses);

    const ipc: f64 = if (cycles > 0) insns / cycles else 0;
    const br_pct: f64 = if (branches > 0) brmisses * 100.0 / branches else 0;
    const l1d_pct: f64 = if (l1d_loads > 0) l1d_miss * 100.0 / l1d_loads else 0;
    const l1d_mpki: f64 = if (insns > 0) l1d_miss * 1000.0 / insns else 0;

    const elapsed_ns_f: f64 = @floatFromInt(stats.elapsed_ns);
    const elapsed_ms = elapsed_ns_f / 1e6;
    const per_inst_ms: f64 = if (stats.instance_count > 0)
        elapsed_ms / @as(f64, @floatFromInt(stats.instance_count))
    else
        0;

    const effective_ghz: f64 = if (elapsed_ns_f > 0) cycles / elapsed_ns_f else 0;

    // --- top border + header
    try hrule(w, box_tl, box_tr);
    try startRow(w);
    try w.print("{s}{s}sat-bench perf baseline{s}", .{ Color.bold, Color.cyan, Color.reset });
    try endRow(w, "sat-bench perf baseline".len);
    try blankRow(w);

    for (dirs, 0..) |d, i| {
        try startRow(w);
        if (i == 0) try w.writeAll("workload   ") else try w.writeAll("           ");
        try w.print("{s}{s}{s}", .{ Color.cyan, d, Color.reset });
        try endRow(w, "workload   ".len + d.len);
    }

    {
        try startRow(w);
        try w.writeAll("instances  ");
        var nb: [32]u8 = undefined;
        const nstr = try std.fmt.bufPrint(&nb, "{d}", .{stats.instance_count});
        try w.print("{s}{s}{s}", .{ Color.cyan, nstr, Color.reset });
        try endRow(w, "instances  ".len + nstr.len);
    }
    {
        // solved N/M with a SAT/UNSAT breakdown — the first thing you
        // want to see when switching to a timed industrial bench where
        // not every instance finishes.
        try startRow(w);
        try w.writeAll("solved     ");
        var nb: [64]u8 = undefined;
        const solved = stats.sat_count + stats.unsat_count;
        const nstr = try std.fmt.bufPrint(
            &nb,
            "{d} / {d}",
            .{ solved, stats.instance_count },
        );
        const solved_color = if (stats.unknown_count == 0)
            Color.green
        else if (solved * 2 >= stats.instance_count)
            Color.yellow
        else
            Color.red;
        try w.print("{s}{s}{s}", .{ solved_color, nstr, Color.reset });
        var db: [64]u8 = undefined;
        const dstr = try std.fmt.bufPrint(
            &db,
            "  ({d} SAT, {d} UNSAT, {d} timeout)",
            .{ stats.sat_count, stats.unsat_count, stats.unknown_count },
        );
        try w.print("{s}{s}{s}", .{ Color.dim, dstr, Color.reset });
        try endRow(w, "solved     ".len + nstr.len + dstr.len);
    }
    {
        try startRow(w);
        try w.writeAll("wall time  ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.1} ms", .{elapsed_ms});
        try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        var pb: [32]u8 = undefined;
        const pstr = try std.fmt.bufPrint(&pb, "  ({d:.3} ms / instance)", .{per_inst_ms});
        try w.print("{s}{s}{s}", .{ Color.dim, pstr, Color.reset });
        try endRow(w, "wall time  ".len + vstr.len + pstr.len);
    }
    if (stats.timeout_s > 0) {
        // PAR-2 is the actual SAT Competition ranking metric: every
        // solved instance costs its wall time, every unsolved one costs
        // 2× the cap. Only meaningful when a per-instance cap was set.
        try startRow(w);
        try w.writeAll("PAR-2      ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.2} s", .{stats.par2_s});
        try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        var db: [32]u8 = undefined;
        const dstr = try std.fmt.bufPrint(&db, "  (cap {d} s/inst)", .{stats.timeout_s});
        try w.print("{s}{s}{s}", .{ Color.dim, dstr, Color.reset });
        try endRow(w, "PAR-2      ".len + vstr.len + dstr.len);
    }
    try blankRow(w);

    // --- per-instance distribution ---
    try sectionHeader(w, "per-instance distribution");
    try distRow(w, "min", stats.dist_min_ms);
    try distRow(w, "p50", stats.dist_p50_ms);
    try distRow(w, "p90", stats.dist_p90_ms);
    try distRow(w, "p99", stats.dist_p99_ms);
    try distRow(w, "max", stats.dist_max_ms);
    try blankRow(w);

    // --- CPU topdown ---
    if (hasTopdown(stats)) {
        try sectionHeader(w, "cpu (intel topdown L1)");
        try topdownRow(w, "retiring", stats.topdown_retiring, "doing useful work");
        try topdownRow(w, "bad-speculation", stats.topdown_bad_spec, "branch miss waste");
        try topdownRow(w, "frontend-bound", stats.topdown_fe_bound, "fetch/decode stall");
        try topdownRow(w, "backend-bound", stats.topdown_be_bound, "memory / execute stall");
        try blankRow(w);
    }

    // --- hardware metrics ---
    try sectionHeader(w, "hardware metrics");
    try metricRow(w, "IPC", "{d:.2}", .{ipc}, ipcVerdict(ipc), stats.instructions, stats.cycles);
    {
        try startRow(w);
        try w.writeAll("effective clock     ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.2} GHz", .{effective_ghz});
        try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try endRow(w, "effective clock     ".len + vstr.len);
    }
    try metricRow(w, "branch-miss rate", "{d:.1}%", .{br_pct}, brMissVerdict(br_pct), stats.branch_misses, stats.branches);
    try metricRow(w, "L1d miss rate", "{d:.2}%", .{l1d_pct}, l1dMissVerdict(l1d_pct), stats.l1d_load_misses, stats.l1d_loads);
    {
        try startRow(w);
        try w.writeAll("L1d MPKI            ");
        var vb: [32]u8 = undefined;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.1}", .{l1d_mpki});
        try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try w.print("{s}   misses per 1k instructions{s}", .{ Color.dim, Color.reset });
        try endRow(w, "L1d MPKI            ".len + vstr.len + "   misses per 1k instructions".len);
    }
    {
        try startRow(w);
        try w.writeAll("LLC absolute misses ");
        var vb: [32]u8 = undefined;
        const vstr = formatCount(&vb, stats.llc_load_misses);
        try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try endRow(w, "LLC absolute misses ".len + vstr.len);
    }
    {
        try startRow(w);
        try w.writeAll("peak RSS            ");
        var vb: [32]u8 = undefined;
        const mb = @as(f64, @floatFromInt(stats.peak_rss_kb)) / 1024.0;
        const vstr = try std.fmt.bufPrint(&vb, "{d:.1} MB", .{mb});
        try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
        try endRow(w, "peak RSS            ".len + vstr.len);
    }
    try blankRow(w);

    // --- solver activity ---
    try sectionHeader(w, "solver activity");
    try solverRow(w, "decisions", stats.solver_decisions, stats.instance_count);
    try solverRow(w, "conflicts", stats.solver_conflicts, stats.instance_count);
    try solverRow(w, "propagations", stats.solver_propagations, stats.instance_count);
    try solverRow(w, "restarts", stats.solver_restarts, stats.instance_count);
    try solverRow(w, "reductions", stats.solver_reductions, stats.instance_count);
    try solverRow(w, "learned clauses", stats.solver_learned, stats.instance_count);
    try solverRow(w, "rephases", stats.solver_rephases, stats.instance_count);
    try solverRow(w, "chrono backtracks", stats.solver_chronos, stats.instance_count);
    try solverRow(w, "probings", stats.solver_probings, stats.instance_count);
    try solverRow(w, "flp units", stats.solver_flp_units, stats.instance_count);
    try solverRow(w, "vivify passes", stats.solver_vivifies, stats.instance_count);
    try solverRow(w, "vivified clauses", stats.solver_vivified, stats.instance_count);
    try solverRow(w, "subsume passes", stats.solver_subsumes, stats.instance_count);
    try solverRow(w, "subsumed clauses", stats.solver_subsumed, stats.instance_count);
    try solverRow(w, "strengthened", stats.solver_strengthened, stats.instance_count);
    try solverRow(w, "mode switches", stats.solver_mode_switches, stats.instance_count);
    try solverRow(w, "compactions", stats.solver_compactions, stats.instance_count);
    try solverRow(w, "bve passes", stats.solver_bves, stats.instance_count);
    try solverRow(w, "eliminated", stats.solver_eliminated, stats.instance_count);
    try solverRow(w, "resolvents added", stats.solver_resolvents_added, stats.instance_count);
    try blankRow(w);

    // --- throughput ---
    try sectionHeader(w, "throughput (wall time / event)");
    try throughputRow(w, "per decision", elapsed_ns_f, stats.solver_decisions);
    try throughputRow(w, "per conflict", elapsed_ns_f, stats.solver_conflicts);
    try throughputRow(w, "per propagation", elapsed_ns_f, stats.solver_propagations);
    try blankRow(w);

    // --- hotspots (self time) ---
    try sectionHeader(w, "hotspots (self time)");
    if (hotspots.len == 0) {
        try startRow(w);
        try w.print("{s}(no samples — did perf record succeed?){s}", .{ Color.yellow, Color.reset });
        try endRow(w, "(no samples — did perf record succeed?)".len);
    } else {
        for (hotspots) |h| try hotspotRow(w, h, elapsed_ns_f);
    }
    try blankRow(w);

    // --- hot instructions inside top function ---
    if (hotspots.len > 0 and hot_insns.len > 0) {
        var title_buf: [128]u8 = undefined;
        const title = try std.fmt.bufPrint(&title_buf, "hot instructions in {s}", .{hotspots[0].symbol});
        try sectionHeader(w, title);
        for (hot_insns) |h| try hotInsnRow(w, h);
        try blankRow(w);
    }

    try hrule(w, box_bl, box_br);
}

fn hasTopdown(s: *const Stats) bool {
    const total = s.topdown_retiring + s.topdown_bad_spec +
        s.topdown_fe_bound + s.topdown_be_bound;
    return total > 0.5;
}

fn distRow(w: *std.Io.Writer, label: []const u8, ms: f64) !void {
    try startRow(w);
    try w.writeAll(label);
    try w.writeAll("  ");
    var vb: [32]u8 = undefined;
    const vstr = formatTime(&vb, ms * 1e6);
    try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
    try endRow(w, label.len + 2 + vstr.len);
}

fn topdownRow(w: *std.Io.Writer, label: []const u8, pct: f64, note: []const u8) !void {
    try startRow(w);
    try w.writeAll(label);
    var pad: usize = 0;
    if (label.len < 20) pad = 20 - label.len;
    var i: usize = 0;
    while (i < pad) : (i += 1) try w.writeAll(" ");
    var vb: [32]u8 = undefined;
    const vstr = try std.fmt.bufPrint(&vb, "{d:>5.1}%", .{pct});

    // Colorize based on which bucket: retiring green, others warning-yellow
    const col = if (std.mem.eql(u8, label, "retiring")) Color.green else Color.yellow;
    try w.print("{s}{s}{s}", .{ col, vstr, Color.reset });
    try w.print("   {s}{s}{s}", .{ Color.dim, note, Color.reset });
    try endRow(w, 20 + vstr.len + 3 + note.len);
}

fn metricRow(
    w: *std.Io.Writer,
    label: []const u8,
    comptime value_fmt: []const u8,
    value_args: anytype,
    v: Verdict,
    hits: u64,
    total: u64,
) !void {
    try startRow(w);
    try w.writeAll(label);
    var visible: usize = label.len;
    var pad: usize = 0;
    if (label.len < 20) pad = 20 - label.len;
    while (pad > 0) : (pad -= 1) {
        try w.writeAll(" ");
        visible += 1;
    }

    var vbuf: [64]u8 = undefined;
    const value_str = try std.fmt.bufPrint(&vbuf, value_fmt, value_args);
    try w.print("{s}{s}{s}", .{ Color.cyan, value_str, Color.reset });
    visible += value_str.len;

    pad = if (value_str.len < 10) 10 - value_str.len else 1;
    while (pad > 0) : (pad -= 1) {
        try w.writeAll(" ");
        visible += 1;
    }

    try w.print("{s}{s}{s}{s}", .{ verdictColor(v), Color.bold, verdictLabel(v), Color.reset });
    visible += verdictLabel(v).len;

    try w.writeAll("   ");
    visible += 3;

    var hbuf: [32]u8 = undefined;
    const hstr = formatCount(&hbuf, hits);
    var tbuf: [32]u8 = undefined;
    const tstr = formatCount(&tbuf, total);
    try w.print("{s}{s} / {s}{s}", .{ Color.dim, hstr, tstr, Color.reset });
    visible += hstr.len + 3 + tstr.len;

    try endRow(w, visible);
}

fn solverRow(w: *std.Io.Writer, label: []const u8, count: u64, instances: u64) !void {
    try startRow(w);
    try w.writeAll(label);
    var pad: usize = 0;
    if (label.len < 20) pad = 20 - label.len;
    var i: usize = 0;
    while (i < pad) : (i += 1) try w.writeAll(" ");

    var cbuf: [32]u8 = undefined;
    const cstr = formatCount(&cbuf, count);
    try w.print("{s}{s}{s}", .{ Color.cyan, cstr, Color.reset });

    var pad2: usize = if (cstr.len < 10) 10 - cstr.len else 1;
    while (pad2 > 0) : (pad2 -= 1) try w.writeAll(" ");

    var vis: usize = 20 + cstr.len;
    if (cstr.len < 10) vis += (10 - cstr.len) else vis += 1;

    if (instances > 0) {
        var ab: [32]u8 = undefined;
        const avg: f64 = @as(f64, @floatFromInt(count)) / @as(f64, @floatFromInt(instances));
        const avg_u: u64 = @intFromFloat(@round(avg));
        const astr = formatCount(&ab, avg_u);
        try w.print("{s}{s}{s} / instance", .{ Color.dim, astr, Color.reset });
        vis += astr.len + " / instance".len;
    }

    try endRow(w, vis);
}

fn throughputRow(w: *std.Io.Writer, label: []const u8, wall_ns: f64, events: u64) !void {
    try startRow(w);
    try w.writeAll(label);
    var pad: usize = 0;
    if (label.len < 20) pad = 20 - label.len;
    var i: usize = 0;
    while (i < pad) : (i += 1) try w.writeAll(" ");

    if (events == 0) {
        try w.print("{s}n/a{s}", .{ Color.dim, Color.reset });
        try endRow(w, 20 + 3);
        return;
    }
    const per: f64 = wall_ns / @as(f64, @floatFromInt(events));
    var vb: [32]u8 = undefined;
    const vstr = formatTime(&vb, per);
    try w.print("{s}{s}{s}", .{ Color.cyan, vstr, Color.reset });
    try endRow(w, 20 + vstr.len);
}

fn hotspotRow(w: *std.Io.Writer, h: Hotspot, wall_ns: f64) !void {
    try startRow(w);

    // Absolute time: percent × wall time.
    var tb: [32]u8 = undefined;
    const ns_in_func = (h.percent / 100.0) * wall_ns;
    const tstr = formatTime(&tb, ns_in_func);
    // Pad tstr to width 9 (right-aligned) for column alignment.
    const tpad: usize = if (tstr.len < 9) 9 - tstr.len else 0;
    var i: usize = 0;
    while (i < tpad) : (i += 1) try w.writeAll(" ");
    try w.print("{s}{s}{s}   ", .{ Color.cyan, tstr, Color.reset });

    var pb: [16]u8 = undefined;
    const pstr = try std.fmt.bufPrint(&pb, "{d:>5.1}%", .{h.percent});
    try w.print("{s}{s}{s}   ", .{ Color.yellow, pstr, Color.reset });

    const max_sym_len: usize = width - 2 - tpad - tstr.len - 3 - pstr.len - 3 - 1;
    var sym = h.symbol;
    var truncated = false;
    if (sym.len > max_sym_len) {
        sym = sym[0 .. max_sym_len - 1];
        truncated = true;
    }
    try w.print("{s}{s}{s}", .{ Color.cyan, sym, Color.reset });
    if (truncated) try w.writeAll("…");

    const visible = tpad + tstr.len + 3 + pstr.len + 3 + sym.len + @as(usize, if (truncated) 1 else 0);
    try endRow(w, visible);
}

fn hotInsnRow(w: *std.Io.Writer, h: HotInsn) !void {
    try startRow(w);
    var pb: [16]u8 = undefined;
    const pstr = try std.fmt.bufPrint(&pb, "{d:>5.1}%", .{h.percent});
    try w.print("{s}{s}{s}   ", .{ Color.yellow, pstr, Color.reset });

    const max_text_len: usize = width - 2 - pstr.len - 3 - 1;
    var text = h.text;
    var truncated = false;
    if (text.len > max_text_len) {
        text = text[0 .. max_text_len - 1];
        truncated = true;
    }
    try w.print("{s}{s}{s}", .{ Color.cyan, text, Color.reset });
    if (truncated) try w.writeAll("…");

    const visible = pstr.len + 3 + text.len + @as(usize, if (truncated) 1 else 0);
    try endRow(w, visible);
}

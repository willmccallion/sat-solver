const std = @import("std");
const Allocator = std.mem.Allocator;

// sat-profile — orchestrator for `zig build bench`. Runs the sat-bench
// binary under `perf stat` + `perf record`, parses the counter output,
// and prints a colored summary table.
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
    const blue = "\x1b[34m";
    const magenta = "\x1b[35m";
    const cyan = "\x1b[36m";
    const gray = "\x1b[90m";
};

const Stats = struct {
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
    elapsed_ns: u64 = 0,
    instance_count: u64 = 0,
};

const Hotspot = struct {
    percent: f64,
    symbol: []const u8,
};

const Verdict = enum { good, warn, bad };

pub fn main() !void {
    var debug_allocator: std.heap.DebugAllocator(.{}) = .init;
    defer _ = debug_allocator.deinit();
    const gpa = debug_allocator.allocator();

    var stdout_buffer: [8192]u8 = undefined;
    var stdout_writer = std.fs.File.stdout().writer(&stdout_buffer);
    const stdout = &stdout_writer.interface;
    defer stdout.flush() catch {};

    var stderr_buffer: [1024]u8 = undefined;
    var stderr_writer = std.fs.File.stderr().writer(&stderr_buffer);
    const stderr = &stderr_writer.interface;
    defer stderr.flush() catch {};

    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);

    if (args.len < 3) {
        try stderr.writeAll("usage: sat-profile <sat-bench-binary> <dir> [dir ...]\n");
        try stderr.flush();
        std.process.exit(1);
    }

    const sat_bench = args[1];
    const dirs = args[2..];

    if (!try perfAvailable(gpa)) {
        try stderr.writeAll(
            "error: `perf` not found. install it (`perf` or `linux-tools` package) and retry.\n",
        );
        try stderr.flush();
        std.process.exit(1);
    }

    try stdout.print("{s}[1/2] running perf stat...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();

    var stats: Stats = .{};

    // -------- perf stat pass --------
    {
        var argv: std.ArrayList([]const u8) = .empty;
        defer argv.deinit(gpa);
        try argv.appendSlice(gpa, &.{
            "perf", "stat",
            "-x",   ",",
            "-e",   events_list,
            "--",   sat_bench,
        });
        try argv.appendSlice(gpa, dirs);

        const result = try std.process.Child.run(.{
            .allocator = gpa,
            .argv = argv.items,
            .max_output_bytes = 1 << 20,
        });
        defer gpa.free(result.stdout);
        defer gpa.free(result.stderr);

        if (result.term != .Exited or result.term.Exited != 0) {
            try stderr.print("perf stat failed:\n{s}\n", .{result.stderr});
            try stderr.flush();
            std.process.exit(1);
        }

        parseBenchOutput(result.stdout, &stats);
        parsePerfStat(result.stderr, &stats);
    }

    try stdout.print("{s}[2/2] running perf record...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();

    // -------- perf record pass --------
    const perf_data = "bench/.cache/perf.data";
    try std.fs.cwd().makePath("bench/.cache");

    var hotspots: std.ArrayList(Hotspot) = .empty;
    defer {
        for (hotspots.items) |h| gpa.free(h.symbol);
        hotspots.deinit(gpa);
    }

    {
        var argv: std.ArrayList([]const u8) = .empty;
        defer argv.deinit(gpa);
        try argv.appendSlice(gpa, &.{
            "perf",          "record",
            "-F",            "999",
            "--call-graph",  "dwarf",
            "-o",            perf_data,
            "--quiet",
            "--",            sat_bench,
        });
        try argv.appendSlice(gpa, dirs);

        const result = try std.process.Child.run(.{
            .allocator = gpa,
            .argv = argv.items,
            .max_output_bytes = 1 << 20,
        });
        defer gpa.free(result.stdout);
        defer gpa.free(result.stderr);

        if (result.term != .Exited or result.term.Exited != 0) {
            try stderr.print("perf record failed:\n{s}\n", .{result.stderr});
            try stderr.flush();
            std.process.exit(1);
        }
    }

    // -------- perf report --------
    {
        const result = try std.process.Child.run(.{
            .allocator = gpa,
            .argv = &.{
                "perf",            "report",
                "-i",              perf_data,
                "--stdio",
                "--no-children",
                "--percent-limit", "0.5",
            },
            .max_output_bytes = 1 << 20,
        });
        defer gpa.free(result.stdout);
        defer gpa.free(result.stderr);

        if (result.term != .Exited or result.term.Exited != 0) {
            try stderr.print("perf report failed:\n{s}\n", .{result.stderr});
            try stderr.flush();
            std.process.exit(1);
        }

        try parsePerfReport(gpa, result.stdout, &hotspots);
    }

    try stdout.writeAll("\n");
    try printReport(stdout, dirs, &stats, hotspots.items);
}

fn perfAvailable(gpa: Allocator) !bool {
    const r = std.process.Child.run(.{
        .allocator = gpa,
        .argv = &.{ "perf", "--version" },
        .max_output_bytes = 1024,
    }) catch return false;
    defer gpa.free(r.stdout);
    defer gpa.free(r.stderr);
    return r.term == .Exited and r.term.Exited == 0;
}

fn parseBenchOutput(output: []const u8, stats: *Stats) void {
    // Looks for the two summary lines emitted by sat-bench:
    //   solved N instances: ...
    //   total X.Y ms (...)
    var it = std.mem.splitScalar(u8, output, '\n');
    while (it.next()) |raw_line| {
        const line = std.mem.trim(u8, raw_line, " \t\r");

        if (std.mem.startsWith(u8, line, "solved ")) {
            const rest = line["solved ".len..];
            const space = std.mem.indexOfScalar(u8, rest, ' ') orelse continue;
            stats.instance_count = std.fmt.parseInt(u64, rest[0..space], 10) catch 0;
        } else if (std.mem.startsWith(u8, line, "total ")) {
            const rest = line["total ".len..];
            const space = std.mem.indexOfScalar(u8, rest, ' ') orelse continue;
            const ms = std.fmt.parseFloat(f64, rest[0..space]) catch continue;
            stats.elapsed_ns = @intFromFloat(ms * 1e6);
        }
    }
}

fn parsePerfStat(output: []const u8, stats: *Stats) void {
    var it = std.mem.splitScalar(u8, output, '\n');
    while (it.next()) |raw_line| {
        const line = std.mem.trim(u8, raw_line, " \t\r");
        if (line.len == 0 or line[0] == '#') continue;

        var fields = std.mem.splitScalar(u8, line, ',');
        const value_str = fields.next() orelse continue;
        _ = fields.next() orelse continue; // unit
        const event_raw = fields.next() orelse continue;

        // Skip non-counted / unsupported counters from hybrid CPUs.
        if (value_str.len == 0 or value_str[0] == '<') continue;

        const value = std.fmt.parseInt(u64, value_str, 10) catch continue;
        const event = stripEventName(event_raw);

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
    // perf report's --stdio output emits multiple "Samples: N of event ..."
    // sections on hybrid CPUs (one per PMU). We read the cpu_core section if
    // we can find it; otherwise we fall back to the first section.
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
                section_is_core = true; // accept first section on non-hybrid
            }
            continue;
        }
        if (!section_is_core) continue;
        if (line.len == 0 or line[0] == '#') continue;

        const trimmed = std.mem.trimLeft(u8, line, " \t");
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

// --- report printing ---------------------------------------------------

const box_tl = "╭";
const box_tr = "╮";
const box_bl = "╰";
const box_br = "╯";
const box_h = "─";
const box_v = "│";
const box_lt = "├";
const box_rt = "┤";
const width = 64;

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
    // Pad out to width-2 total columns (the 2 leading cols plus content).
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
    if (n >= 1_000_000_000) {
        return std.fmt.bufPrint(buf, "{d:.2}B", .{nf / 1e9}) catch buf[0..0];
    } else if (n >= 1_000_000) {
        return std.fmt.bufPrint(buf, "{d:.2}M", .{nf / 1e6}) catch buf[0..0];
    } else if (n >= 1_000) {
        return std.fmt.bufPrint(buf, "{d:.2}K", .{nf / 1e3}) catch buf[0..0];
    } else {
        return std.fmt.bufPrint(buf, "{d}", .{n}) catch buf[0..0];
    }
}

fn printReport(
    w: *std.Io.Writer,
    dirs: []const []const u8,
    stats: *const Stats,
    hotspots: []const Hotspot,
) !void {
    const cycles: f64 = @floatFromInt(stats.cycles);
    const insns: f64 = @floatFromInt(stats.instructions);
    const branches: f64 = @floatFromInt(stats.branches);
    const brmisses: f64 = @floatFromInt(stats.branch_misses);
    const l1d_loads: f64 = @floatFromInt(stats.l1d_loads);
    const l1d_miss: f64 = @floatFromInt(stats.l1d_load_misses);
    const llc_loads: f64 = @floatFromInt(stats.llc_loads);
    const llc_miss: f64 = @floatFromInt(stats.llc_load_misses);

    const ipc: f64 = if (cycles > 0) insns / cycles else 0;
    const br_pct: f64 = if (branches > 0) brmisses * 100.0 / branches else 0;
    const l1d_pct: f64 = if (l1d_loads > 0) l1d_miss * 100.0 / l1d_loads else 0;
    const llc_pct: f64 = if (llc_loads > 0) llc_miss * 100.0 / llc_loads else 0;

    const elapsed_ms = @as(f64, @floatFromInt(stats.elapsed_ns)) / 1e6;
    const per_inst_ms: f64 = if (stats.instance_count > 0)
        elapsed_ms / @as(f64, @floatFromInt(stats.instance_count))
    else
        0;

    // Top
    try hrule(w, box_tl, box_tr);

    // Title row
    try startRow(w);
    const title = "sat-bench perf baseline";
    try w.print("{s}{s}{s}{s}", .{ Color.bold, Color.cyan, title, Color.reset });
    try endRow(w, title.len);

    try blankRow(w);

    // Workload rows
    for (dirs, 0..) |d, i| {
        try startRow(w);
        if (i == 0) {
            try w.writeAll("workload   ");
            try w.print("{s}{s}{s}", .{ Color.cyan, d, Color.reset });
            try endRow(w, "workload   ".len + d.len);
        } else {
            try w.writeAll("           ");
            try w.print("{s}{s}{s}", .{ Color.cyan, d, Color.reset });
            try endRow(w, "           ".len + d.len);
        }
    }

    // Instance count + wall time
    {
        var line_buf: [128]u8 = undefined;
        const body = try std.fmt.bufPrint(
            &line_buf,
            "instances  {d}",
            .{stats.instance_count},
        );
        try startRow(w);
        try w.writeAll("instances  ");
        var n_buf: [32]u8 = undefined;
        const n = try std.fmt.bufPrint(&n_buf, "{d}", .{stats.instance_count});
        try w.print("{s}{s}{s}", .{ Color.cyan, n, Color.reset });
        try endRow(w, body.len);
    }
    {
        var buf: [128]u8 = undefined;
        const visible = try std.fmt.bufPrint(
            &buf,
            "wall time  {d:.1} ms  ({d:.3} ms/instance)",
            .{ elapsed_ms, per_inst_ms },
        );
        try startRow(w);
        try w.writeAll("wall time  ");
        var vbuf: [64]u8 = undefined;
        const val = try std.fmt.bufPrint(&vbuf, "{d:.1} ms", .{elapsed_ms});
        try w.print("{s}{s}{s}", .{ Color.cyan, val, Color.reset });
        var pbuf: [64]u8 = undefined;
        const per = try std.fmt.bufPrint(&pbuf, "  ({d:.3} ms/instance)", .{per_inst_ms});
        try w.print("{s}{s}{s}", .{ Color.dim, per, Color.reset });
        try endRow(w, visible.len);
    }

    try blankRow(w);
    try hrule(w, box_lt, box_rt);
    try blankRow(w);

    // Metric header
    {
        try startRow(w);
        try w.print("{s}{s}{s}", .{ Color.bold, "metric               value          verdict    counts", Color.reset });
        try endRow(w, "metric               value          verdict    counts".len);
    }
    try blankRow(w);

    // IPC row
    try metricRow(w, "IPC", "{d:.2}", .{ipc}, ipcVerdict(ipc), stats.instructions, stats.cycles);
    // Branch-miss row
    try metricRow(w, "branch-misses", "{d:.1}%", .{br_pct}, brMissVerdict(br_pct), stats.branch_misses, stats.branches);
    // L1d miss row
    try metricRow(w, "L1d miss rate", "{d:.2}%", .{l1d_pct}, l1dMissVerdict(l1d_pct), stats.l1d_load_misses, stats.l1d_loads);
    // LLC miss row — counts are typically small; mark OK if absolute misses < 1M
    {
        const v: Verdict = if (stats.llc_load_misses < 1_000_000) .good else if (llc_pct < 50.0) .warn else .bad;
        try metricRow(w, "LLC miss rate", "{d:.1}%", .{llc_pct}, v, stats.llc_load_misses, stats.llc_loads);
    }

    try blankRow(w);
    try hrule(w, box_lt, box_rt);
    try blankRow(w);

    // Hotspots header
    {
        try startRow(w);
        try w.print("{s}{s}{s}", .{ Color.bold, "hotspots (self time)", Color.reset });
        try endRow(w, "hotspots (self time)".len);
    }
    try blankRow(w);

    if (hotspots.len == 0) {
        try startRow(w);
        try w.print("{s}(no samples — did perf record succeed?){s}", .{ Color.yellow, Color.reset });
        try endRow(w, "(no samples — did perf record succeed?)".len);
    } else {
        for (hotspots) |h| {
            try hotspotRow(w, h);
        }
    }

    try blankRow(w);
    try hrule(w, box_bl, box_br);
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
    // label (width 18)
    try w.writeAll(label);
    var visible: usize = label.len;
    var pad: usize = 0;
    if (label.len < 18) pad = 18 - label.len;
    while (pad > 0) : (pad -= 1) {
        try w.writeAll(" ");
        visible += 1;
    }

    // value (cyan)
    var vbuf: [64]u8 = undefined;
    const value_str = try std.fmt.bufPrint(&vbuf, value_fmt, value_args);
    try w.print("{s}{s}{s}", .{ Color.cyan, value_str, Color.reset });
    visible += value_str.len;

    // pad to 14
    pad = if (value_str.len < 14) 14 - value_str.len else 1;
    while (pad > 0) : (pad -= 1) {
        try w.writeAll(" ");
        visible += 1;
    }

    // verdict
    try w.print("{s}{s}{s}{s}", .{ verdictColor(v), Color.bold, verdictLabel(v), Color.reset });
    visible += verdictLabel(v).len;

    // pad to column for counts
    pad = 7;
    while (pad > 0) : (pad -= 1) {
        try w.writeAll(" ");
        visible += 1;
    }

    // counts: hits / total
    var hbuf: [32]u8 = undefined;
    const hstr = formatCount(&hbuf, hits);
    var tbuf: [32]u8 = undefined;
    const tstr = formatCount(&tbuf, total);
    try w.print("{s}{s} / {s}{s}", .{ Color.dim, hstr, tstr, Color.reset });
    visible += hstr.len + 3 + tstr.len;

    try endRow(w, visible);
}

fn hotspotRow(w: *std.Io.Writer, h: Hotspot) !void {
    try startRow(w);
    var pbuf: [16]u8 = undefined;
    const pstr = try std.fmt.bufPrint(&pbuf, "{d:>5.1}%", .{h.percent});
    try w.print("{s}{s}{s}  ", .{ Color.yellow, pstr, Color.reset });

    // Trim very long symbol names so they fit
    const max_sym_len: usize = width - 2 - pstr.len - 2 - 1;
    var sym = h.symbol;
    var truncated = false;
    if (sym.len > max_sym_len) {
        sym = sym[0 .. max_sym_len - 1];
        truncated = true;
    }
    try w.print("{s}{s}{s}", .{ Color.cyan, sym, Color.reset });
    if (truncated) try w.writeAll("…");

    const visible = pstr.len + 2 + sym.len + @as(usize, if (truncated) 1 else 0);
    try endRow(w, visible);
}

const std = @import("std");
const parser = @import("parser.zig");
const solver_mod = @import("solver.zig");

// sat-bench — batch runner designed to be the perf-record target for
// `zig build bench`. Iterates one or more directories of .cnf files in
// a single long-running process, tracks per-instance timings + peak
// RSS + aggregated solver stats, and emits a structured summary that
// sat-profile can parse into its report table.
//
// Summary format on stdout (sat-profile depends on these lines):
//
//   solved N instances: X SAT, Y UNSAT, Z unknown
//   total T.T ms (P.P ms/instance)
//   dist_ms: min=... p50=... p90=... p99=... max=...
//   stats: decisions=... conflicts=... propagations=... restarts=... reductions=... learned=...
//   peak_rss_kb: R

pub fn main() !void {
    const gpa = std.heap.smp_allocator;

    var stdout_buffer: [4096]u8 = undefined;
    var stdout_writer = std.fs.File.stdout().writer(&stdout_buffer);
    const stdout = &stdout_writer.interface;
    defer stdout.flush() catch {};

    var stderr_buffer: [1024]u8 = undefined;
    var stderr_writer = std.fs.File.stderr().writer(&stderr_buffer);
    const stderr = &stderr_writer.interface;
    defer stderr.flush() catch {};

    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);

    if (args.len < 2) {
        try stderr.writeAll("usage: sat-bench <dir-of-cnfs> [dir-of-cnfs ...]\n");
        try stderr.flush();
        std.process.exit(1);
    }

    var total: u32 = 0;
    var sat_count: u32 = 0;
    var unsat_count: u32 = 0;
    var unknown_count: u32 = 0;
    var agg_stats: solver_mod.Stats = .{};

    // Per-instance timings (ns) for distribution. Bounded memory:
    // a few tens of thousands of instances × 8 bytes is fine.
    var per_instance_ns: std.ArrayList(u64) = .empty;
    defer per_instance_ns.deinit(gpa);

    var timer = try std.time.Timer.start();

    for (args[1..]) |dir_path| {
        try runDirectory(
            gpa,
            dir_path,
            &total,
            &sat_count,
            &unsat_count,
            &unknown_count,
            &agg_stats,
            &per_instance_ns,
            stderr,
        );
    }

    const elapsed_ns = timer.read();
    const elapsed_ms = @as(f64, @floatFromInt(elapsed_ns)) / 1e6;
    const per_inst_ms: f64 = if (total > 0)
        elapsed_ms / @as(f64, @floatFromInt(total))
    else
        0;

    try stdout.print(
        "solved {d} instances: {d} SAT, {d} UNSAT, {d} unknown\n" ++
            "total {d:.1} ms ({d:.3} ms/instance)\n",
        .{ total, sat_count, unsat_count, unknown_count, elapsed_ms, per_inst_ms },
    );

    // Distribution: sort per-instance times, report min / p50 / p90 /
    // p99 / max. Cheap for thousands of instances.
    if (per_instance_ns.items.len > 0) {
        std.mem.sort(u64, per_instance_ns.items, {}, std.sort.asc(u64));
        const n = per_instance_ns.items.len;
        const min = per_instance_ns.items[0];
        const p50 = per_instance_ns.items[n / 2];
        const p90 = per_instance_ns.items[(n * 9) / 10];
        const p99 = per_instance_ns.items[(n * 99) / 100];
        const max = per_instance_ns.items[n - 1];
        try stdout.print(
            "dist_ms: min={d:.3} p50={d:.3} p90={d:.3} p99={d:.3} max={d:.3}\n",
            .{
                nsToMs(min),
                nsToMs(p50),
                nsToMs(p90),
                nsToMs(p99),
                nsToMs(max),
            },
        );
    }

    try stdout.print(
        "stats: decisions={d} conflicts={d} propagations={d} restarts={d} reductions={d} learned={d}\n",
        .{
            agg_stats.decisions,
            agg_stats.conflicts,
            agg_stats.propagations,
            agg_stats.restarts,
            agg_stats.reductions,
            agg_stats.learned,
        },
    );

    // Peak RSS from getrusage. On Linux ru_maxrss is in kilobytes.
    const ru = std.posix.getrusage(std.posix.rusage.SELF);
    try stdout.print("peak_rss_kb: {d}\n", .{ru.maxrss});
}

fn nsToMs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e6;
}

fn runDirectory(
    gpa: std.mem.Allocator,
    dir_path: []const u8,
    total: *u32,
    sat_count: *u32,
    unsat_count: *u32,
    unknown_count: *u32,
    agg_stats: *solver_mod.Stats,
    per_instance_ns: *std.ArrayList(u64),
    stderr: *std.Io.Writer,
) !void {
    var dir = std.fs.cwd().openDir(dir_path, .{ .iterate = true }) catch |err| {
        try stderr.print("sat-bench: cannot open {s}: {s}\n", .{ dir_path, @errorName(err) });
        try stderr.flush();
        std.process.exit(1);
    };
    defer dir.close();

    // Collect a sorted list of .cnf names so profiling runs are reproducible.
    var names: std.ArrayList([]u8) = .empty;
    defer {
        for (names.items) |n| gpa.free(n);
        names.deinit(gpa);
    }

    var it = dir.iterate();
    while (try it.next()) |entry| {
        if (entry.kind != .file) continue;
        if (!std.mem.endsWith(u8, entry.name, ".cnf")) continue;
        try names.append(gpa, try gpa.dupe(u8, entry.name));
    }

    std.mem.sort([]u8, names.items, {}, struct {
        fn lessThan(_: void, a: []u8, b: []u8) bool {
            return std.mem.lessThan(u8, a, b);
        }
    }.lessThan);

    for (names.items) |name| {
        const file = try dir.openFile(name, .{});
        defer file.close();

        const source = try file.readToEndAlloc(gpa, 1 << 30);
        defer gpa.free(source);

        const formula = try parser.parse(gpa, source);
        var solver = try solver_mod.Solver.init(gpa, formula);
        defer solver.deinit();

        var inst_timer = try std.time.Timer.start();
        const result = try solver.solve();
        const inst_ns = inst_timer.read();
        try per_instance_ns.append(gpa, inst_ns);

        accumulate(agg_stats, &solver.stats);

        total.* += 1;
        switch (result) {
            .sat => {
                if (!solver.verifyModel()) {
                    try stderr.print("sat-bench: BUG: model verification failed on {s}\n", .{name});
                    try stderr.flush();
                    std.process.exit(2);
                }
                sat_count.* += 1;
            },
            .unsat => unsat_count.* += 1,
            .unknown => unknown_count.* += 1,
        }
    }
}

fn accumulate(dst: *solver_mod.Stats, src: *const solver_mod.Stats) void {
    dst.decisions += src.decisions;
    dst.propagations += src.propagations;
    dst.conflicts += src.conflicts;
    dst.restarts += src.restarts;
    dst.learned += src.learned;
    dst.reductions += src.reductions;
    dst.deleted += src.deleted;
}

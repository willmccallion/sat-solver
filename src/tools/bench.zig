const std = @import("std");
const search = @import("search");
const parser = @import("io").parser;
const solver_mod = search.solver;

// sat-bench — batch runner designed to be the perf-record target for
// `zig build bench`. Iterates one or more directories of .cnf files in
// a single long-running process, tracks per-instance timings + peak
// RSS + aggregated solver stats, and emits a structured summary that
// sat-profile can parse into its report table.
//
// Flags:
//   --timeout-sec N   Per-instance wall-clock cap. A watchdog thread
//                     flips solver_mod.interrupted after N seconds and
//                     the instance is scored as .unknown. Default 0 =
//                     no cap (legacy behaviour for uf200/uuf200 bench).
//
// Summary format on stdout (sat-profile depends on these lines):
//
//   solved N instances: X SAT, Y UNSAT, Z unknown
//   total T.T ms (P.P ms/instance)
//   dist_ms: min=... p50=... p90=... p99=... max=...
//   stats: decisions=... conflicts=... propagations=... restarts=... reductions=... learned=...
//   peak_rss_kb: R
//   par2_s: P.PPP          (competition-style penalty: solved→t, unsolved→2T)
//   timeout_s: T           (0 if no per-instance cap was applied)

const WatchdogCtx = struct {
    io: std.Io,
    deadline: std.Io.Clock.Timestamp,
    finished: *std.Io.Event,
    interrupted: *std.atomic.Value(bool),
};

// Flips the interrupt only once the deadline has really passed: waitTimeout
// also returns error.Timeout on spurious wakeups.
fn watchdogFn(ctx: WatchdogCtx) void {
    while (!ctx.finished.isSet()) {
        ctx.finished.waitTimeout(ctx.io, .{ .deadline = ctx.deadline }) catch {};
        if (ctx.deadline.durationFromNow(ctx.io).raw.nanoseconds <= 0) {
            if (!ctx.finished.isSet()) ctx.interrupted.store(true, .monotonic);
            return;
        }
    }
}

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;

    var stdout_buffer: [4096]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writer(io, &stdout_buffer);
    const stdout = &stdout_writer.interface;
    defer stdout.flush() catch {};

    var stderr_buffer: [1024]u8 = undefined;
    var stderr_writer = std.Io.File.stderr().writer(io, &stderr_buffer);
    const stderr = &stderr_writer.interface;
    defer stderr.flush() catch {};

    const args = try init.minimal.args.toSlice(init.arena.allocator());

    var timeout_sec: u32 = 0;
    var dirs: std.ArrayList([]const u8) = .empty;
    defer dirs.deinit(gpa);

    var i: usize = 1;
    while (i < args.len) : (i += 1) {
        const a = args[i];
        if (std.mem.eql(u8, a, "--timeout-sec")) {
            i += 1;
            if (i >= args.len) {
                try stderr.writeAll("sat-bench: --timeout-sec requires a value\n");
                try stderr.flush();
                std.process.exit(1);
            }
            timeout_sec = std.fmt.parseInt(u32, args[i], 10) catch {
                try stderr.print("sat-bench: invalid --timeout-sec value `{s}`\n", .{args[i]});
                try stderr.flush();
                std.process.exit(1);
            };
        } else {
            try dirs.append(gpa, a);
        }
    }

    if (dirs.items.len == 0) {
        try stderr.writeAll(
            "usage: sat-bench [--timeout-sec N] <dir-of-cnfs> [dir-of-cnfs ...]\n",
        );
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

    // PAR-2 accumulator in ns. Solved instance contributes its solve
    // time; unsolved contributes 2 × timeout. Matches SAT Competition
    // scoring exactly. Collapses to raw wall time when timeout_sec=0.
    // u64 holds ≈ 584 years of ns, comfortably beyond any realistic
    // (instances × timeout) product.
    var par2_ns: u64 = 0;
    const timeout_ns: u64 = @as(u64, timeout_sec) * std.time.ns_per_s;

    const start = std.Io.Clock.Timestamp.now(io, .awake);

    for (dirs.items) |dir_path| {
        try runDirectory(
            gpa,
            io,
            dir_path,
            timeout_ns,
            &total,
            &sat_count,
            &unsat_count,
            &unknown_count,
            &agg_stats,
            &per_instance_ns,
            &par2_ns,
            stderr,
        );
    }

    const elapsed_ms = @as(f64, @floatFromInt(start.untilNow(io).raw.nanoseconds)) / 1e6;
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
        "stats: decisions={d} conflicts={d} propagations={d} restarts={d} reductions={d} learned={d} rephases={d} chronos={d} probings={d} flp_units={d} vivifies={d} vivified={d} subsumes={d} subsumed={d} strengthened={d} mode_switches={d} compactions={d} bves={d} eliminated={d} resolvents_added={d}\n",
        .{
            agg_stats.decisions,
            agg_stats.conflicts,
            agg_stats.propagations,
            agg_stats.restarts,
            agg_stats.reductions,
            agg_stats.learned,
            agg_stats.rephases,
            agg_stats.chronos,
            agg_stats.probings,
            agg_stats.flp_units,
            agg_stats.vivifies,
            agg_stats.vivified,
            agg_stats.subsumes,
            agg_stats.subsumed,
            agg_stats.strengthened,
            agg_stats.mode_switches,
            agg_stats.compactions,
            agg_stats.bves,
            agg_stats.eliminated,
            agg_stats.resolvents_added,
        },
    );

    // Peak RSS from getrusage. On Linux ru_maxrss is in kilobytes.
    const ru = std.posix.getrusage(std.posix.rusage.SELF);
    try stdout.print("peak_rss_kb: {d}\n", .{ru.maxrss});

    const par2_s: f64 = @as(f64, @floatFromInt(par2_ns)) / 1e9;
    try stdout.print("par2_s: {d:.3}\n", .{par2_s});
    try stdout.print("timeout_s: {d}\n", .{timeout_sec});
}

fn nsToMs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e6;
}

fn runDirectory(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir_path: []const u8,
    timeout_ns: u64,
    total: *u32,
    sat_count: *u32,
    unsat_count: *u32,
    unknown_count: *u32,
    agg_stats: *solver_mod.Stats,
    per_instance_ns: *std.ArrayList(u64),
    par2_ns: *u64,
    stderr: *std.Io.Writer,
) !void {
    var dir = std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true }) catch |err| {
        try stderr.print("sat-bench: cannot open {s}: {s}\n", .{ dir_path, @errorName(err) });
        try stderr.flush();
        std.process.exit(1);
    };
    defer dir.close(io);

    // Collect a sorted list of .cnf names so profiling runs are reproducible.
    var names: std.ArrayList([]u8) = .empty;
    defer {
        for (names.items) |n| gpa.free(n);
        names.deinit(gpa);
    }

    var it = dir.iterate();
    while (try it.next(io)) |entry| {
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
        const file = try dir.openFile(io, name, .{});
        defer file.close(io);

        var file_buffer: [64 * 1024]u8 = undefined;
        var file_reader = file.reader(io, &file_buffer);
        const source = try file_reader.interface.allocRemaining(gpa, .unlimited);
        defer gpa.free(source);

        const formula = try parser.parse(gpa, source);
        var solver = try solver_mod.Solver.init(gpa, formula);
        defer solver.deinit();

        // Per-instance: reset the global interrupt flag, arm a watchdog
        // if we have a timeout. The watchdog holds a ResetEvent we flip
        // the moment solve() returns, so short instances don't pay the
        // full timeout waiting on a detached thread.
        solver_mod.interrupted.store(false, .monotonic);
        var finished: std.Io.Event = .unset;
        const wd_thread: ?std.Thread = if (timeout_ns > 0)
            try std.Thread.spawn(.{}, watchdogFn, .{WatchdogCtx{
                .io = io,
                .deadline = .fromNow(io, .{ .raw = .fromNanoseconds(timeout_ns), .clock = .awake }),
                .finished = &finished,
                .interrupted = &solver_mod.interrupted,
            }})
        else
            null;

        const inst_start = std.Io.Clock.Timestamp.now(io, .awake);
        const result = try solver.solve();
        const inst_ns: u64 = @intCast(inst_start.untilNow(io).raw.nanoseconds);

        // Signal and join before touching shared state for the next
        // instance, so a late-waking watchdog can never set
        // `interrupted` across the instance boundary.
        finished.set(io);
        if (wd_thread) |t| t.join();

        try per_instance_ns.append(gpa, inst_ns);

        accumulate(agg_stats, &solver.stats);

        total.* += 1;
        switch (result) {
            .sat => {
                solver.reconstructEliminatedVars();
                if (!solver.verifyModel()) {
                    try stderr.print("sat-bench: BUG: model verification failed on {s}\n", .{name});
                    try stderr.flush();
                    std.process.exit(2);
                }
                sat_count.* += 1;
                par2_ns.* += inst_ns;
            },
            .unsat => {
                unsat_count.* += 1;
                par2_ns.* += inst_ns;
            },
            .unknown => {
                unknown_count.* += 1;
                // PAR-2 penalty: unsolved costs 2× the timeout. If no
                // timeout was set, charge the wall time we already spent.
                par2_ns.* += if (timeout_ns > 0) 2 * timeout_ns else inst_ns;
            },
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
    dst.rephases += src.rephases;
    dst.chronos += src.chronos;
    dst.probings += src.probings;
    dst.flp_units += src.flp_units;
    dst.vivifies += src.vivifies;
    dst.vivified += src.vivified;
    dst.subsumes += src.subsumes;
    dst.subsumed += src.subsumed;
    dst.strengthened += src.strengthened;
    dst.mode_switches += src.mode_switches;
    dst.compactions += src.compactions;
    dst.bves += src.bves;
    dst.eliminated += src.eliminated;
    dst.resolvents_added += src.resolvents_added;
}

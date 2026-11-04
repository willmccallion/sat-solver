const std = @import("std");
const CnfNames = @import("instances.zig").CnfNames;
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
//                     interrupts the solver after N seconds and
//                     the instance is scored as .unknown. Default 0 =
//                     no cap.
//
// Summary format on stdout (sat-profile depends on these lines):
//
//   solved N instances: X SAT, Y UNSAT, Z unknown
//   total T.T ms (P.P ms/instance)
//   dist_ms: min=... p50=... p90=... p99=... max=...
//   stats: name=value for every field of search.Stats, in declaration order
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

const Options = struct {
    timeout_sec: u32,
    dirs: []const []const u8,
};

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

    const arena = init.arena.allocator();
    const options = try parseArgs(arena, try init.minimal.args.toSlice(arena), stderr);
    const timeout_ns: u64 = @as(u64, options.timeout_sec) * std.time.ns_per_s;

    var tally: Tally = .{};
    defer tally.per_instance_ns.deinit(gpa);
    const start = std.Io.Clock.Timestamp.now(io, .awake);
    for (options.dirs) |dir_path| try runDirectory(gpa, io, dir_path, timeout_ns, &tally, stderr);
    const elapsed_ms = @as(f64, @floatFromInt(start.untilNow(io).raw.nanoseconds)) / 1e6;
    try tally.printSummary(stdout, elapsed_ms, options.timeout_sec);
}

// Prints the message and exits; with stderr failing too there is nowhere
// left to report that.
fn fatal(stderr: *std.Io.Writer, comptime fmt: []const u8, args: anytype, exit_code: u8) noreturn {
    stderr.print(fmt, args) catch {};
    stderr.flush() catch {};
    std.process.exit(exit_code);
}

fn parseArgs(arena: std.mem.Allocator, args: []const []const u8, stderr: *std.Io.Writer) !Options {
    var timeout_sec: u32 = 0;
    var dirs: std.ArrayList([]const u8) = .empty;
    var i: usize = 1;
    while (i < args.len) : (i += 1) {
        const arg = args[i];
        if (!std.mem.eql(u8, arg, "--timeout-sec")) {
            try dirs.append(arena, arg);
            continue;
        }
        i += 1;
        if (i >= args.len) fatal(stderr, "sat-bench: --timeout-sec requires a value\n", .{}, 1);
        timeout_sec = std.fmt.parseInt(u32, args[i], 10) catch
            fatal(stderr, "sat-bench: invalid --timeout-sec value `{s}`\n", .{args[i]}, 1);
    }
    if (dirs.items.len == 0) fatal(stderr, "usage: sat-bench [--timeout-sec N] <dir-of-cnfs> [dir-of-cnfs ...]\n", .{}, 1);
    return .{ .timeout_sec = timeout_sec, .dirs = dirs.items };
}

// What every instance solved so far adds up to.
const Tally = struct {
    total: u32 = 0,
    sat_count: u32 = 0,
    unsat_count: u32 = 0,
    unknown_count: u32 = 0,
    stats: solver_mod.Stats = .{},
    per_instance_ns: std.ArrayList(u64) = .empty,
    // PAR-2, as SAT Competition scores it: a solved instance costs its
    // solve time and an unsolved one twice the timeout, or with no timeout
    // the time it ran. A u64 of nanoseconds overflows only after 584 years.
    par2_ns: u64 = 0,

    fn record(self: *Tally, gpa: std.mem.Allocator, result: solver_mod.Result, stats: *const solver_mod.Stats, ns: u64, timeout_ns: u64) !void {
        try self.per_instance_ns.append(gpa, ns);
        inline for (comptime std.meta.fieldNames(solver_mod.Stats)) |name| {
            @field(self.stats, name) += @field(stats, name);
        }
        self.total += 1;
        switch (result) {
            .sat => self.sat_count += 1,
            .unsat => self.unsat_count += 1,
            .unknown => self.unknown_count += 1,
        }
        self.par2_ns += if (result == .unknown and timeout_ns > 0) 2 * timeout_ns else ns;
    }

    fn printSummary(self: *Tally, out: *std.Io.Writer, elapsed_ms: f64, timeout_sec: u32) !void {
        const per_inst_ms: f64 = if (self.total > 0) elapsed_ms / @as(f64, @floatFromInt(self.total)) else 0;
        try out.print(
            "solved {d} instances: {d} SAT, {d} UNSAT, {d} unknown\n" ++
                "total {d:.1} ms ({d:.3} ms/instance)\n",
            .{ self.total, self.sat_count, self.unsat_count, self.unknown_count, elapsed_ms, per_inst_ms },
        );
        try self.printDistribution(out);

        try out.writeAll("stats:");
        inline for (comptime std.meta.fieldNames(solver_mod.Stats)) |name| {
            try out.print(" {s}={d}", .{ name, @field(self.stats, name) });
        }
        try out.writeAll("\n");

        // On Linux ru_maxrss is in kilobytes.
        const ru = std.posix.getrusage(std.posix.rusage.SELF);
        try out.print("peak_rss_kb: {d}\n", .{ru.maxrss});
        try out.print("par2_s: {d:.3}\n", .{@as(f64, @floatFromInt(self.par2_ns)) / 1e9});
        try out.print("timeout_s: {d}\n", .{timeout_sec});
    }

    fn printDistribution(self: *Tally, out: *std.Io.Writer) !void {
        const times = self.per_instance_ns.items;
        if (times.len == 0) return;
        std.mem.sort(u64, times, {}, std.sort.asc(u64));
        const n = times.len;
        try out.print(
            "dist_ms: min={d:.3} p50={d:.3} p90={d:.3} p99={d:.3} max={d:.3}\n",
            .{ nsToMs(times[0]), nsToMs(times[n / 2]), nsToMs(times[(n * 9) / 10]), nsToMs(times[(n * 99) / 100]), nsToMs(times[n - 1]) },
        );
    }
};

fn nsToMs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e6;
}

fn runDirectory(gpa: std.mem.Allocator, io: std.Io, dir_path: []const u8, timeout_ns: u64, tally: *Tally, stderr: *std.Io.Writer) !void {
    var dir = std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true }) catch |err|
        fatal(stderr, "sat-bench: cannot open {s}: {s}\n", .{ dir_path, @errorName(err) }, 1);
    defer dir.close(io);
    const names = try CnfNames.list(gpa, io, dir);
    defer names.deinit(gpa);
    for (names.items) |name| try solveInstance(gpa, io, dir, name, timeout_ns, tally, stderr);
}

fn solveInstance(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir: std.Io.Dir,
    name: []const u8,
    timeout_ns: u64,
    tally: *Tally,
    stderr: *std.Io.Writer,
) !void {
    const file = try dir.openFile(io, name, .{});
    defer file.close(io);
    var file_buffer: [64 * 1024]u8 = undefined;
    var file_reader = file.readerStreaming(io, &file_buffer);
    var formula = try parser.parse(gpa, &file_reader.interface);
    defer formula.deinit();

    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    const start = std.Io.Clock.Timestamp.now(io, .awake);
    const result = try solveWithin(io, &solver, timeout_ns);
    const ns: u64 = @intCast(start.untilNow(io).raw.nanoseconds);

    if (result == .sat) {
        solver.extendModel();
        if (solver.findFalsifiedClause(&formula)) |index| {
            fatal(stderr, "sat-bench: BUG: model falsifies clause {d} of {s}\n", .{ index + 1, name }, 2);
        }
    }
    try tally.record(gpa, result, &solver.stats, ns, timeout_ns);
}

// Solves with a watchdog that interrupts the solver after `timeout_ns`, if
// set. The watchdog waits on an event set when solve returns, so a short
// instance does not wait out the whole timeout.
fn solveWithin(io: std.Io, solver: *solver_mod.Solver, timeout_ns: u64) !solver_mod.Result {
    var interrupted: std.atomic.Value(bool) = .init(false);
    solver.interrupt = &interrupted;
    var finished: std.Io.Event = .unset;
    const watchdog: ?std.Thread = if (timeout_ns > 0)
        try std.Thread.spawn(.{}, watchdogFn, .{WatchdogCtx{
            .io = io,
            .deadline = .fromNow(io, .{ .raw = .fromNanoseconds(timeout_ns), .clock = .awake }),
            .finished = &finished,
            .interrupted = &interrupted,
        }})
    else
        null;
    const result = solver.solve();
    // Joined before `interrupted` goes out of scope.
    finished.set(io);
    if (watchdog) |thread| thread.join();
    return result;
}

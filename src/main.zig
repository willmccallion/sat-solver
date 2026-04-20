const std = @import("std");
const core = @import("core");
const io = @import("io");
const search = @import("search");
const parser = io.parser;
const cnf = core.cnf;
const solver_mod = search.solver;
const flate = std.compress.flate;

const usage =
    \\usage: sat [options] [path/to/file.cnf[.gz]]
    \\
    \\Options:
    \\  --proof PATH         write DRAT proof to PATH (for UNSAT verification)
    \\  --time-limit SECS    abort with `s UNKNOWN` after SECS wall-clock seconds
    \\  -h, --help           show this message and exit
    \\
    \\Reads a DIMACS CNF formula from the given path, or from stdin when no
    \\path is provided. Files ending in `.gz` are decompressed transparently.
    \\Output follows the SAT Competition format on stdout (comment lines begin
    \\with `c`, status line is `s SATISFIABLE` / `s UNSATISFIABLE` / `s UNKNOWN`,
    \\and models are `v`-prefixed lists terminated by 0). Exit code encodes
    \\the result: 10 = SAT, 20 = UNSAT, 0 = UNKNOWN.
    \\
    \\The solver also responds to SIGINT, SIGTERM, and SIGXCPU by returning
    \\`s UNKNOWN` cleanly — this is what SAT Competition infrastructure uses
    \\to enforce its 5000-second per-instance time limit.
    \\
;

fn signalHandler(_: i32) callconv(.c) void {
    solver_mod.interrupted.store(true, .monotonic);
}

fn timeoutThreadFn(seconds: u32) void {
    std.Thread.sleep(@as(u64, seconds) * std.time.ns_per_s);
    solver_mod.interrupted.store(true, .monotonic);
}

pub fn main() !u8 {
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

    var input_path: ?[]const u8 = null;
    var proof_path: ?[]const u8 = null;
    var time_limit: ?u32 = null;

    var i: usize = 1;
    while (i < args.len) : (i += 1) {
        const a = args[i];
        if (std.mem.eql(u8, a, "-h") or std.mem.eql(u8, a, "--help")) {
            try stdout.writeAll(usage);
            return 0;
        } else if (std.mem.eql(u8, a, "--proof")) {
            i += 1;
            if (i >= args.len) {
                try stderr.writeAll("sat: --proof requires a PATH argument\n");
                try stderr.flush();
                std.process.exit(1);
            }
            proof_path = args[i];
        } else if (std.mem.eql(u8, a, "--time-limit")) {
            i += 1;
            if (i >= args.len) {
                try stderr.writeAll("sat: --time-limit requires a SECS argument\n");
                try stderr.flush();
                std.process.exit(1);
            }
            time_limit = std.fmt.parseInt(u32, args[i], 10) catch {
                try stderr.print("sat: --time-limit: invalid integer `{s}`\n", .{args[i]});
                try stderr.flush();
                std.process.exit(1);
            };
        } else if (a.len > 0 and a[0] == '-') {
            try stderr.print("sat: unknown option `{s}`\n", .{a});
            try stderr.writeAll(usage);
            try stderr.flush();
            return 1;
        } else {
            if (input_path != null) {
                try stderr.writeAll("sat: only one input path allowed\n");
                try stderr.flush();
                std.process.exit(1);
            }
            input_path = a;
        }
    }

    // Route SIGINT / SIGTERM / SIGXCPU into the solver's interrupt flag.
    // Competition infrastructure sends SIGTERM or SIGXCPU to enforce its
    // per-instance timeout; SIGINT is the ctrl-c escape hatch during
    // local testing. On any of these, the solver returns .unknown at the
    // next conflict and main falls through to the `s UNKNOWN` path.
    {
        const act: std.posix.Sigaction = .{
            .handler = .{ .handler = signalHandler },
            .mask = std.posix.sigemptyset(),
            .flags = 0,
        };
        std.posix.sigaction(std.posix.SIG.INT, &act, null);
        std.posix.sigaction(std.posix.SIG.TERM, &act, null);
        std.posix.sigaction(std.posix.SIG.XCPU, &act, null);
    }

    // --time-limit uses a detached thread rather than setitimer so we
    // don't have to wrestle with libc's itimerval vs. the kernel's
    // itimerspec. A single sleep + atomic store is plenty precise for
    // multi-second timeouts, and the thread gets reaped at exit.
    if (time_limit) |secs| {
        const t = try std.Thread.spawn(.{}, timeoutThreadFn, .{secs});
        t.detach();
    }

    const source = blk: {
        if (input_path) |p| {
            break :blk readInputFile(gpa, p) catch |err| {
                try stderr.print("sat: cannot read {s}: {s}\n", .{ p, @errorName(err) });
                return 1;
            };
        } else {
            break :blk readStdin(gpa) catch |err| {
                try stderr.print("sat: cannot read stdin: {s}\n", .{@errorName(err)});
                return 1;
            };
        }
    };
    defer gpa.free(source);

    const formula = parser.parse(gpa, source) catch |err| {
        try stdout.print("c parse error: {s}\n", .{@errorName(err)});
        try stdout.writeAll("s UNKNOWN\n");
        return 0;
    };

    // Open the DRAT proof file if requested. The file handle + writer
    // state live in this scope so the `defer` flush + close both fire
    // before process exit. We only wire the writer into the solver if
    // we successfully created it.
    var proof_file: ?std.fs.File = null;
    defer if (proof_file) |f| f.close();
    var proof_file_writer: std.fs.File.Writer = undefined;
    var proof_buffer: [8192]u8 = undefined;
    var proof_interface: ?*std.Io.Writer = null;
    defer if (proof_interface) |w| w.flush() catch {};

    if (proof_path) |pp| {
        proof_file = std.fs.cwd().createFile(pp, .{}) catch |err| {
            try stderr.print("sat: cannot create proof file {s}: {s}\n", .{ pp, @errorName(err) });
            return 1;
        };
        proof_file_writer = proof_file.?.writer(&proof_buffer);
        proof_interface = &proof_file_writer.interface;
    }

    var solver = try solver_mod.Solver.init(gpa, formula);
    defer solver.deinit();

    if (proof_interface) |w| solver.setProofWriter(w);

    const result = try solver.solve();
    switch (result) {
        .sat => {
            if (!solver.verifyModel()) {
                try stdout.writeAll("c BUG: model verification failed\n");
                try stdout.writeAll("s UNKNOWN\n");
                return 0;
            }
            try stdout.writeAll("s SATISFIABLE\n");
            try writeModel(stdout, &solver);
            return 10;
        },
        .unsat => {
            try stdout.writeAll("s UNSATISFIABLE\n");
            return 20;
        },
        .unknown => {
            try stdout.writeAll("s UNKNOWN\n");
            return 0;
        },
    }
}

// Read an input CNF, transparently decompressing .gz files.
fn readInputFile(gpa: std.mem.Allocator, path: []const u8) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    if (std.mem.endsWith(u8, path, ".gz")) {
        var file_buf: [4096]u8 = undefined;
        var file_reader = file.reader(&file_buf);

        var decomp_buf: [flate.max_window_len]u8 = undefined;
        var decomp = flate.Decompress.init(
            &file_reader.interface,
            .gzip,
            &decomp_buf,
        );
        return decomp.reader.allocRemaining(gpa, .unlimited);
    }

    return file.readToEndAlloc(gpa, 1 << 30);
}

fn readStdin(gpa: std.mem.Allocator) ![]u8 {
    var buf: [4096]u8 = undefined;
    var reader = std.fs.File.stdin().readerStreaming(&buf);
    return reader.interface.allocRemaining(gpa, .unlimited);
}

fn writeModel(out: *std.Io.Writer, solver: *solver_mod.Solver) !void {
    const num_vars = solver.num_vars;
    try out.writeAll("v");
    var i: u32 = 0;
    while (i < num_vars) : (i += 1) {
        const v = solver.assignment.valueOfVar(i);
        const lit: i32 = switch (v) {
            .@"true", .unassigned => @as(i32, @intCast(i + 1)),
            .@"false" => -@as(i32, @intCast(i + 1)),
        };
        try out.print(" {d}", .{lit});
    }
    try out.writeAll(" 0\n");
}

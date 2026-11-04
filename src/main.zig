const std = @import("std");
const core = @import("core");
const search = @import("search");
const parser = @import("io").parser;
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

fn signalHandler(_: std.posix.SIG) callconv(.c) void {
    solver_mod.interrupted.store(true, .monotonic);
}

fn timeoutThreadFn(io: std.Io, seconds: u32) void {
    io.sleep(.fromSeconds(seconds), .awake) catch {};
    solver_mod.interrupted.store(true, .monotonic);
}

pub fn main(init: std.process.Init) !u8 {
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
    // local testing. On any of these, the solver returns .unknown on its
    // next search iteration and main falls through to the `s UNKNOWN` path.
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
        const t = try std.Thread.spawn(.{}, timeoutThreadFn, .{ io, secs });
        t.detach();
    }

    var formula = blk: {
        if (input_path) |path| {
            const file = std.Io.Dir.cwd().openFile(io, path, .{}) catch |err| {
                try stderr.print("sat: cannot open {s}: {s}\n", .{ path, @errorName(err) });
                return 1;
            };
            defer file.close(io);
            break :blk parseFile(gpa, io, file, std.mem.endsWith(u8, path, ".gz"));
        }
        break :blk parseFile(gpa, io, std.Io.File.stdin(), false);
    } catch |err| {
        try stdout.print("c parse error: {s}\n", .{@errorName(err)});
        try stdout.writeAll("s UNKNOWN\n");
        return 0;
    };
    defer formula.deinit();
    formula.trimUnusedVars();

    // Open the DRAT proof file if requested. It is flushed explicitly once
    // solving ends, so a failed write is reported instead of lost.
    var proof_file: ?std.Io.File = null;
    defer if (proof_file) |f| f.close(io);
    var proof_file_writer: std.Io.File.Writer = undefined;
    var proof_buffer: [8192]u8 = undefined;
    var proof_interface: ?*std.Io.Writer = null;

    if (proof_path) |pp| {
        proof_file = std.Io.Dir.cwd().createFile(io, pp, .{}) catch |err| {
            try stderr.print("sat: cannot create proof file {s}: {s}\n", .{ pp, @errorName(err) });
            return 1;
        };
        proof_file_writer = proof_file.?.writer(io, &proof_buffer);
        proof_interface = &proof_file_writer.interface;
    }

    var solver = solver_mod.Solver.init(gpa, &formula) catch |err| {
        try stdout.print("c error: {s}\n", .{@errorName(err)});
        try stdout.writeAll("s UNKNOWN\n");
        return 0;
    };
    defer solver.deinit();

    if (proof_interface) |w| solver.setProofWriter(w);

    const result = solver.solve() catch |err| {
        try stdout.print("c error: {s}\n", .{@errorName(err)});
        try stdout.writeAll("s UNKNOWN\n");
        return 0;
    };
    if (proof_interface) |w| w.flush() catch {
        const cause = proof_file_writer.err orelse error.WriteFailed;
        try stdout.print("c error: cannot write proof: {s}\n", .{@errorName(cause)});
        try stdout.writeAll("s UNKNOWN\n");
        return 0;
    };
    switch (result) {
        .sat => {
            solver.extendModel();
            if (solver.findFalsifiedClause(&formula)) |index| {
                try stdout.print("c BUG: model falsifies input clause {d}\n", .{index + 1});
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

const InputError = parser.ParseError || std.Io.File.Reader.Error || flate.Decompress.Error;

// Streams `file` through the DIMACS parser, gunzipping when `gzipped`.
// A read failure is reported as the underlying I/O or gzip error.
fn parseFile(gpa: std.mem.Allocator, io: std.Io, file: std.Io.File, gzipped: bool) InputError!cnf.Formula {
    var file_buffer: [64 * 1024]u8 = undefined;
    var file_reader = file.readerStreaming(io, &file_buffer);
    if (!gzipped) {
        return parser.parse(gpa, &file_reader.interface) catch |err| switch (err) {
            error.ReadFailed => {
                if (file_reader.err) |read_err| return read_err;
                return err;
            },
            else => return err,
        };
    }
    var window: [flate.max_window_len]u8 = undefined;
    var decompress = flate.Decompress.init(&file_reader.interface, .gzip, &window);
    return parser.parse(gpa, &decompress.reader) catch |err| switch (err) {
        error.ReadFailed => {
            if (file_reader.err) |read_err| return read_err;
            if (decompress.err) |gzip_err| return gzip_err;
            return err;
        },
        else => return err,
    };
}

fn writeModel(out: *std.Io.Writer, solver: *solver_mod.Solver) !void {
    const num_vars = solver.num_vars;
    try out.writeAll("v");
    var i: u32 = 0;
    while (i < num_vars) : (i += 1) {
        const v = solver.assignment.valueOfVar(i);
        const lit: i32 = switch (v) {
            .true, .unassigned => @as(i32, @intCast(i + 1)),
            .false => -@as(i32, @intCast(i + 1)),
        };
        try out.print(" {d}", .{lit});
    }
    try out.writeAll(" 0\n");
}

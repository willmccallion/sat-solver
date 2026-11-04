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

const exit_success: u8 = 0;
const exit_failure: u8 = 1;
const exit_sat: u8 = 10;
const exit_unsat: u8 = 20;
const exit_unknown: u8 = 0;

const Options = struct {
    input_path: ?[]const u8 = null,
    proof_path: ?[]const u8 = null,
    time_limit_s: ?u32 = null,
};

const UsageError = union(enum) {
    unknown_option: []const u8,
    missing_proof_path,
    missing_time_limit,
    invalid_time_limit: []const u8,
    second_input_path,
};

const Command = union(enum) {
    help,
    solve: Options,
    usage_error: UsageError,
};

pub fn main(init: std.process.Init) !u8 {
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
    const options = switch (parseArgs(args[1..])) {
        .help => {
            try stdout.writeAll(usage);
            return exit_success;
        },
        .usage_error => |err| return reportUsageError(stderr, err),
        .solve => |options| options,
    };

    installSignalHandlers();
    if (options.time_limit_s) |seconds| try startTimeLimit(io, seconds);
    return solveAndReport(init.gpa, io, options, stdout, stderr);
}

fn parseArgs(args: []const []const u8) Command {
    var options: Options = .{};
    var i: usize = 0;
    while (i < args.len) : (i += 1) {
        const arg = args[i];
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) return .help;
        if (std.mem.eql(u8, arg, "--proof")) {
            i += 1;
            if (i == args.len) return .{ .usage_error = .missing_proof_path };
            options.proof_path = args[i];
        } else if (std.mem.eql(u8, arg, "--time-limit")) {
            i += 1;
            if (i == args.len) return .{ .usage_error = .missing_time_limit };
            options.time_limit_s = std.fmt.parseInt(u32, args[i], 10) catch
                return .{ .usage_error = .{ .invalid_time_limit = args[i] } };
        } else if (arg.len > 0 and arg[0] == '-') {
            return .{ .usage_error = .{ .unknown_option = arg } };
        } else {
            if (options.input_path != null) return .{ .usage_error = .second_input_path };
            options.input_path = arg;
        }
    }
    return .{ .solve = options };
}

fn reportUsageError(out: *std.Io.Writer, err: UsageError) !u8 {
    switch (err) {
        .unknown_option => |option| {
            try out.print("sat: unknown option `{s}`\n", .{option});
            try out.writeAll(usage);
        },
        .missing_proof_path => try out.writeAll("sat: --proof requires a PATH argument\n"),
        .missing_time_limit => try out.writeAll("sat: --time-limit requires a SECS argument\n"),
        .invalid_time_limit => |value| try out.print("sat: --time-limit: invalid integer `{s}`\n", .{value}),
        .second_input_path => try out.writeAll("sat: only one input path allowed\n"),
    }
    return exit_failure;
}

// Competition infrastructure sends SIGTERM or SIGXCPU to enforce its
// per-instance timeout; SIGINT is ctrl-c during local testing. Each makes
// the solver return .unknown on its next search iteration.
fn installSignalHandlers() void {
    const act: std.posix.Sigaction = .{
        .handler = .{ .handler = signalHandler },
        .mask = std.posix.sigemptyset(),
        .flags = 0,
    };
    std.posix.sigaction(std.posix.SIG.INT, &act, null);
    std.posix.sigaction(std.posix.SIG.TERM, &act, null);
    std.posix.sigaction(std.posix.SIG.XCPU, &act, null);
}

fn signalHandler(_: std.posix.SIG) callconv(.c) void {
    solver_mod.interrupted.store(true, .monotonic);
}

// A detached thread rather than setitimer, which would mean reconciling
// libc's itimerval with the kernel's itimerspec. One sleep is precise
// enough for limits in whole seconds, and the thread is reaped at exit.
fn startTimeLimit(io: std.Io, seconds: u32) !void {
    const thread = try std.Thread.spawn(.{}, interruptAfter, .{ io, seconds });
    thread.detach();
}

fn interruptAfter(io: std.Io, seconds: u32) void {
    io.sleep(.fromSeconds(seconds), .awake) catch {};
    solver_mod.interrupted.store(true, .monotonic);
}

fn solveAndReport(
    gpa: std.mem.Allocator,
    io: std.Io,
    options: Options,
    stdout: *std.Io.Writer,
    stderr: *std.Io.Writer,
) !u8 {
    var formula = blk: {
        const path = options.input_path orelse break :blk parseFile(gpa, io, std.Io.File.stdin(), .plain);
        const file = std.Io.Dir.cwd().openFile(io, path, .{}) catch |err| {
            try stderr.print("sat: cannot open {s}: {s}\n", .{ path, @errorName(err) });
            return exit_failure;
        };
        defer file.close(io);
        break :blk parseFile(gpa, io, file, if (std.mem.endsWith(u8, path, ".gz")) .gzip else .plain);
    } catch |err| return reportUnknown(stdout, "parse error: {s}", .{@errorName(err)});
    defer formula.deinit();
    formula.trimUnusedVars();

    var proof_file: ProofFile = undefined;
    const proof: ?*ProofFile = if (options.proof_path) |path| blk: {
        proof_file.create(io, path) catch |err| {
            try stderr.print("sat: cannot create proof file {s}: {s}\n", .{ path, @errorName(err) });
            return exit_failure;
        };
        break :blk &proof_file;
    } else null;
    defer if (proof) |p| p.file.close(io);

    var solver = solver_mod.Solver.init(gpa, &formula) catch |err|
        return reportUnknown(stdout, "error: {s}", .{@errorName(err)});
    defer solver.deinit();
    if (proof) |p| solver.setProofWriter(&p.writer.interface);

    const result = solver.solve() catch |err|
        return reportUnknown(stdout, "error: {s}", .{@errorName(err)});
    // Flushed explicitly, so a failed write is reported instead of lost.
    if (proof) |p| p.writer.interface.flush() catch |err|
        return reportUnknown(stdout, "error: cannot write proof: {s}", .{@errorName(p.writer.err orelse err)});
    return reportResult(stdout, &solver, &formula, result);
}

// The DRAT proof output. It must stay in place once created, since the
// writer points into `buffer`.
const ProofFile = struct {
    file: std.Io.File,
    writer: std.Io.File.Writer,
    buffer: [8192]u8,

    fn create(self: *ProofFile, io: std.Io, path: []const u8) !void {
        self.file = try std.Io.Dir.cwd().createFile(io, path, .{});
        self.writer = self.file.writer(io, &self.buffer);
    }
};

fn reportResult(
    out: *std.Io.Writer,
    solver: *solver_mod.Solver,
    formula: *const cnf.Formula,
    result: solver_mod.Result,
) !u8 {
    switch (result) {
        .sat => {
            solver.extendModel();
            if (solver.findFalsifiedClause(formula)) |index| {
                return reportUnknown(out, "BUG: model falsifies input clause {d}", .{index + 1});
            }
            try out.writeAll("s SATISFIABLE\n");
            try writeModel(out, solver);
            return exit_sat;
        },
        .unsat => {
            try out.writeAll("s UNSATISFIABLE\n");
            return exit_unsat;
        },
        .unknown => {
            try out.writeAll("s UNKNOWN\n");
            return exit_unknown;
        },
    }
}

// Prints `c <message>` and the UNKNOWN status line.
fn reportUnknown(out: *std.Io.Writer, comptime fmt: []const u8, args: anytype) !u8 {
    try out.print("c " ++ fmt ++ "\n", args);
    try out.writeAll("s UNKNOWN\n");
    return exit_unknown;
}

const InputError = parser.ParseError || std.Io.File.Reader.Error || flate.Decompress.Error;

const Compression = enum { plain, gzip };

// Streams `file` through the DIMACS parser, decompressing it first if it is
// gzipped. A read failure is reported as the underlying I/O or gzip error.
fn parseFile(gpa: std.mem.Allocator, io: std.Io, file: std.Io.File, compression: Compression) InputError!cnf.Formula {
    var file_buffer: [64 * 1024]u8 = undefined;
    var file_reader = file.readerStreaming(io, &file_buffer);
    if (compression == .plain) {
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

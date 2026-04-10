const std = @import("std");
const parser = @import("parser.zig");
const cnf = @import("cnf.zig");
const solver_mod = @import("solver.zig");

const usage =
    \\usage: sat [path/to/file.cnf]
    \\
    \\Reads a DIMACS CNF formula from the given path, or from stdin when no path
    \\is provided. Output follows the SAT Competition format; exit code encodes
    \\the result (10 = SAT, 20 = UNSAT, 0 = UNKNOWN).
    \\
;

pub fn main() !void {
    var debug_allocator: std.heap.DebugAllocator(.{}) = .init;
    defer _ = debug_allocator.deinit();
    const gpa = debug_allocator.allocator();

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

    if (args.len > 2) {
        try stderr.writeAll(usage);
        try stderr.flush();
        std.process.exit(1);
    }
    if (args.len == 2) {
        const a = args[1];
        if (std.mem.eql(u8, a, "-h") or std.mem.eql(u8, a, "--help")) {
            try stderr.writeAll(usage);
            try stderr.flush();
            std.process.exit(1);
        }
        if (a.len > 0 and a[0] == '-') {
            try stderr.writeAll(usage);
            try stderr.flush();
            std.process.exit(1);
        }
    }

    const source: []u8 = if (args.len == 2)
        readFile(gpa, args[1]) catch |err| {
            stderr.print("sat: cannot read {s}: {s}\n", .{ args[1], @errorName(err) }) catch {};
            stderr.flush() catch {};
            std.process.exit(1);
        }
    else
        readStdin(gpa) catch |err| {
            stderr.print("sat: cannot read stdin: {s}\n", .{@errorName(err)}) catch {};
            stderr.flush() catch {};
            std.process.exit(1);
        };
    defer gpa.free(source);

    const formula = parser.parse(gpa, source) catch |err| {
        try stdout.print("c parse error: {s}\n", .{@errorName(err)});
        try stdout.writeAll("s UNKNOWN\n");
        try stdout.flush();
        std.process.exit(0);
    };

    var solver = try solver_mod.Solver.init(gpa, formula);
    defer solver.deinit();

    const result = solver.solve();
    switch (result) {
        .sat => {
            try stdout.writeAll("s SATISFIABLE\n");
            try writeModel(stdout, &solver);
            try stdout.flush();
            std.process.exit(10);
        },
        .unsat => {
            try stdout.writeAll("s UNSATISFIABLE\n");
            try stdout.flush();
            std.process.exit(20);
        },
        .unknown => {
            try stdout.writeAll("s UNKNOWN\n");
            try stdout.flush();
            std.process.exit(0);
        },
    }
}

fn readFile(gpa: std.mem.Allocator, path: []const u8) ![]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    return file.readToEndAlloc(gpa, 1 << 30);
}

fn readStdin(gpa: std.mem.Allocator) ![]u8 {
    var buf: [4096]u8 = undefined;
    var reader = std.fs.File.stdin().readerStreaming(&buf);
    return reader.interface.allocRemaining(gpa, .unlimited);
}

fn writeModel(out: *std.Io.Writer, solver: *solver_mod.Solver) !void {
    const num_vars = solver.formula.num_vars;
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

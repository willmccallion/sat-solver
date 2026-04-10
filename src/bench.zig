const std = @import("std");
const parser = @import("parser.zig");
const solver_mod = @import("solver.zig");

// sat-bench — batch runner for profiling. Iterates one or more directories
// of .cnf files in a single long-running process, solves each, verifies
// any SAT models, and prints a timing summary at the end. Designed to be
// the target of `perf stat` / `perf record` so samples cover real solver
// work instead of process-startup noise.

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

    var timer = try std.time.Timer.start();

    for (args[1..]) |dir_path| {
        try runDirectory(
            gpa,
            dir_path,
            &total,
            &sat_count,
            &unsat_count,
            &unknown_count,
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
}

fn runDirectory(
    gpa: std.mem.Allocator,
    dir_path: []const u8,
    total: *u32,
    sat_count: *u32,
    unsat_count: *u32,
    unknown_count: *u32,
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

        const result = try solver.solve();
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

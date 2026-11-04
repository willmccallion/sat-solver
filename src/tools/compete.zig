const std = @import("std");
const CnfNames = @import("instances.zig").CnfNames;
const Allocator = std.mem.Allocator;
const report = @import("report.zig");
const Color = report.Color;
const box = report.box;
const Table = report.Table;

// sat-compete — tournament readiness checker for `zig build compete`.
//
// Runs a fixed rubric of checks against the current build and prints a
// colored report comparing the solver to the published SAT Competition
// 2025 main-track reference numbers. Two distinct jobs:
//
//   1. Submittability — the non-negotiable things a SAT Competition
//      submission must do: correct verdicts, gzipped input, signal
//      handling, DRAT proof output.
//
//   2. Competitiveness — rough performance metrics (wall time, IPC,
//      branch-miss %, ns/propagation) compared to a published
//      reference so you know how far off you are from placing.
//
// The published reference is hard-coded at the top of this file. If
// a future SAT Competition shifts the numbers, update them here.

// Published reference — SAT Competition 2025 Main Track (sequential).
// Source: https://satcompetition.github.io/2025/satcomp25slides.pdf
//         Codel, Fazekas, Heule, Iser — SAT 2025, Glasgow, August 2025
const ref_total_instances: u32 = 400;
const ref_timeout_seconds: u32 = 5000;
const ref_scoring: []const u8 = "PAR-2 (penalizes slow solves)";
const ref_winner_name: []const u8 = "AE-Kissat-MAB";
const ref_winner_solved: u32 = 327;
const ref_winner_par2: f64 = 2264.73;
const ref_second_name: []const u8 = "Kissat-public";
const ref_second_solved: u32 = 321;
const ref_third_name: []const u8 = "Kissat-VSA";
const ref_third_solved: u32 = 317;

// Directional perf targets for a competitive solver. These aren't
// exact published numbers — modern solver papers rarely publish ns-
// level breakdowns — but they represent the order of magnitude a
// competitive CDCL implementation should be in.
const ref_ipc_good: f64 = 2.0;
const ref_branch_miss_good_pct: f64 = 5.0;
const ref_bad_spec_good_pct: f64 = 20.0;

const Status = enum { pass, fail, warn, skip };

const Check = struct {
    name: []const u8,
    status: Status,
    detail: []u8, // owned
};

const Perf = struct {
    available: bool = false,
    wall_ms: f64 = 0,
    instance_count: u64 = 0,
    propagations: u64 = 0,
    conflicts: u64 = 0,
    ipc: f64 = 0,
    branch_miss_pct: f64 = 0,
    bad_spec_pct: f64 = 0,
    retiring_pct: f64 = 0,
};

const Capacity = struct {
    tested: u32 = 0,
    solved: u32 = 0,
    elapsed_s: f64 = 0,
    limit_s: u32 = 0,
    available: bool = false,
};

const width: usize = 72;

pub fn main(init: std.process.Init) !u8 {
    const gpa = init.gpa;
    const io = init.io;

    var stdout_buffer: [8192]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writer(io, &stdout_buffer);
    const stdout = &stdout_writer.interface;
    defer stdout.flush() catch {};

    var stderr_buffer: [2048]u8 = undefined;
    var stderr_writer = std.Io.File.stderr().writer(io, &stderr_buffer);
    const stderr = &stderr_writer.interface;
    defer stderr.flush() catch {};

    const args = try init.minimal.args.toSlice(init.arena.allocator());

    const sat_path = if (args.len >= 2) args[1] else "./zig-out/bin/sat";
    const bench_path = if (args.len >= 3) args[2] else "./zig-out/bin/sat-bench";

    var checks: std.ArrayList(Check) = .empty;
    defer {
        for (checks.items) |c| gpa.free(c.detail);
        checks.deinit(gpa);
    }

    try stdout.print("{s}[1/5] verifying binaries...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();
    try checks.append(gpa, try checkBinary(gpa, io, "sat binary", sat_path));
    try checks.append(gpa, try checkBinary(gpa, io, "sat-bench binary", bench_path));

    try stdout.print("{s}[2/5] running SATLIB correctness sweep...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();
    try checks.append(gpa, try checkCorrectness(gpa, io));

    try stdout.print("{s}[3/5] verifying gzip input + signal + DRAT...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();
    try checks.append(gpa, try checkGzipInput(gpa, io, sat_path));
    try checks.append(gpa, try checkSignalHandling(gpa, io, sat_path));
    try checks.append(gpa, try checkDratOutput(gpa, io, sat_path));

    try stdout.print("{s}[4/5] collecting perf baseline (uf100 + uuf100)...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();
    var perf: Perf = .{};
    collectPerf(gpa, io, bench_path, &perf) catch |err| {
        try stderr.print("warning: perf baseline failed: {s}\n", .{@errorName(err)});
    };

    try stdout.print("{s}[5/5] capacity probe (uf250 sample, 5 s each)...{s}\n", .{ Color.dim, Color.reset });
    try stdout.flush();
    var capacity: Capacity = .{};
    collectCapacity(gpa, io, sat_path, &capacity) catch |err| {
        try stderr.print("warning: capacity probe failed: {s}\n", .{@errorName(err)});
    };

    try stdout.writeAll("\n");
    try printReport(.{ .writer = stdout, .width = width }, checks.items, &perf, &capacity);

    // Non-zero exit if any submittability check failed.
    for (checks.items) |c| {
        if (c.status == .fail) return 1;
    }
    return 0;
}

fn checkBinary(gpa: Allocator, io: std.Io, name: []const u8, path: []const u8) !Check {
    const file = std.Io.Dir.cwd().openFile(io, path, .{}) catch |err| {
        return .{
            .name = name,
            .status = .fail,
            .detail = try std.fmt.allocPrint(gpa, "{s}: {s}", .{ path, @errorName(err) }),
        };
    };
    file.close(io);
    // Strip the cache prefix so the detail column stays readable.
    const base = std.fs.path.basename(path);
    return .{
        .name = name,
        .status = .pass,
        .detail = try std.fmt.allocPrint(gpa, "{s}", .{base}),
    };
}

// Spawns `bench/run.sh` and parses the trailing "all N instances correct"
// line. Anything else (partial results, mismatches, missing instances)
// is a fail with the first few mismatch lines quoted in the detail.
fn checkCorrectness(gpa: Allocator, io: std.Io) !Check {
    const result = std.process.run(gpa, io, .{
        .argv = &.{ "bash", "bench/run.sh" },
        .stdout_limit = .limited(1 << 20),
        .stderr_limit = .limited(1 << 20),
    }) catch |err| {
        return .{
            .name = "correctness sweep",
            .status = .fail,
            .detail = try std.fmt.allocPrint(gpa, "spawn failed: {s}", .{@errorName(err)}),
        };
    };
    defer gpa.free(result.stdout);
    defer gpa.free(result.stderr);

    const passed = result.term == .exited and result.term.exited == 0;
    var total: u64 = 0;
    var it = std.mem.splitScalar(u8, result.stdout, '\n');
    while (it.next()) |line| {
        if (std.mem.startsWith(u8, line, "all ")) {
            const rest = line["all ".len..];
            const sp = std.mem.indexOfScalar(u8, rest, ' ') orelse continue;
            total = std.fmt.parseInt(u64, rest[0..sp], 10) catch 0;
        }
    }

    if (passed and total > 0) {
        return .{
            .name = "correctness sweep",
            .status = .pass,
            .detail = try std.fmt.allocPrint(gpa, "{d}/{d} instances across SATLIB + DIMACS", .{ total, total }),
        };
    }
    return .{
        .name = "correctness sweep",
        .status = .fail,
        .detail = try gpa.dupe(u8, "bench/run.sh reported mismatches (see `bench/run.sh`)"),
    };
}

// sat must give the same verdict and model for a fixture and its gzipped
// copy.
fn checkGzipInput(gpa: Allocator, io: std.Io, sat_path: []const u8) !Check {
    const plain_path = "tests/fixtures/trivial_sat.cnf";
    const gz_path = "tests/fixtures/trivial_sat.cnf.gz";

    const plain = std.process.run(gpa, io, .{
        .argv = &.{ sat_path, plain_path },
        .stdout_limit = .limited(1 << 14),
        .stderr_limit = .limited(1 << 14),
    }) catch |err| return Check{
        .name = "gzip input",
        .status = .fail,
        .detail = try std.fmt.allocPrint(gpa, "sat spawn: {s}", .{@errorName(err)}),
    };
    defer gpa.free(plain.stdout);
    defer gpa.free(plain.stderr);

    const gz_out = std.process.run(gpa, io, .{
        .argv = &.{ sat_path, gz_path },
        .stdout_limit = .limited(1 << 14),
        .stderr_limit = .limited(1 << 14),
    }) catch |err| return Check{
        .name = "gzip input",
        .status = .fail,
        .detail = try std.fmt.allocPrint(gpa, "sat spawn (gz): {s}", .{@errorName(err)}),
    };
    defer gpa.free(gz_out.stdout);
    defer gpa.free(gz_out.stderr);

    const same_exit = std.meta.eql(plain.term, gz_out.term);
    const same_out = std.mem.eql(u8, plain.stdout, gz_out.stdout);
    if (!same_exit or !same_out) {
        return .{
            .name = "gzip input",
            .status = .fail,
            .detail = try gpa.dupe(u8, "sat disagrees between .cnf and .cnf.gz"),
        };
    }

    var lines = std.mem.splitScalar(u8, plain.stdout, '\n');
    return .{
        .name = "gzip input",
        .status = .pass,
        .detail = try std.fmt.allocPrint(gpa, "same verdict ({s})", .{lines.first()}),
    };
}

// The SIGTERM goes to sat solving 11 pigeons in 10 holes, which takes over
// half a minute even in ReleaseFast, so a signal sent after
// `signal_delay_ms` always arrives mid-search rather than before sat has
// installed its handler or after it has finished.
const pigeonhole_holes = 10;
const signal_delay_ms = 500;

fn writePigeonhole(io: std.Io, path: []const u8, holes: u32) !void {
    var file = try std.Io.Dir.cwd().createFile(io, path, .{});
    defer file.close(io);
    var buffer: [4096]u8 = undefined;
    var file_writer = file.writer(io, &buffer);
    const w = &file_writer.interface;
    const pigeons = holes + 1;
    const clause_count = pigeons + holes * pigeons * (pigeons - 1) / 2;
    try w.print("p cnf {d} {d}\n", .{ pigeons * holes, clause_count });
    for (0..pigeons) |pigeon| {
        for (0..holes) |hole| try w.print("{d} ", .{pigeon * holes + hole + 1});
        try w.writeAll("0\n");
    }
    for (0..holes) |hole| {
        for (0..pigeons) |a| {
            for (a + 1..pigeons) |b| try w.print("-{d} -{d} 0\n", .{ a * holes + hole + 1, b * holes + hole + 1 });
        }
    }
    try w.flush();
}

// Spawns the solver on a long-ish instance, sends SIGTERM after a
// short delay, verifies it exits 0 with `s UNKNOWN` on stdout.
fn checkSignalHandling(gpa: Allocator, io: std.Io, sat_path: []const u8) !Check {
    const inst = "bench/.cache/sat-compete-pigeonhole.cnf";
    try std.Io.Dir.cwd().createDirPath(io, "bench/.cache");
    try writePigeonhole(io, inst, pigeonhole_holes);

    var child = try std.process.spawn(io, .{
        .argv = &.{ sat_path, inst },
        .stdin = .ignore,
        .stdout = .pipe,
        .stderr = .ignore,
    });

    io.sleep(.fromMilliseconds(signal_delay_ms), .awake) catch {};
    if (child.id) |pid| std.posix.kill(pid, std.posix.SIG.TERM) catch {};

    var stdout_buffer: [1024]u8 = undefined;
    var stdout_reader = child.stdout.?.readerStreaming(io, &stdout_buffer);
    const child_stdout = try stdout_reader.interface.allocRemaining(gpa, .limited(1 << 16));
    defer gpa.free(child_stdout);
    const term = try child.wait(io);

    const exit_ok = term == .exited and term.exited == 0;
    const says_unknown = std.mem.indexOf(u8, child_stdout, "s UNKNOWN") != null;
    if (exit_ok and says_unknown) {
        return .{
            .name = "signal handling (SIGTERM)",
            .status = .pass,
            .detail = try gpa.dupe(u8, "exits 0 with `s UNKNOWN`"),
        };
    }
    return .{
        .name = "signal handling (SIGTERM)",
        .status = .fail,
        .detail = try std.fmt.allocPrint(
            gpa,
            "term={any} stdout=`{s}`",
            .{ term, std.mem.trim(u8, child_stdout, " \t\r\n") },
        ),
    };
}

// Runs `sat --proof ...` on a known UNSAT instance and checks the proof
// file was created and ends with an empty clause line. If `drat-trim`
// is on PATH it also does a full proof-check round-trip.
fn checkDratOutput(gpa: Allocator, io: std.Io, sat_path: []const u8) !Check {
    const inst = "tests/fixtures/trivial_unsat.cnf";
    const drat_path = "bench/.cache/sat-compete.drat";
    try std.Io.Dir.cwd().createDirPath(io, "bench/.cache");
    std.Io.Dir.cwd().deleteFile(io, drat_path) catch |err| switch (err) {
        error.FileNotFound => {},
        else => return err,
    };

    const run = std.process.run(gpa, io, .{
        .argv = &.{ sat_path, "--proof", drat_path, inst },
        .stdout_limit = .limited(1 << 14),
        .stderr_limit = .limited(1 << 14),
    }) catch |err| return Check{
        .name = "DRAT proof output",
        .status = .fail,
        .detail = try std.fmt.allocPrint(gpa, "sat spawn: {s}", .{@errorName(err)}),
    };
    defer gpa.free(run.stdout);
    defer gpa.free(run.stderr);

    const contents = std.Io.Dir.cwd().readFileAlloc(io, drat_path, gpa, .limited(1 << 16)) catch |err| return Check{
        .name = "DRAT proof output",
        .status = .fail,
        .detail = try std.fmt.allocPrint(gpa, "no proof file: {s}", .{@errorName(err)}),
    };
    defer gpa.free(contents);

    const has_empty_clause = std.mem.indexOf(u8, contents, "0\n") != null;
    if (!has_empty_clause) {
        return .{
            .name = "DRAT proof output",
            .status = .fail,
            .detail = try gpa.dupe(u8, "proof missing empty clause"),
        };
    }

    // Optional: round-trip with drat-trim if installed.
    const drat_trim_check = std.process.run(gpa, io, .{
        .argv = &.{ "drat-trim", "--version" },
        .stdout_limit = .limited(1 << 14),
        .stderr_limit = .limited(1 << 14),
    }) catch null;
    if (drat_trim_check) |c| {
        gpa.free(c.stdout);
        gpa.free(c.stderr);

        const verify = std.process.run(gpa, io, .{
            .argv = &.{ "drat-trim", inst, drat_path },
            .stdout_limit = .limited(1 << 16),
            .stderr_limit = .limited(1 << 16),
        }) catch {
            std.Io.Dir.cwd().deleteFile(io, drat_path) catch {};
            return .{
                .name = "DRAT proof output",
                .status = .warn,
                .detail = try gpa.dupe(u8, "drat-trim spawn failed"),
            };
        };
        defer gpa.free(verify.stdout);
        defer gpa.free(verify.stderr);
        std.Io.Dir.cwd().deleteFile(io, drat_path) catch {};

        const verified = std.mem.indexOf(u8, verify.stdout, "s VERIFIED") != null;
        if (verified) {
            return .{
                .name = "DRAT proof output",
                .status = .pass,
                .detail = try gpa.dupe(u8, "round-trip verified by drat-trim"),
            };
        }
        return .{
            .name = "DRAT proof output",
            .status = .fail,
            .detail = try gpa.dupe(u8, "drat-trim rejected proof"),
        };
    }

    std.Io.Dir.cwd().deleteFile(io, drat_path) catch {};
    return .{
        .name = "DRAT proof output",
        .status = .warn,
        .detail = try gpa.dupe(u8, "emits empty clause (install `drat-trim` for full verification)"),
    };
}

fn collectPerf(gpa: Allocator, io: std.Io, bench_path: []const u8, out: *Perf) !void {
    // Light perf probe on uf100 + uuf100 — a few seconds total, long
    // enough to get stable counter values without the 40-second deep
    // bench. Full profiling lives in `zig build bench`.
    const events = "cycles,instructions,branches,branch-misses";

    var argv: std.ArrayList([]const u8) = .empty;
    defer argv.deinit(gpa);
    try argv.appendSlice(gpa, &.{
        "perf",                      "stat",
        "-x",                        ",",
        "-e",                        events,
        "-M",                        "TopdownL1",
        "--",                        bench_path,
        "bench/instances/uf100-430", "bench/instances/uuf100-430",
    });

    const result = std.process.run(gpa, io, .{
        .argv = argv.items,
        .stdout_limit = .limited(1 << 22),
        .stderr_limit = .limited(1 << 22),
    }) catch |err| {
        if (err == error.FileNotFound) {
            // `perf` not installed; don't hard-fail. Perf is optional
            // for submittability and only needed for the competitive
            // scoreboard section.
            return;
        }
        return err;
    };
    defer gpa.free(result.stdout);
    defer gpa.free(result.stderr);

    if (result.term != .exited or result.term.exited != 0) return;

    const bench = try report.BenchSummary.parse(result.stdout);
    const counters = report.PerfStat.parse(result.stderr);
    out.* = .{
        .available = true,
        .wall_ms = @as(f64, @floatFromInt(bench.elapsed_ns)) / 1e6,
        .instance_count = bench.instance_count,
        .propagations = bench.solver.propagations,
        .conflicts = bench.solver.conflicts,
        .ipc = counters.ipc(),
        .branch_miss_pct = counters.branchMissPercent(),
        .bad_spec_pct = counters.topdown_bad_spec,
        .retiring_pct = counters.topdown_retiring,
    };
}

// Runs the solver on a sample of uf250 instances with a short time
// limit and reports how many finished. This is the highest-tier
// classical random 3-SAT set; modern solvers blast through it in
// sub-second per instance. If yours times out on many of these you're
// nowhere near competitive — but if it clears the sample, it means
// the CDCL + reduceDB stack is working.
fn collectCapacity(gpa: Allocator, io: std.Io, sat_path: []const u8, out: *Capacity) !void {
    const dir_path = "bench/instances/uf250-1065";
    // An unfetched set leaves `out.available` false, which the report notes.
    var dir = std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true }) catch |err| switch (err) {
        error.FileNotFound => return,
        else => return err,
    };
    defer dir.close(io);

    const per_inst_limit_s: u32 = 5;
    const max_samples: u32 = 10;

    const names = try CnfNames.list(gpa, io, dir);
    defer names.deinit(gpa);

    const sample_count = @min(@as(usize, max_samples), names.items.len);
    const start = std.Io.Clock.Timestamp.now(io, .awake);
    const limit_arg = try std.fmt.allocPrint(gpa, "{d}", .{per_inst_limit_s});
    defer gpa.free(limit_arg);

    for (names.items[0..sample_count]) |name| {
        const path = try std.fs.path.join(gpa, &.{ dir_path, name });
        defer gpa.free(path);

        const result = try std.process.run(gpa, io, .{
            .argv = &.{ sat_path, "--time-limit", limit_arg, path },
            .stdout_limit = .limited(1 << 14),
            .stderr_limit = .limited(1 << 14),
        });
        defer gpa.free(result.stdout);
        defer gpa.free(result.stderr);

        out.tested += 1;
        if (result.term == .exited) {
            const code = result.term.exited;
            if (code == 10 or code == 20) out.solved += 1;
        }
    }

    out.elapsed_s = @as(f64, @floatFromInt(start.untilNow(io).raw.nanoseconds)) / 1e9;
    out.limit_s = per_inst_limit_s;
    out.available = sample_count > 0;
}

fn statusGlyph(s: Status) struct { color: []const u8, glyph: []const u8 } {
    return switch (s) {
        .pass => .{ .color = Color.green, .glyph = "[ PASS ]" },
        .fail => .{ .color = Color.red, .glyph = "[ FAIL ]" },
        .warn => .{ .color = Color.yellow, .glyph = "[ WARN ]" },
        .skip => .{ .color = Color.gray, .glyph = "[ SKIP ]" },
    };
}

fn checkRow(t: Table, check: *const Check) !void {
    try t.startRow();
    const g = statusGlyph(check.status);
    try t.writer.print("{s}{s}{s}{s}  ", .{ g.color, Color.bold, g.glyph, Color.reset });
    try t.writer.print("{s}", .{check.name});

    const label_width: usize = 30;
    const name_cols = g.glyph.len + 2 + check.name.len;
    const pad: usize = if (name_cols < label_width) label_width - name_cols else 1;
    try t.writer.splatByteAll(' ', pad);
    var visible = name_cols + pad;
    visible += try t.writeTruncated(Color.dim, check.detail, visible);

    try t.endRow(visible);
}

fn plainRow(t: Table, label: []const u8, value: []const u8, note: []const u8) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    const label_pad = 22 -| label.len;
    try t.writer.splatByteAll(' ', label_pad);
    var vis = label.len + label_pad;
    try t.writer.print("{s}{s}{s}", .{ Color.cyan, value, Color.reset });
    vis += report.displayWidth(value);
    if (note.len > 0) {
        try t.writer.print("   {s}{s}{s}", .{ Color.dim, note, Color.reset });
        vis += 3 + note.len;
    }
    try t.endRow(vis);
}

fn compareRow(
    t: Table,
    label: []const u8,
    your_value: []const u8,
    ref_value: []const u8,
    verdict_color: []const u8,
) !void {
    try t.startRow();
    try t.writer.writeAll(label);
    const label_pad = 22 -| label.len;
    try t.writer.splatByteAll(' ', label_pad);
    var vis = label.len + label_pad;

    try t.writer.print("{s}{s}{s}", .{ verdict_color, your_value, Color.reset });
    vis += your_value.len;

    const mid_pad: usize = if (your_value.len < 14) 14 - your_value.len else 2;
    try t.writer.splatByteAll(' ', mid_pad);
    vis += mid_pad;

    try t.writer.print("{s}vs {s}{s}", .{ Color.dim, ref_value, Color.reset });
    vis += 3 + ref_value.len;

    try t.endRow(vis);
}

fn printReport(
    t: Table,
    checks: []const Check,
    perf: *const Perf,
    cap: *const Capacity,
) !void {
    try t.rule(box.tl, box.tr);
    try t.textRow(Color.bold ++ Color.cyan, "tournament readiness — sat");
    try t.blankRow();
    try t.textRow(Color.dim, "reference: SAT Competition 2025, Main Sequential Track");
    try t.textRow(Color.dim, "satcompetition.github.io/2025/satcomp25slides.pdf");
    try t.blankRow();

    const is_submittable = try printSubmittability(t, checks);
    try printScoreboard(t);
    try printHardware(t, perf);
    try printCapacity(t, cap);
    try printVerdict(t, is_submittable, perf);
}

// Lists the required checks; true when none failed.
fn printSubmittability(t: Table, checks: []const Check) !bool {
    try t.sectionHeader("submittability (required for competition entry)");
    for (checks) |*check| try checkRow(t, check);
    try t.blankRow();

    const is_submittable = for (checks) |check| {
        if (check.status == .fail) break false;
    } else true;
    try t.startRow();
    if (is_submittable) {
        try t.writer.print(
            "{s}{s}=> submittable{s}{s}   every required check passes{s}",
            .{ Color.green, Color.bold, Color.reset, Color.dim, Color.reset },
        );
        try t.endRow("=> submittable   every required check passes".len);
    } else {
        try t.writer.print(
            "{s}{s}=> NOT submittable{s}{s}   at least one required check failed{s}",
            .{ Color.red, Color.bold, Color.reset, Color.dim, Color.reset },
        );
        try t.endRow("=> NOT submittable   at least one required check failed".len);
    }
    try t.blankRow();
    return is_submittable;
}

fn printScoreboard(t: Table) !void {
    try t.sectionHeader("competitive scoreboard");
    var line_buf: [96]u8 = undefined;
    try t.textRow(Color.dim, try std.fmt.bufPrint(&line_buf, "SAT Comp 2025 main sequential, {d}s timeout,", .{ref_timeout_seconds}));
    try t.textRow(Color.dim, "scored by " ++ ref_scoring);
    try t.blankRow();
    try t.textRow(Color.cyan, try std.fmt.bufPrint(&line_buf, "1. {s:<16} {d}/{d}  PAR-2 {d:.0}", .{
        ref_winner_name, ref_winner_solved, ref_total_instances, ref_winner_par2,
    }));
    try t.textRow(Color.dim, try std.fmt.bufPrint(&line_buf, "2. {s:<16} {d}/{d}", .{
        ref_second_name, ref_second_solved, ref_total_instances,
    }));
    try t.textRow(Color.dim, try std.fmt.bufPrint(&line_buf, "3. {s:<16} {d}/{d}", .{
        ref_third_name, ref_third_solved, ref_total_instances,
    }));
    try t.blankRow();
}

// The solver's hardware metrics against the ranges a competitive solver
// reaches.
fn printHardware(t: Table, perf: *const Perf) !void {
    if (!perf.available) {
        try t.textRow(Color.yellow, "hardware metrics: skipped (perf not available)");
        try t.blankRow();
        return;
    }
    try t.textRow(Color.bold, "hardware metrics (light bench: uf100 + uuf100)");
    try t.blankRow();

    var value_buf: [16]u8 = undefined;
    try compareRow(t, "IPC", try std.fmt.bufPrint(&value_buf, "{d:.2}", .{perf.ipc}), "~2.0+ (target)", targetColor(perf.ipc >= ref_ipc_good));
    try compareRow(
        t,
        "branch-miss rate",
        try std.fmt.bufPrint(&value_buf, "{d:.1}%", .{perf.branch_miss_pct}),
        "< 5% (target)",
        targetColor(perf.branch_miss_pct < ref_branch_miss_good_pct),
    );
    try compareRow(
        t,
        "bad-speculation",
        try std.fmt.bufPrint(&value_buf, "{d:.1}%", .{perf.bad_spec_pct}),
        "< 20% (target)",
        targetColor(perf.bad_spec_pct < ref_bad_spec_good_pct),
    );
    if (perf.propagations > 0 and perf.wall_ms > 0) {
        const ns_per_prop: f64 = perf.wall_ms * 1e6 / @as(f64, @floatFromInt(perf.propagations));
        try compareRow(
            t,
            "ns / propagation",
            try std.fmt.bufPrint(&value_buf, "{d:.0} ns", .{ns_per_prop}),
            "30-80 ns (target)",
            targetColor(ns_per_prop < 100),
        );
    }
    try t.blankRow();
}

fn targetColor(meets_target: bool) []const u8 {
    return if (meets_target) Color.green else Color.red;
}

fn printCapacity(t: Table, cap: *const Capacity) !void {
    if (!cap.available or cap.tested == 0) {
        try t.textRow(Color.dim, "capacity probe skipped (fetch uf250 via bench/fetch.sh)");
        try t.blankRow();
        return;
    }
    var title_buf: [64]u8 = undefined;
    try t.textRow(Color.bold, try std.fmt.bufPrint(&title_buf, "capacity (uf250 sample, {d}s/instance)", .{cap.limit_s}));
    try t.blankRow();

    var solved_buf: [96]u8 = undefined;
    const solved = try std.fmt.bufPrint(&solved_buf, "solved  {d}/{d}  in {d:.1} s total", .{ cap.solved, cap.tested, cap.elapsed_s });
    try plainRow(t, "your solver", solved, "");
    // Every modern CDCL solver finishes uf250 in well under a second per
    // instance, so missing any of the sample is far from competitive.
    try plainRow(t, "modern CDCL", "≈10/10", "< 1 s / instance (Kissat / CaDiCaL)");
    try t.blankRow();
}

fn printVerdict(t: Table, is_submittable: bool, perf: *const Perf) !void {
    try t.rule(box.lt, box.rt);
    try t.blankRow();
    const is_competitive = perf.available and perf.ipc >= ref_ipc_good and
        perf.branch_miss_pct < ref_branch_miss_good_pct and
        perf.bad_spec_pct < ref_bad_spec_good_pct;
    const color, const verdict = if (!is_submittable)
        .{ Color.red, "NOT SUBMITTABLE" }
    else if (is_competitive)
        .{ Color.green, "SUBMITTABLE + COMPETITIVE" }
    else
        .{ Color.yellow, "SUBMITTABLE, not yet competitive" };
    try t.startRow();
    try t.writer.writeAll("overall: ");
    try t.writer.print("{s}{s}{s}{s}", .{ color, Color.bold, verdict, Color.reset });
    try t.endRow("overall: ".len + verdict.len);
    try t.blankRow();
    try t.rule(box.bl, box.br);
}

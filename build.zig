const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const layers = addLayers(b, target, optimize);
    const tools = addTools(b, target, optimize, layers);
    addProfileSteps(b, tools);

    const sat_module = b.addModule("sat", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{ layers.core, layers.io, layers.search },
    });

    const run_cmd = b.addRunArtifact(tools.sat);
    run_cmd.step.dependOn(b.getInstallStep());
    run_cmd.addPassthruArgs();
    b.step("run", "Run the sat solver").dependOn(&run_cmd.step);

    addTests(b, target, optimize, layers, sat_module, tools);
}

// The layer modules, as imports. Dependency DAG, strictly downward:
//   core  ←  io
//   core, io, heuristics  ←  search
//   everything  ←  tools, main, root (the `sat` public module)
const Layers = struct {
    core: std.Build.Module.Import,
    io: std.Build.Module.Import,
    heuristics: std.Build.Module.Import,
    search: std.Build.Module.Import,
};

fn addLayers(b: *std.Build, target: std.Build.ResolvedTarget, optimize: std.builtin.OptimizeMode) Layers {
    const core = b.createModule(.{ .root_source_file = b.path("src/core/mod.zig"), .target = target, .optimize = optimize });
    const io = b.createModule(.{
        .root_source_file = b.path("src/io/mod.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{.{ .name = "core", .module = core }},
    });
    const heuristics = b.createModule(.{ .root_source_file = b.path("src/heuristics/mod.zig"), .target = target, .optimize = optimize });
    const search = b.createModule(.{
        .root_source_file = b.path("src/search/mod.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "core", .module = core },
            .{ .name = "io", .module = io },
            .{ .name = "heuristics", .module = heuristics },
        },
    });
    return .{
        .core = .{ .name = "core", .module = core },
        .io = .{ .name = "io", .module = io },
        .heuristics = .{ .name = "heuristics", .module = heuristics },
        .search = .{ .name = "search", .module = search },
    };
}

const Tools = struct {
    sat: *std.Build.Step.Compile,
    sudoku: *std.Build.Step.Compile,
    // Always ReleaseFast, since the profile steps measure it.
    bench_release: *std.Build.Step.Compile,
    profile: *std.Build.Step.Compile,
    compete: *std.Build.Step.Compile,
};

fn addTools(
    b: *std.Build,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    layers: Layers,
) Tools {
    // The solver and sat-bench keep their symbols for perf annotate.
    const sat = addTool(b, target, .{
        .name = "sat",
        .root = "src/main.zig",
        .optimize = optimize,
        .strip = false,
        .imports = &.{ layers.core, layers.io, layers.search },
    });
    const bench_imports: []const std.Build.Module.Import = &.{ layers.io, layers.search };
    const bench = addTool(b, target, .{
        .name = "sat-bench",
        .root = "src/tools/bench.zig",
        .optimize = optimize,
        .strip = false,
        .imports = bench_imports,
    });
    const sudoku = addTool(b, target, .{
        .name = "sat-sudoku",
        .root = "src/tools/sudoku.zig",
        .optimize = optimize,
        .imports = &.{ layers.core, layers.search },
    });
    b.installArtifact(sat);
    b.installArtifact(bench);
    b.installArtifact(sudoku);

    const sudoku_run = b.addRunArtifact(sudoku);
    sudoku_run.addPassthruArgs();
    b.step("sudoku", "Solve a Sudoku (zig build sudoku -- PUZZLE)").dependOn(&sudoku_run.step);

    return .{
        .sat = sat,
        .sudoku = sudoku,
        .bench_release = addTool(b, target, .{
            .name = "sat-bench",
            .root = "src/tools/bench.zig",
            .optimize = .ReleaseFast,
            .strip = false,
            .imports = bench_imports,
        }),
        .profile = addTool(b, target, .{
            .name = "sat-profile",
            .root = "src/tools/profile.zig",
            .optimize = .Debug,
            .imports = &.{layers.search},
        }),
        .compete = addTool(b, target, .{
            .name = "sat-compete",
            .root = "src/tools/compete.zig",
            .optimize = .Debug,
            .imports = &.{layers.search},
        }),
    };
}

const Tool = struct {
    name: []const u8,
    root: []const u8,
    optimize: std.builtin.OptimizeMode,
    strip: ?bool = null,
    imports: []const std.Build.Module.Import = &.{},
};

fn addTool(b: *std.Build, target: std.Build.ResolvedTarget, tool: Tool) *std.Build.Step.Compile {
    return b.addExecutable(.{
        .name = tool.name,
        .root_module = b.createModule(.{
            .root_source_file = b.path(tool.root),
            .target = target,
            .optimize = tool.optimize,
            .strip = tool.strip,
            .imports = tool.imports,
        }),
    });
}

fn addProfileSteps(b: *std.Build, tools: Tools) void {
    addProfileStep(b, tools, "bench", "Run deep perf profile on uf200/uuf200 + uf250/uuf250 (~7 min)", &.{
        "bench/instances/uf200-860",
        "bench/instances/uuf200-860",
        "bench/instances/uf250-1065",
        "bench/instances/uuf250-1065",
    });

    const compete_run = b.addRunArtifact(tools.compete);
    compete_run.addArtifactArg(tools.sat);
    compete_run.addArtifactArg(tools.bench_release);
    compete_run.has_side_effects = true;
    compete_run.stdio = .inherit;
    b.step(
        "compete",
        "Tournament readiness check — submittability + perf vs SAT Competition 2025",
    ).dependOn(&compete_run.step);

    addProfileStep(b, tools, "bench-quick", "Run fast perf profile on uf100 + uuf100 (~4 s)", &.{
        "bench/instances/uf100-430",
        "bench/instances/uuf100-430",
    });
    addProfileStep(b, tools, "bench-industrial", "Perf profile on SATLIB crafted (bf/ssa/hanoi/parity/aim) with 30 s cap", &.{
        "--timeout-sec",
        "30",
        "bench/instances/dimacs-bf",
        "bench/instances/dimacs-ssa",
        "bench/instances/dimacs-hanoi",
        "bench/instances/dimacs-parity",
        "bench/instances/dimacs-aim",
    });
    addProfileStep(b, tools, "bench-satcomp", "Perf profile on SAT Competition 2025 subset (run bench/fetch_satcomp.sh first)", &.{
        "--timeout-sec",
        "60",
        "bench/instances/satcomp2025",
    });
}

// A step that runs sat-profile over the release sat-bench with `args`.
fn addProfileStep(b: *std.Build, tools: Tools, name: []const u8, description: []const u8, args: []const []const u8) void {
    const run = b.addRunArtifact(tools.profile);
    run.addArtifactArg(tools.bench_release);
    run.addArgs(args);
    run.has_side_effects = true;
    run.stdio = .inherit;
    b.step(name, description).dependOn(&run.step);
}

fn addTests(
    b: *std.Build,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    layers: Layers,
    sat_module: *std.Build.Module,
    tools: Tools,
) void {
    const test_filters = b.option(
        []const []const u8,
        "test-filter",
        "Run only the unit tests whose names contain this text",
    ) orelse &.{};
    const unit_tests = b.addTest(.{
        .filters = test_filters,
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/unit.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "sat", .module = sat_module }},
        }),
    });
    const run_unit_tests = b.addRunArtifact(unit_tests);
    b.step("unit", "Run only tests/unit.zig (narrow with -Dtest-filter=TEXT)").dependOn(&run_unit_tests.step);

    const test_step = b.step("test", "Run unit tests and end-to-end round-trip");
    test_step.dependOn(&run_unit_tests.step);
    test_step.dependOn(&b.addRunArtifact(b.addTest(.{ .root_module = tools.sudoku.root_module })).step);
    // The profile tools only run under perf, so compiling them here is
    // what keeps them building.
    test_step.dependOn(&tools.profile.step);
    test_step.dependOn(&tools.compete.step);
    const report_tests = b.addTest(.{ .root_module = b.createModule(.{
        .root_source_file = b.path("src/tools/report.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{layers.search},
    }) });
    test_step.dependOn(&b.addRunArtifact(report_tests).step);
    test_step.dependOn(&b.addRunArtifact(b.addTest(.{ .root_module = layers.heuristics.module })).step);

    addSudokuTests(b, test_step, tools.sudoku);
    addSolverCliTests(b, target, test_step, tools.sat);
}

fn addSudokuTests(b: *std.Build, test_step: *std.Build.Step, sudoku: *std.Build.Step.Compile) void {
    const solved = b.addRunArtifact(sudoku);
    solved.addArg("53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79");
    solved.expectExitCode(0);
    solved.expectStdOutEqual(
        \\5 3 4 | 6 7 8 | 9 1 2
        \\6 7 2 | 1 9 5 | 3 4 8
        \\1 9 8 | 3 4 2 | 5 6 7
        \\------+-------+------
        \\8 5 9 | 7 6 1 | 4 2 3
        \\4 2 6 | 8 5 3 | 7 9 1
        \\7 1 3 | 9 2 4 | 8 5 6
        \\------+-------+------
        \\9 6 1 | 5 3 7 | 2 8 4
        \\2 8 7 | 4 1 9 | 6 3 5
        \\3 4 5 | 2 8 6 | 1 7 9
        \\
    );
    test_step.dependOn(&solved.step);

    const oversized_puzzle = b.allocator.alloc(u8, 64 * 1024 + 1) catch @panic("OOM");
    @memset(oversized_puzzle, '.');
    const oversized = b.addRunArtifact(sudoku);
    oversized.setStdIn(.{ .bytes = oversized_puzzle });
    oversized.expectExitCode(2);
    oversized.expectStdErrEqual("sat-sudoku: input is over 64 KiB\n");
    test_step.dependOn(&oversized.step);
}

fn addSolverCliTests(b: *std.Build, target: std.Build.ResolvedTarget, test_step: *std.Build.Step, sat: *std.Build.Step.Compile) void {
    const proof = b.addRunArtifact(sat);
    proof.addArg("--proof");
    _ = proof.addOutputFileArg("trivial_unsat.drat");
    proof.addFileArg(b.path("tests/fixtures/trivial_unsat.cnf"));
    proof.expectExitCode(20);
    proof.expectStdOutEqual("s UNSATISFIABLE\n");
    test_step.dependOn(&proof.step);

    const cli_cases = [_]CliCase{
        .{ .args = &.{"tests/fixtures/trivial_sat.cnf"}, .exit_code = 10 },
        .{ .args = &.{"tests/fixtures/trivial_unsat.cnf"}, .exit_code = 20, .stdout = "s UNSATISFIABLE\n" },
        .{ .args = &.{"tests/fixtures/small_sat.cnf"}, .exit_code = 10 },
        .{ .args = &.{"--bogus"}, .exit_code = 1, .stderr_contains = "sat: unknown option `--bogus`\nusage: sat " },
        .{ .args = &.{"--proof"}, .exit_code = 1, .stderr_contains = "sat: --proof requires a PATH argument\n" },
        .{ .args = &.{"--time-limit"}, .exit_code = 1, .stderr_contains = "sat: --time-limit requires a SECS argument\n" },
        .{ .args = &.{ "--time-limit", "abc" }, .exit_code = 1, .stderr_contains = "sat: --time-limit: invalid integer `abc`\n" },
        .{
            .args = &.{ "tests/fixtures/trivial_sat.cnf", "tests/fixtures/small_sat.cnf" },
            .exit_code = 1,
            .stderr_contains = "sat: only one input path allowed\n",
        },
        .{
            .args = &.{"tests/fixtures/missing.cnf"},
            .exit_code = 1,
            .stderr_contains = "sat: cannot open tests/fixtures/missing.cnf: FileNotFound\n",
        },
        .{ .stdin = "p cnf 1 1\n1 x 0\n", .exit_code = 0, .stdout = "c parse error: InvalidToken\ns UNKNOWN\n" },
        .{ .args = &.{"tests/fixtures/trivial_sat.cnf.gz"}, .exit_code = 10, .stdout = "s SATISFIABLE\nv 1 -2 0\n" },
    };
    for (cli_cases) |case| addCliTest(b, test_step, sat, case);

    if (target.result.os.tag != .linux) return;

    // /dev/full fails every write, standing in for a full disk.
    const linux_cases = [_]CliCase{
        .{
            .args = &.{ "--proof", "/dev/full", "tests/fixtures/trivial_unsat.cnf" },
            .exit_code = 0,
            .stdout = "c error: cannot write proof: NoSpaceLeft\ns UNKNOWN\n",
        },
        // This proof outgrows its buffer, so the write fails during search.
        .{
            .args = &.{ "--proof", "/dev/full", "tests/fixtures/pigeonhole_7_6.cnf" },
            .exit_code = 0,
            .stdout = "c error: cannot write proof: NoSpaceLeft\ns UNKNOWN\n",
        },
    };
    for (linux_cases) |case| addCliTest(b, test_step, sat, case);

    // The address-space cap turns a header-sized allocation into a
    // clean OutOfMemory instead of the OOM killer.
    const huge_header = b.addSystemCommand(&.{ "prlimit", "--as=4294967296", "--" });
    huge_header.addArtifactArg(sat);
    huge_header.setStdIn(.{ .bytes = "p cnf 1073741824 1\n1 0\n" });
    huge_header.expectExitCode(10);
    huge_header.expectStdOutEqual("s SATISFIABLE\nv 1 0\n");
    test_step.dependOn(&huge_header.step);

    const stdout_write_failure = b.addSystemCommand(&.{ "sh", "-c", "exec \"$0\" \"$1\" > /dev/full" });
    stdout_write_failure.addArtifactArg(sat);
    stdout_write_failure.addFileArg(b.path("tests/fixtures/trivial_sat.cnf"));
    stdout_write_failure.expectExitCode(1);
    stdout_write_failure.expectStdErrEqual("sat: cannot write to stdout: NoSpaceLeft\n");
    test_step.dependOn(&stdout_write_failure.step);

    // A model longer than the stdout buffer fails mid-print instead.
    const model_write_failure = b.addSystemCommand(&.{ "sh", "-c", "exec \"$0\" > /dev/full" });
    model_write_failure.addArtifactArg(sat);
    model_write_failure.setStdIn(.{ .bytes = "p cnf 2000 1\n2000 0\n" });
    model_write_failure.expectExitCode(1);
    model_write_failure.expectStdErrEqual("sat: cannot write to stdout: NoSpaceLeft\n");
    test_step.dependOn(&model_write_failure.step);
}

// One run of the `sat` CLI from the build root, checked on its exit code
// and, where given, its whole stdout and a line its stderr must contain.
const CliCase = struct {
    args: []const []const u8 = &.{},
    stdin: ?[]const u8 = null,
    exit_code: u8,
    stdout: ?[]const u8 = null,
    stderr_contains: ?[]const u8 = null,
};

fn addCliTest(b: *std.Build, test_step: *std.Build.Step, exe: *std.Build.Step.Compile, case: CliCase) void {
    const run = b.addRunArtifact(exe);
    run.setCwd(b.path("."));
    run.addArgs(case.args);
    run.setStdIn(.{ .bytes = case.stdin orelse "" });
    run.expectExitCode(case.exit_code);
    if (case.stdout) |out| run.expectStdOutEqual(out);
    if (case.stderr_contains) |line| run.addCheck(.{ .expect_stderr_match = line });
    test_step.dependOn(&run.step);
}

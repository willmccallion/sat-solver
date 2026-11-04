const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // --- Layer module graph ------------------------------------------------
    // Dependency DAG, strictly downward:
    //   core  ←  io
    //   core, io, heuristics  ←  search
    //   everything  ←  tools, main, root (the `sat` public module)
    const core = b.createModule(.{
        .root_source_file = b.path("src/core/mod.zig"),
        .target = target,
        .optimize = optimize,
    });
    const io = b.createModule(.{
        .root_source_file = b.path("src/io/mod.zig"),
        .target = target,
        .optimize = optimize,
    });
    io.addImport("core", core);

    const heuristics = b.createModule(.{
        .root_source_file = b.path("src/heuristics/mod.zig"),
        .target = target,
        .optimize = optimize,
    });

    const search = b.createModule(.{
        .root_source_file = b.path("src/search/mod.zig"),
        .target = target,
        .optimize = optimize,
    });
    search.addImport("core", core);
    search.addImport("io", io);
    search.addImport("heuristics", heuristics);

    const addLayerImports = struct {
        fn apply(
            m: *std.Build.Module,
            c: *std.Build.Module,
            i: *std.Build.Module,
            h: *std.Build.Module,
            s: *std.Build.Module,
        ) void {
            m.addImport("core", c);
            m.addImport("io", i);
            m.addImport("heuristics", h);
            m.addImport("search", s);
        }
    }.apply;

    const exe_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    addLayerImports(exe_module, core, io, heuristics, search);
    const exe = b.addExecutable(.{ .name = "sat", .root_module = exe_module });
    b.installArtifact(exe);

    const bench_module = b.createModule(.{
        .root_source_file = b.path("src/tools/bench.zig"),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    addLayerImports(bench_module, core, io, heuristics, search);
    const bench_exe = b.addExecutable(.{ .name = "sat-bench", .root_module = bench_module });
    b.installArtifact(bench_exe);

    const sudoku_module = b.createModule(.{
        .root_source_file = b.path("src/tools/sudoku.zig"),
        .target = target,
        .optimize = optimize,
    });
    addLayerImports(sudoku_module, core, io, heuristics, search);
    const sudoku_exe = b.addExecutable(.{ .name = "sat-sudoku", .root_module = sudoku_module });
    b.installArtifact(sudoku_exe);

    const sudoku_run = b.addRunArtifact(sudoku_exe);
    sudoku_run.addPassthruArgs();
    const sudoku_step = b.step("sudoku", "Solve a Sudoku (zig build sudoku -- PUZZLE)");
    sudoku_step.dependOn(&sudoku_run.step);

    const bench_release_module = b.createModule(.{
        .root_source_file = b.path("src/tools/bench.zig"),
        .target = target,
        .optimize = .ReleaseFast,
        .strip = false,
    });
    addLayerImports(bench_release_module, core, io, heuristics, search);
    const bench_release_exe = b.addExecutable(.{ .name = "sat-bench", .root_module = bench_release_module });

    const profile_module = b.createModule(.{
        .root_source_file = b.path("src/tools/profile.zig"),
        .target = target,
        .optimize = .Debug,
    });
    addLayerImports(profile_module, core, io, heuristics, search);
    const profile_exe = b.addExecutable(.{ .name = "sat-profile", .root_module = profile_module });

    const profile_run = b.addRunArtifact(profile_exe);
    profile_run.addArtifactArg(bench_release_exe);
    profile_run.addArg("bench/instances/uf200-860");
    profile_run.addArg("bench/instances/uuf200-860");
    profile_run.addArg("bench/instances/uf250-1065");
    profile_run.addArg("bench/instances/uuf250-1065");
    profile_run.has_side_effects = true;
    profile_run.stdio = .inherit;

    const bench_step = b.step("bench", "Run deep perf profile on uf200/uuf200 + uf250/uuf250 (~7 min)");
    bench_step.dependOn(&profile_run.step);

    const compete_module = b.createModule(.{
        .root_source_file = b.path("src/tools/compete.zig"),
        .target = target,
        .optimize = .Debug,
    });
    addLayerImports(compete_module, core, io, heuristics, search);
    const compete_exe = b.addExecutable(.{ .name = "sat-compete", .root_module = compete_module });

    const compete_run = b.addRunArtifact(compete_exe);
    compete_run.addArtifactArg(exe);
    compete_run.addArtifactArg(bench_release_exe);
    compete_run.has_side_effects = true;
    compete_run.stdio = .inherit;

    const compete_step = b.step(
        "compete",
        "Tournament readiness check — submittability + perf vs SAT Competition 2025",
    );
    compete_step.dependOn(&compete_run.step);

    const quick_profile_run = b.addRunArtifact(profile_exe);
    quick_profile_run.addArtifactArg(bench_release_exe);
    quick_profile_run.addArg("bench/instances/uf100-430");
    quick_profile_run.addArg("bench/instances/uuf100-430");
    quick_profile_run.has_side_effects = true;
    quick_profile_run.stdio = .inherit;

    const bench_quick_step = b.step("bench-quick", "Run fast perf profile on uf100 + uuf100 (~4 s)");
    bench_quick_step.dependOn(&quick_profile_run.step);

    const industrial_profile_run = b.addRunArtifact(profile_exe);
    industrial_profile_run.addArtifactArg(bench_release_exe);
    industrial_profile_run.addArg("--timeout-sec");
    industrial_profile_run.addArg("30");
    industrial_profile_run.addArg("bench/instances/dimacs-bf");
    industrial_profile_run.addArg("bench/instances/dimacs-ssa");
    industrial_profile_run.addArg("bench/instances/dimacs-hanoi");
    industrial_profile_run.addArg("bench/instances/dimacs-parity");
    industrial_profile_run.addArg("bench/instances/dimacs-aim");
    industrial_profile_run.has_side_effects = true;
    industrial_profile_run.stdio = .inherit;

    const bench_industrial_step = b.step(
        "bench-industrial",
        "Perf profile on SATLIB crafted (bf/ssa/hanoi/parity/aim) with 30 s cap",
    );
    bench_industrial_step.dependOn(&industrial_profile_run.step);

    const satcomp_profile_run = b.addRunArtifact(profile_exe);
    satcomp_profile_run.addArtifactArg(bench_release_exe);
    satcomp_profile_run.addArg("--timeout-sec");
    satcomp_profile_run.addArg("60");
    satcomp_profile_run.addArg("bench/instances/satcomp2025");
    satcomp_profile_run.has_side_effects = true;
    satcomp_profile_run.stdio = .inherit;

    const bench_satcomp_step = b.step(
        "bench-satcomp",
        "Perf profile on SAT Competition 2025 subset (run bench/fetch_satcomp.sh first)",
    );
    bench_satcomp_step.dependOn(&satcomp_profile_run.step);

    const sat_module = b.addModule("sat", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    addLayerImports(sat_module, core, io, heuristics, search);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    run_cmd.addPassthruArgs();
    const run_step = b.step("run", "Run the sat solver");
    run_step.dependOn(&run_cmd.step);

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
            .imports = &.{
                .{ .name = "sat", .module = sat_module },
            },
        }),
    });
    const run_unit_tests = b.addRunArtifact(unit_tests);
    const unit_step = b.step("unit", "Run only tests/unit.zig (narrow with -Dtest-filter=TEXT)");
    unit_step.dependOn(&run_unit_tests.step);

    const e2e_sat = b.addRunArtifact(exe);
    e2e_sat.addFileArg(b.path("tests/fixtures/trivial_sat.cnf"));
    e2e_sat.expectExitCode(10);

    const e2e_unsat = b.addRunArtifact(exe);
    e2e_unsat.addFileArg(b.path("tests/fixtures/trivial_unsat.cnf"));
    e2e_unsat.expectExitCode(20);
    e2e_unsat.expectStdOutEqual("s UNSATISFIABLE\n");

    const e2e_small = b.addRunArtifact(exe);
    e2e_small.addFileArg(b.path("tests/fixtures/small_sat.cnf"));
    e2e_small.expectExitCode(10);

    const e2e_proof = b.addRunArtifact(exe);
    e2e_proof.addArg("--proof");
    _ = e2e_proof.addOutputFileArg("trivial_unsat.drat");
    e2e_proof.addFileArg(b.path("tests/fixtures/trivial_unsat.cnf"));
    e2e_proof.expectExitCode(20);
    e2e_proof.expectStdOutEqual("s UNSATISFIABLE\n");

    const run_sudoku_tests = b.addRunArtifact(b.addTest(.{ .root_module = sudoku_module }));

    const e2e_sudoku = b.addRunArtifact(sudoku_exe);
    e2e_sudoku.addArg("53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79");
    e2e_sudoku.expectExitCode(0);
    e2e_sudoku.expectStdOutEqual(
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

    const oversized_puzzle = b.allocator.alloc(u8, 64 * 1024 + 1) catch @panic("OOM");
    @memset(oversized_puzzle, '.');
    const e2e_sudoku_oversized = b.addRunArtifact(sudoku_exe);
    e2e_sudoku_oversized.setStdIn(.{ .bytes = oversized_puzzle });
    e2e_sudoku_oversized.expectExitCode(2);
    e2e_sudoku_oversized.expectStdErrEqual("sat-sudoku: input is over 64 KiB\n");

    const test_step = b.step("test", "Run unit tests and end-to-end round-trip");
    test_step.dependOn(&run_unit_tests.step);
    test_step.dependOn(&run_sudoku_tests.step);
    test_step.dependOn(&e2e_sudoku.step);
    test_step.dependOn(&e2e_sudoku_oversized.step);
    test_step.dependOn(&e2e_sat.step);
    test_step.dependOn(&e2e_unsat.step);
    test_step.dependOn(&e2e_small.step);
    test_step.dependOn(&e2e_proof.step);

    if (target.result.os.tag == .linux) {
        // The address-space cap turns a header-sized allocation into a
        // clean OutOfMemory instead of the OOM killer.
        const e2e_huge_header = b.addSystemCommand(&.{ "prlimit", "--as=4294967296", "--" });
        e2e_huge_header.addArtifactArg(exe);
        e2e_huge_header.setStdIn(.{ .bytes = "p cnf 1073741824 1\n1 0\n" });
        e2e_huge_header.expectExitCode(10);
        e2e_huge_header.expectStdOutEqual("s SATISFIABLE\nv 1 0\n");
        test_step.dependOn(&e2e_huge_header.step);

        // /dev/full fails every write, standing in for a full disk.
        const e2e_proof_write_failure = b.addRunArtifact(exe);
        e2e_proof_write_failure.addArgs(&.{ "--proof", "/dev/full" });
        e2e_proof_write_failure.addFileArg(b.path("tests/fixtures/trivial_unsat.cnf"));
        e2e_proof_write_failure.expectExitCode(0);
        e2e_proof_write_failure.expectStdOutEqual("c error: cannot write proof: NoSpaceLeft\ns UNKNOWN\n");
        test_step.dependOn(&e2e_proof_write_failure.step);
    }
}

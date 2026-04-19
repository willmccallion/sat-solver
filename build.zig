const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "sat",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .strip = false,
        }),
    });
    b.installArtifact(exe);

    const bench_exe = b.addExecutable(.{
        .name = "sat-bench",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/bench.zig"),
            .target = target,
            .optimize = optimize,
            .strip = false,
        }),
    });
    b.installArtifact(bench_exe);

    // A dedicated ReleaseFast build of sat-bench used only by `zig build
    // bench` — not installed, so it never shadows the user's optimize choice.
    const bench_release_exe = b.addExecutable(.{
        .name = "sat-bench",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/bench.zig"),
            .target = target,
            .optimize = .ReleaseFast,
            .strip = false,
        }),
    });

    const profile_exe = b.addExecutable(.{
        .name = "sat-profile",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/profile.zig"),
            .target = target,
            .optimize = .Debug,
        }),
    });

    const profile_run = b.addRunArtifact(profile_exe);
    profile_run.addArtifactArg(bench_release_exe);
    // uf200/uuf200 for continuity with prior baselines; uf250/uuf250
    // for instances big enough that restart and clause-DB policy
    // actually move the needle. The uf250 sets are ~8x harder than
    // uf200 and are where adaptive strategies pay for themselves.
    profile_run.addArg("bench/instances/uf200-860");
    profile_run.addArg("bench/instances/uuf200-860");
    profile_run.addArg("bench/instances/uf250-1065");
    profile_run.addArg("bench/instances/uuf250-1065");
    profile_run.has_side_effects = true;
    profile_run.stdio = .inherit;

    const bench_step = b.step("bench", "Run deep perf profile on uf200/uuf200 + uf250/uuf250 (~7 min)");
    bench_step.dependOn(&profile_run.step);

    const compete_exe = b.addExecutable(.{
        .name = "sat-compete",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/compete.zig"),
            .target = target,
            .optimize = .Debug,
        }),
    });

    const compete_run = b.addRunArtifact(compete_exe);
    compete_run.addArtifactArg(exe); // the installed `sat` binary
    compete_run.addArtifactArg(bench_release_exe); // the ReleaseFast `sat-bench`
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

    // bench-industrial — SATLIB crafted instances that behave much
    // more like competition industrial (structure, long chains of
    // implications, learned-clause payoff) than uniform-random 3-SAT.
    // 30 s per-instance cap is short enough for a dev-loop iteration
    // and long enough that something genuinely hard becomes visible.
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

    // bench-satcomp — SAT Competition 2025 main-track subset fetched
    // by `bench/fetch_satcomp.sh`. Requires running that script first
    // (it decompresses xz→cnf into bench/instances/satcomp2025/).
    // 60 s cap keeps a 40-instance subset under an hour worst case.
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

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run the sat solver");
    run_step.dependOn(&run_cmd.step);

    const unit_tests = b.addTest(.{
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

    const test_step = b.step("test", "Run unit tests and end-to-end round-trip");
    test_step.dependOn(&run_unit_tests.step);
    test_step.dependOn(&e2e_sat.step);
    test_step.dependOn(&e2e_unsat.step);
    test_step.dependOn(&e2e_small.step);
}

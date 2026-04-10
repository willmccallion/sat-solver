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

const std = @import("std");
const state = @import("state.zig");

pub const Result = enum { sat, unsat, unknown };

// Global interrupt flag. Set from signal handlers (SIGINT/SIGTERM/SIGXCPU)
// or the --time-limit thread; polled at the top of every solve() iteration.
// On first observed `true`, solve returns .unknown at the next conflict
// boundary so main falls through to `s UNKNOWN`.
pub var interrupted: std.atomic.Value(bool) = .init(false);

// Long preprocessing and inprocessing loops poll this alongside their
// budgets, so a SIGTERM or --time-limit is honoured outside search too.
pub fn interruptRequested() bool {
    return interrupted.load(.monotonic);
}

pub const Solver = state.Solver;
pub const Stats = state.Stats;

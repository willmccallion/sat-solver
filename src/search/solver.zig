const std = @import("std");
const state = @import("state.zig");

pub const Result = enum { sat, unsat, unknown };

// The process-wide interrupt flag, which signal handlers (SIGINT, SIGTERM,
// SIGXCPU) and the --time-limit thread set. A solver obeys it unless its
// `interrupt` points elsewhere.
pub var interrupted: std.atomic.Value(bool) = .init(false);

pub const Solver = state.Solver;
pub const Error = state.Error;
pub const Stats = state.Stats;

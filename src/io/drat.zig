const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;

// DRAT proof emission. A proof is a sequence of clause additions ("a"
// lines, or bare literals) and deletions ("d "-prefixed), terminated by
// the empty clause `0\n` once the solver has derived UNSAT. Checkers
// like drat-trim replay the proof against the input .cnf to verify the
// UNSAT verdict, which most SAT Competition tracks require.
//
// The writer is optional throughout the solver: when no proof was
// requested, `Writer` holds a null `*std.Io.Writer` and every emit
// degrades to a load + branch.

pub const Writer = struct {
    out: ?*std.Io.Writer = null,

    pub fn none() Writer {
        return .{ .out = null };
    }

    pub fn wrap(out: *std.Io.Writer) Writer {
        return .{ .out = out };
    }

    pub fn addClause(self: Writer, lits: []const Literal) !void {
        const w = self.out orelse return;
        for (lits) |lit| try w.print("{d} ", .{lit.toDimacs()});
        try w.writeAll("0\n");
    }

    pub fn deleteClause(self: Writer, lits: []const Literal) !void {
        const w = self.out orelse return;
        try w.writeAll("d ");
        for (lits) |lit| try w.print("{d} ", .{lit.toDimacs()});
        try w.writeAll("0\n");
    }

    pub fn empty(self: Writer) !void {
        const w = self.out orelse return;
        try w.writeAll("0\n");
    }
};

// Open a DRAT proof output file. Caller owns the returned file handle
// and is responsible for closing it (and flushing the writer interface
// via the caller-held buffer).
pub fn openFile(path: []const u8) !std.fs.File {
    return std.fs.cwd().createFile(path, .{});
}

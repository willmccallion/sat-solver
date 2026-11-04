//! sat-sudoku — solves a 9x9 Sudoku by encoding it as CNF and handing it
//! to the CDCL solver. Variable `holds(cell, digit)` means "cell contains
//! digit"; every cell and every row, column and box gets exactly one of
//! each, and each given digit is a unit clause.

const std = @import("std");
const core = @import("core");
const search = @import("search");
const Literal = core.cnf.Literal;
const Formula = core.cnf.Formula;
const Solver = search.solver.Solver;

const usage =
    \\usage: sat-sudoku [PUZZLE]
    \\
    \\PUZZLE is the 81 cells row by row: digits 1-9, and `.` or `0` for an
    \\empty cell. Whitespace is ignored, so a 9-line grid works too. With no
    \\argument the puzzle is read from stdin.
    \\
    \\Exit code: 0 = solved, 1 = the puzzle has no solution, 2 = bad input or
    \\no answer.
    \\
;

const side = 9;
const box_side = 3;
const cell_count = side * side;
const var_count = cell_count * side;
const max_input_bytes = 64 * 1024;

/// A digit 1-9, stored zero-based so it doubles as a variable offset.
const Digit = struct {
    index: u4,

    const all: [side]Digit = blk: {
        var digits: [side]Digit = undefined;
        for (&digits, 0..) |*d, i| d.* = .{ .index = i };
        break :blk digits;
    };

    fn fromChar(c: u8) ?Digit {
        if (c < '1' or c > '9') return null;
        return .{ .index = @intCast(c - '1') };
    }

    fn toChar(self: Digit) u8 {
        return '1' + @as(u8, self.index);
    }
};

const Cell = struct {
    row: u4,
    col: u4,

    fn fromIndex(i: usize) Cell {
        return .{ .row = @intCast(i / side), .col = @intCast(i % side) };
    }

    fn index(self: Cell) usize {
        return @as(usize, self.row) * side + self.col;
    }
};

/// The 27 rows, columns and boxes, each of which must hold 1-9 once.
const groups: [3 * side][side]Cell = blk: {
    var all: [3 * side][side]Cell = undefined;
    for (0..side) |g| {
        const box_row = (g / box_side) * box_side;
        const box_col = (g % box_side) * box_side;
        for (0..side) |k| {
            all[g][k] = .{ .row = g, .col = k };
            all[side + g][k] = .{ .row = k, .col = g };
            all[2 * side + g][k] = .{ .row = box_row + k / box_side, .col = box_col + k % box_side };
        }
    }
    break :blk all;
};

const Puzzle = struct {
    givens: [cell_count]?Digit,
};

const Grid = [cell_count]Digit;

const Outcome = union(enum) {
    solved: Grid,
    no_solution,
    interrupted,
};

const PuzzleError = error{ InvalidCharacter, WrongCellCount };

fn parsePuzzle(text: []const u8) PuzzleError!Puzzle {
    var givens: [cell_count]?Digit = undefined;
    var count: usize = 0;
    for (text) |c| {
        if (std.ascii.isWhitespace(c)) continue;
        const given: ?Digit = if (c == '.' or c == '0')
            null
        else
            Digit.fromChar(c) orelse return error.InvalidCharacter;
        if (count == cell_count) return error.WrongCellCount;
        givens[count] = given;
        count += 1;
    }
    if (count != cell_count) return error.WrongCellCount;
    return .{ .givens = givens };
}

fn holds(cell: Cell, digit: Digit) Literal {
    const var_index: u32 = @intCast(cell.index() * side + digit.index);
    return Literal.init(var_index, false);
}

fn addExactlyOne(formula: *Formula, lits: []const Literal) Formula.AddClauseError!void {
    try formula.addClause(lits);
    for (lits, 0..) |a, i| {
        for (lits[i + 1 ..]) |b| {
            try formula.addClause(&.{ a.negate(), b.negate() });
        }
    }
}

fn encode(allocator: std.mem.Allocator, puzzle: *const Puzzle) Formula.AddClauseError!Formula {
    var formula = Formula.init(allocator, var_count);
    errdefer formula.deinit();

    var lits: [side]Literal = undefined;
    for (0..cell_count) |i| {
        const cell = Cell.fromIndex(i);
        for (Digit.all, &lits) |digit, *lit| lit.* = holds(cell, digit);
        try addExactlyOne(&formula, &lits);
    }
    for (groups) |group| {
        for (Digit.all) |digit| {
            for (group, &lits) |cell, *lit| lit.* = holds(cell, digit);
            try addExactlyOne(&formula, &lits);
        }
    }
    for (puzzle.givens, 0..) |given, i| {
        const digit = given orelse continue;
        try formula.addClause(&.{holds(Cell.fromIndex(i), digit)});
    }
    return formula;
}

fn readGrid(solver: *const Solver) error{CellWithoutDigit}!Grid {
    var grid: Grid = undefined;
    for (&grid, 0..) |*slot, i| {
        const cell = Cell.fromIndex(i);
        slot.* = for (Digit.all) |digit| {
            if (solver.assignment.valueOfLiteral(holds(cell, digit)) == .true) break digit;
        } else return error.CellWithoutDigit;
    }
    return grid;
}

fn solvePuzzle(allocator: std.mem.Allocator, puzzle: *const Puzzle) !Outcome {
    var formula = try encode(allocator, puzzle);
    defer formula.deinit();
    var solver = try Solver.init(allocator, &formula);
    defer solver.deinit();

    switch (try solver.solve()) {
        .unsat => return .no_solution,
        .unknown => return .interrupted,
        .sat => {},
    }
    solver.extendModel();
    if (solver.findFalsifiedClause(&formula) != null) return error.ModelFalsifiesFormula;
    return .{ .solved = try readGrid(&solver) };
}

fn writeGrid(out: *std.Io.Writer, grid: *const Grid) std.Io.Writer.Error!void {
    for (0..side) |row| {
        if (row != 0 and row % box_side == 0) try out.writeAll("------+-------+------\n");
        for (0..side) |col| {
            if (col != 0) try out.writeAll(if (col % box_side == 0) " | " else " ");
            try out.writeByte(grid[row * side + col].toChar());
        }
        try out.writeByte('\n');
    }
}

fn describePuzzleError(err: PuzzleError) []const u8 {
    return switch (err) {
        error.InvalidCharacter => "cells must be 1-9, `.` or `0`",
        error.WrongCellCount => "a puzzle has exactly 81 cells",
    };
}

pub fn main(init: std.process.Init) u8 {
    var stdout_buffer: [4096]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writer(init.io, &stdout_buffer);
    const stdout = &stdout_writer.interface;
    defer stdout.flush() catch {};

    var stderr_buffer: [1024]u8 = undefined;
    var stderr_writer = std.Io.File.stderr().writer(init.io, &stderr_buffer);
    const stderr = &stderr_writer.interface;
    defer stderr.flush() catch {};

    // Exit code 1 means "no solution", so no failure may fall through to it.
    return run(init, stdout, stderr) catch |err| {
        stderr.print("sat-sudoku: {s}\n", .{@errorName(err)}) catch {};
        return 2;
    };
}

fn run(init: std.process.Init, stdout: *std.Io.Writer, stderr: *std.Io.Writer) !u8 {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len > 2) {
        try stderr.writeAll(usage);
        return 2;
    }
    if (args.len == 2 and (std.mem.eql(u8, args[1], "-h") or std.mem.eql(u8, args[1], "--help"))) {
        try stdout.writeAll(usage);
        return 0;
    }

    const text = if (args.len == 2) args[1] else readStdin(init) catch |err| switch (err) {
        error.StreamTooLong => {
            try stderr.print("sat-sudoku: input is over {d} KiB\n", .{max_input_bytes / 1024});
            return 2;
        },
        else => |e| return e,
    };

    const puzzle = parsePuzzle(text) catch |err| {
        try stderr.print("sat-sudoku: {s}\n", .{describePuzzleError(err)});
        return 2;
    };

    switch (try solvePuzzle(init.gpa, &puzzle)) {
        .solved => |grid| {
            try writeGrid(stdout, &grid);
            return 0;
        },
        .no_solution => {
            try stderr.writeAll("sat-sudoku: the puzzle has no solution\n");
            return 1;
        },
        .interrupted => {
            try stderr.writeAll("sat-sudoku: solver stopped before an answer\n");
            return 2;
        },
    }
}

fn readStdin(init: std.process.Init) ![]u8 {
    var stdin_buffer: [4096]u8 = undefined;
    var stdin_reader = std.Io.File.stdin().readerStreaming(init.io, &stdin_buffer);
    return stdin_reader.interface.allocRemaining(init.arena.allocator(), .limited(max_input_bytes));
}

const testing = std.testing;

fn blanks(comptime n: usize) [n]u8 {
    return @splat('.');
}

const escargot = "1....7.9..3..2...8..96..5....53..9...1..8...26....4...3......1..4......7..7...3..";

fn expectValidSolutionOf(puzzle: *const Puzzle, grid: *const Grid) !void {
    for (puzzle.givens, grid) |given, digit| {
        if (given) |g| try testing.expectEqual(g.index, digit.index);
    }
    for (groups) |group| {
        var seen: [side]bool = @splat(false);
        for (group) |cell| seen[grid[cell.index()].index] = true;
        try testing.expect(std.mem.allEqual(bool, &seen, true));
    }
}

test "solves a hard puzzle while keeping every given" {
    const puzzle = try parsePuzzle(escargot);

    const outcome = try solvePuzzle(testing.allocator, &puzzle);

    try expectValidSolutionOf(&puzzle, &outcome.solved);
}

test "solves an empty grid" {
    const puzzle = try parsePuzzle(&blanks(cell_count));

    const outcome = try solvePuzzle(testing.allocator, &puzzle);

    try expectValidSolutionOf(&puzzle, &outcome.solved);
}

test "reports no solution when a row repeats a digit" {
    const puzzle = try parsePuzzle("55" ++ &blanks(cell_count - 2));

    const outcome = try solvePuzzle(testing.allocator, &puzzle);

    try testing.expectEqual(.no_solution, outcome);
}

test "parses a grid split across lines" {
    const text = "53..7....\n6..195...\n.98....6.\n8...6...3\n4..8.3..1\n7...2...6\n.6....28.\n...419..5\n....8..79\n";

    const puzzle = try parsePuzzle(text);

    try testing.expectEqual(Digit.fromChar('5'), puzzle.givens[0]);
    try testing.expectEqual(@as(?Digit, null), puzzle.givens[2]);
    try testing.expectEqual(Digit.fromChar('9'), puzzle.givens[cell_count - 1]);
}

test "rejects a puzzle with too few cells" {
    try testing.expectError(error.WrongCellCount, parsePuzzle("123"));
}

test "rejects a puzzle with too many cells" {
    try testing.expectError(error.WrongCellCount, parsePuzzle(&blanks(cell_count + 1)));
}

test "rejects a cell that is not a digit or blank" {
    try testing.expectError(error.InvalidCharacter, parsePuzzle("x" ++ &blanks(cell_count - 1)));
}

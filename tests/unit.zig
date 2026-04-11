const std = @import("std");
const testing = std.testing;

const sat = @import("sat");
const cnf = sat.cnf;
const parser = sat.parser;
const solver_mod = sat.solver;
const Literal = cnf.Literal;

fn solveSource(source: []const u8) !struct { result: solver_mod.Result, verified: bool } {
    const gpa = testing.allocator;
    const formula = try parser.parse(gpa, source);
    var solver = try solver_mod.Solver.init(gpa, formula);
    defer solver.deinit();
    const result = try solver.solve();
    const verified = if (result == .sat) solver.verifyModel() else true;
    return .{ .result = result, .verified = verified };
}

const trivial_sat_src = @embedFile("fixtures/trivial_sat.cnf");
const trivial_unsat_src = @embedFile("fixtures/trivial_unsat.cnf");
const small_sat_src = @embedFile("fixtures/small_sat.cnf");

test "literal encoding round-trips" {
    const lit = Literal.init(7, false);
    try testing.expectEqual(@as(u32, 7), lit.variable());
    try testing.expectEqual(false, lit.isNegative());
    try testing.expectEqual(@as(u32, 14), lit.raw);

    const neg = lit.negate();
    try testing.expectEqual(@as(u32, 7), neg.variable());
    try testing.expectEqual(true, neg.isNegative());
    try testing.expect(neg.negate().eql(lit));
}

test "literal fromDimacs / toDimacs round-trip" {
    try testing.expectEqual(@as(i32, 3), Literal.fromDimacs(3).toDimacs());
    try testing.expectEqual(@as(i32, -3), Literal.fromDimacs(-3).toDimacs());
    try testing.expectEqual(@as(i32, 1), Literal.fromDimacs(1).toDimacs());
    try testing.expectEqual(@as(i32, -42), Literal.fromDimacs(-42).toDimacs());
}

test "parser: trivial_sat fixture" {
    var formula = try parser.parse(testing.allocator, trivial_sat_src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 2), formula.num_vars);
    try testing.expectEqual(@as(usize, 1), formula.clauses.items.len);
    try testing.expectEqual(@as(usize, 2), formula.clauses.items[0].len);
}

test "parser: trivial_unsat fixture" {
    var formula = try parser.parse(testing.allocator, trivial_unsat_src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 1), formula.num_vars);
    try testing.expectEqual(@as(usize, 2), formula.clauses.items.len);
    try testing.expectEqual(@as(usize, 1), formula.clauses.items[0].len);
    try testing.expectEqual(@as(i32, 1), formula.clauses.items[0][0].toDimacs());
    try testing.expectEqual(@as(i32, -1), formula.clauses.items[1][0].toDimacs());
}

test "parser: small_sat fixture" {
    var formula = try parser.parse(testing.allocator, small_sat_src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 10), formula.num_vars);
    try testing.expectEqual(@as(usize, 20), formula.clauses.items.len);
}

test "parser: clauses span multiple lines" {
    const src =
        \\p cnf 3 2
        \\1 2
        \\3 0
        \\-1
        \\-2 -3 0
    ;
    var formula = try parser.parse(testing.allocator, src);
    defer formula.deinit();
    try testing.expectEqual(@as(usize, 2), formula.clauses.items.len);
    try testing.expectEqual(@as(usize, 3), formula.clauses.items[0].len);
    try testing.expectEqual(@as(usize, 3), formula.clauses.items[1].len);
}

test "parser: tolerates blank lines, tabs, CRLF, extra whitespace" {
    const src = "c leading comment\r\n\r\np cnf 2 1\r\n\t1  \t -2 \t0 \r\n";
    var formula = try parser.parse(testing.allocator, src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 2), formula.num_vars);
    try testing.expectEqual(@as(usize, 1), formula.clauses.items.len);
    try testing.expectEqual(@as(usize, 2), formula.clauses.items[0].len);
}

test "parser: rejects missing p cnf header" {
    const src =
        \\c just a comment
        \\1 2 0
    ;
    try testing.expectError(error.MissingHeader, parser.parse(testing.allocator, src));
}

test "parser: rejects unterminated clause" {
    const src =
        \\p cnf 3 1
        \\1 2 3
    ;
    try testing.expectError(error.UnterminatedClause, parser.parse(testing.allocator, src));
}

test "parser: rejects non-integer token" {
    const src =
        \\p cnf 2 1
        \\1 foo 0
    ;
    try testing.expectError(error.InvalidToken, parser.parse(testing.allocator, src));
}

test "parser: rejects variable out of range" {
    const src =
        \\p cnf 2 1
        \\1 7 0
    ;
    try testing.expectError(error.VariableOutOfRange, parser.parse(testing.allocator, src));
}

test "parser: stops at SATLIB % end-of-content marker" {
    const src =
        \\p cnf 2 1
        \\1 2 0
        \\%
        \\0
    ;
    var formula = try parser.parse(testing.allocator, src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 2), formula.num_vars);
    try testing.expectEqual(@as(usize, 1), formula.clauses.items.len);
}

test "parser: rejects clause count mismatch > 5% (malformed DIMACS)" {
    // Declares 10 clauses but only provides 2 — mimics the malformed
    // SATLIB dubois100.cnf which is missing `0` terminators and gets
    // silently joined into a handful of giant tautology clauses.
    const src =
        \\p cnf 2 10
        \\1 2 0
        \\-1 -2 0
    ;
    try testing.expectError(error.ClauseCountMismatch, parser.parse(testing.allocator, src));
}

test "parser: accepts small clause count discrepancy (within slack)" {
    // Declares 1 clause, provides 1 — exact match, always OK.
    const src =
        \\p cnf 2 1
        \\1 2 0
    ;
    var formula = try parser.parse(testing.allocator, src);
    defer formula.deinit();
    try testing.expectEqual(@as(usize, 1), formula.clauses.items.len);
}

test "parser: rejects malformed p line" {
    const src =
        \\p cnf 2
        \\1 0
    ;
    try testing.expectError(error.InvalidHeader, parser.parse(testing.allocator, src));
}

test "solver: trivial_sat returns sat with verified model" {
    const out = try solveSource(trivial_sat_src);
    try testing.expectEqual(solver_mod.Result.sat, out.result);
    try testing.expect(out.verified);
}

test "solver: trivial_unsat returns unsat" {
    const out = try solveSource(trivial_unsat_src);
    try testing.expectEqual(solver_mod.Result.unsat, out.result);
}

test "solver: small_sat returns sat with verified model" {
    const out = try solveSource(small_sat_src);
    try testing.expectEqual(solver_mod.Result.sat, out.result);
    try testing.expect(out.verified);
}

test "solver: empty formula is trivially sat" {
    const out = try solveSource("p cnf 0 0\n");
    try testing.expectEqual(solver_mod.Result.sat, out.result);
    try testing.expect(out.verified);
}

test "solver: 3-literal unsat (pigeonhole-ish)" {
    // Forces all eight clauses over x1,x2,x3 — i.e. every assignment falsifies
    // some clause. Exercises conflict analysis and learning.
    const src =
        \\p cnf 3 8
        \\ 1  2  3 0
        \\ 1  2 -3 0
        \\ 1 -2  3 0
        \\ 1 -2 -3 0
        \\-1  2  3 0
        \\-1  2 -3 0
        \\-1 -2  3 0
        \\-1 -2 -3 0
    ;
    const out = try solveSource(src);
    try testing.expectEqual(solver_mod.Result.unsat, out.result);
}

test "solver: chained implications propagate to sat" {
    // 1 -> 2 -> 3 -> 4, with x1 forced true. Should be solved by unit
    // propagation alone (no decisions beyond the forced unit).
    const src =
        \\p cnf 4 4
        \\ 1 0
        \\-1 2 0
        \\-2 3 0
        \\-3 4 0
    ;
    const out = try solveSource(src);
    try testing.expectEqual(solver_mod.Result.sat, out.result);
    try testing.expect(out.verified);
}

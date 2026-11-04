const std = @import("std");
const testing = std.testing;

const sat = @import("sat");
const cnf = sat.cnf;
const parser = sat.parser;
const solver_mod = sat.solver;
const clause_mod = sat.clause;
const assignment_mod = sat.assignment;
const Literal = cnf.Literal;
const ClauseRef = cnf.ClauseRef;
const Reason = assignment_mod.Reason;

fn parseSource(source: []const u8) !cnf.Formula {
    var reader: std.Io.Reader = .fixed(source);
    return parser.parse(testing.allocator, &reader);
}

// `verified` checks the model against every clause of `source` as
// written, independently of the parser and the solver's clause database.
fn solveSource(source: []const u8) !struct { result: solver_mod.Result, verified: bool } {
    const gpa = testing.allocator;
    var formula = try parseSource(source);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();
    const result = try solver.solve();
    if (result != .sat) return .{ .result = result, .verified = true };
    solver.extendModel();
    return .{ .result = result, .verified = modelSatisfiesSource(&solver, source) };
}

fn modelSatisfiesSource(solver: *solver_mod.Solver, source: []const u8) bool {
    var clause_satisfied = false;
    var lines = std.mem.tokenizeScalar(u8, source, '\n');
    while (lines.next()) |line| {
        if (line.len == 0 or line[0] == 'c' or line[0] == 'p') continue;
        var tokens = std.mem.tokenizeAny(u8, line, " \t\r");
        while (tokens.next()) |token| {
            const dimacs = std.fmt.parseInt(i32, token, 10) catch return false;
            if (dimacs == 0) {
                if (!clause_satisfied) return false;
                clause_satisfied = false;
                continue;
            }
            const value = solver.assignment.valueOfLiteral(Literal.fromDimacs(dimacs));
            if (value == .true) clause_satisfied = true;
        }
    }
    return true;
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
    var formula = try parseSource(trivial_sat_src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 2), formula.num_vars);
    try testing.expectEqual(@as(usize, 1), formula.clauseCount());
    try testing.expectEqual(@as(usize, 2), formula.clause(0).len);
}

test "parser: trivial_unsat fixture" {
    var formula = try parseSource(trivial_unsat_src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 1), formula.num_vars);
    try testing.expectEqual(@as(usize, 2), formula.clauseCount());
    try testing.expectEqual(@as(usize, 1), formula.clause(0).len);
    try testing.expectEqual(@as(i32, 1), formula.clause(0)[0].toDimacs());
    try testing.expectEqual(@as(i32, -1), formula.clause(1)[0].toDimacs());
}

test "parser: small_sat fixture" {
    var formula = try parseSource(small_sat_src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 10), formula.num_vars);
    try testing.expectEqual(@as(usize, 20), formula.clauseCount());
}

test "parser: tokens split across reader refills parse the same as one buffer" {
    var buffer: [16]u8 = undefined;
    var chunked: std.testing.Reader = .init(&buffer, &.{.{ .buffer = small_sat_src }});
    chunked.artificial_limit = .limited(3);
    var expected = try parseSource(small_sat_src);
    defer expected.deinit();

    var formula = try parser.parse(testing.allocator, &chunked.interface);
    defer formula.deinit();

    try testing.expectEqual(expected.num_vars, formula.num_vars);
    try testing.expectEqualSlices(u32, expected.clause_ends.items, formula.clause_ends.items);
    try testing.expectEqualSlices(Literal, expected.literals.items, formula.literals.items);
}

test "parser: clauses span multiple lines" {
    const src =
        \\p cnf 3 2
        \\1 2
        \\3 0
        \\-1
        \\-2 -3 0
    ;
    var formula = try parseSource(src);
    defer formula.deinit();
    try testing.expectEqual(@as(usize, 2), formula.clauseCount());
    try testing.expectEqual(@as(usize, 3), formula.clause(0).len);
    try testing.expectEqual(@as(usize, 3), formula.clause(1).len);
}

test "parser: tolerates blank lines, tabs, CRLF, extra whitespace" {
    const src = "c leading comment\r\n\r\np cnf 2 1\r\n\t1  \t -2 \t0 \r\n";
    var formula = try parseSource(src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 2), formula.num_vars);
    try testing.expectEqual(@as(usize, 1), formula.clauseCount());
    try testing.expectEqual(@as(usize, 2), formula.clause(0).len);
}

test "parser: rejects missing p cnf header" {
    const src =
        \\c just a comment
        \\1 2 0
    ;
    try testing.expectError(error.MissingHeader, parseSource(src));
}

test "parser: rejects unterminated clause" {
    const src =
        \\p cnf 3 1
        \\1 2 3
    ;
    try testing.expectError(error.UnterminatedClause, parseSource(src));
}

test "parser: rejects non-integer token" {
    const src =
        \\p cnf 2 1
        \\1 foo 0
    ;
    try testing.expectError(error.InvalidToken, parseSource(src));
}

test "parser: rejects variable out of range" {
    const src =
        \\p cnf 2 1
        \\1 7 0
    ;
    try testing.expectError(error.VariableOutOfRange, parseSource(src));
}

test "parser: stops at SATLIB % end-of-content marker" {
    const src =
        \\p cnf 2 1
        \\1 2 0
        \\%
        \\0
    ;
    var formula = try parseSource(src);
    defer formula.deinit();
    try testing.expectEqual(@as(u32, 2), formula.num_vars);
    try testing.expectEqual(@as(usize, 1), formula.clauseCount());
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
    try testing.expectError(error.ClauseCountMismatch, parseSource(src));
}

test "parser: accepts small clause count discrepancy (within slack)" {
    // Declares 1 clause, provides 1 — exact match, always OK.
    const src =
        \\p cnf 2 1
        \\1 2 0
    ;
    var formula = try parseSource(src);
    defer formula.deinit();
    try testing.expectEqual(@as(usize, 1), formula.clauseCount());
}

test "parser: drops tautological clauses but counts them against the header" {
    const src =
        \\p cnf 3 2
        \\1 -1 3 0
        \\2 3 0
    ;
    var formula = try parseSource(src);
    defer formula.deinit();
    try testing.expectEqual(@as(usize, 1), formula.clauseCount());
    try testing.expectEqual(@as(usize, 2), formula.clause(0).len);
}

test "parser: merges duplicate literals within a clause" {
    const src =
        \\p cnf 3 1
        \\2 -3 2 2 0
    ;
    var formula = try parseSource(src);
    defer formula.deinit();
    const clause = formula.clause(0);
    try testing.expectEqual(@as(usize, 2), clause.len);
    try testing.expect(clause[0].eql(Literal.fromDimacs(2)));
    try testing.expect(clause[1].eql(Literal.fromDimacs(-3)));
}

test "parser: rejects malformed p line" {
    const src =
        \\p cnf 2
        \\1 0
    ;
    try testing.expectError(error.InvalidHeader, parseSource(src));
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

test "solver: tautological and duplicate-literal clauses yield a correct model" {
    // Fuzzer-minimized. Treating (-2 1 2) as a subsumer once produced the
    // model -1 -2 -3, which falsifies (2 3 1).
    const src =
        \\p cnf 3 4
        \\3 -1 -1 0
        \\-2 1 2 0
        \\2 3 1 0
        \\-3 -3 2 0
    ;
    const out = try solveSource(src);
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

// Count non-deleted clauses in the arena by walking headers.
fn countLiveLongClauses(solver: *solver_mod.Solver) usize {
    var live: usize = 0;
    var cref: ClauseRef = 0;
    while (cref < solver.arena.items.len) {
        const header = solver.arena.items[cref].raw;
        const len = header & clause_mod.len_mask;
        const span = clause_mod.header_slots + len;
        if ((header & clause_mod.deleted_bit) == 0) live += 1;
        cref += span;
    }
    return live;
}

// True iff bin_watchers contains a binary clause {a, b}. Matches the
// registration invariant: the binary appears as {.other = b} in
// bin_watchers[a.negate().raw].
fn hasBinary(solver: *solver_mod.Solver, a: Literal, b: Literal) bool {
    for (solver.bin_watchers[a.negate().raw].items) |entry| {
        if (entry.other.raw == b.raw) return true;
    }
    return false;
}

test "equiv: a literal equivalent to its negation is refuted with a RUP unit first" {
    // 1 ≡ 2 and 1 ≡ ¬2 put 1 and ¬1 in one SCC of the implication graph.
    const src =
        \\p cnf 2 4
        \\-1 2 0
        \\1 -2 0
        \\-1 -2 0
        \\1 2 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();
    var proof_buffer: [64]u8 = undefined;
    var proof: std.Io.Writer = .fixed(&proof_buffer);
    solver.setProofWriter(&proof);
    _ = try solver.propagate();

    const r = try solver.equiv();

    try testing.expectEqual(solver_mod.Result.unsat, r.?);
    try testing.expectEqualStrings("-1 0\n0\n", proof.buffered());
}

// True iff the `var_idx`-th variable has been marked eliminated by BVE.
fn hasEliminated(solver: *solver_mod.Solver, var_idx: u32) bool {
    return solver.eliminated.isSet(var_idx);
}

test "subsume: trivial — (1 2 3) subsumed by (1 2)" {
    // (1 2) is stored as a binary in bin_watchers; (1 2 3) is the only
    // long clause in the arena. preprocessSubsume should mark (1 2 3)
    // deleted via the binary-subsumer pass.
    const src =
        \\p cnf 3 2
        \\1 2 3 0
        \\1 2 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    _ = try solver.propagate();

    const r = try solver.preprocessSubsume();
    try testing.expect(r == null);

    try testing.expectEqual(@as(usize, 0), countLiveLongClauses(&solver));
    try testing.expect(hasBinary(&solver, Literal.fromDimacs(1), Literal.fromDimacs(2)));
    try testing.expectEqual(@as(u64, 1), solver.stats.subsumed_clauses);
}

test "subsume: learned clause that subsumes an irredundant clause survives reduceDB" {
    const src =
        \\p cnf 4 1
        \\1 2 3 4 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();
    // reduceDB drops the worse half by LBD, so with the subsumer at LBD 9
    // and a bystander at LBD 3 the subsumer is the one it would pick.
    const subsumer_lits = [_]Literal{ Literal.fromDimacs(1), Literal.fromDimacs(2), Literal.fromDimacs(3) };
    const bystander_lits = [_]Literal{ Literal.fromDimacs(-1), Literal.fromDimacs(-2), Literal.fromDimacs(-4) };
    const subsumer = try solver.addClauseToArena(&subsumer_lits, true, 9);
    const bystander = try solver.addClauseToArena(&bystander_lits, true, 3);
    try solver.learned_clauses.appendSlice(gpa, &.{ subsumer, bystander });
    try solver.attachWatches(subsumer);
    try solver.attachWatches(bystander);
    _ = try solver.propagate();

    const r = try solver.preprocessSubsume();
    try solver.reduceDB();

    try testing.expect(r == null);
    try testing.expect(!solver.clauseIsDeleted(subsumer));
    try testing.expect(!solver.clauseIsLearned(subsumer));
    try testing.expectEqual(@as(usize, 2), countLiveLongClauses(&solver));
}

test "subsume: SSR to unit — (1 2) and (1 -2) derive unit 1" {
    // Binary subsumer (1, 2) resolves with its sibling (1, -2) on 2 to
    // derive the level-0 unit (1). Both binaries should leave
    // bin_watchers, stats.strengthened_clauses increments.
    const src =
        \\p cnf 2 2
        \\1 2 0
        \\1 -2 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    _ = try solver.propagate();

    const r = try solver.preprocessSubsume();
    try testing.expect(r == null);

    try testing.expectEqual(assignment_mod.Value.true, solver.assignment.valueOfVar(0));
    try testing.expect(solver.stats.strengthened_clauses >= 1);
}

test "subsume: SSR to binary — long clause strengthened to a new binary" {
    // SSR case: binary (1 -2) resolves with the 3-literal clause
    // (1 2 -34) on variable 2 to derive the binary (1 -34). The old
    // 3-literal clause gets the deleted bit set, and the new binary is
    // registered in bin_watchers.
    //
    // The smallest case, (1 2 3) with (1 -2) giving (1 3), never reaches
    // SSR, for two reasons:
    //   (a) the subsumption-style abstract fast-reject
    //       `(abstract(C) & ~abstract(D)) != 0` inside
    //       processSubsumerBinary. The abstract uses `lit.raw & 63` so
    //       a bit-collision between the C-literal being flipped and
    //       some D-literal is required for the check to pass on an SSR
    //       pair. Variable 33 (dimacs -34, raw=67 → bit 67 & 63 = 3)
    //       supplies that collision against dimacs -2 (raw=3).
    //   (b) pivot selection picks the shorter occ list among the
    //       binary's two literals. With only one other long clause,
    //       occ[dimacs-2] is empty and gets picked, so (1 2 -34) is
    //       never walked. The extra clause (-2 5 6) balances the pivot
    //       tie so occ[dimacs1] is chosen and (1 2 -34) is discovered.
    //
    // With both workarounds in place the SSR fires exactly once and
    // produces the expected binary.
    const src =
        \\p cnf 34 3
        \\1 2 -34 0
        \\1 -2 0
        \\-2 5 6 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    // Locate the cref of (1 2 -34) before subsume — it's the first
    // length-3 clause added to the arena.
    var cref_long: ClauseRef = std.math.maxInt(u32);
    {
        var cref: ClauseRef = 0;
        while (cref < solver.arena.items.len) {
            const header = solver.arena.items[cref].raw;
            const len = header & clause_mod.len_mask;
            const span = clause_mod.header_slots + len;
            if ((header & clause_mod.deleted_bit) == 0 and len == 3) {
                const lits = solver.clauseLits(cref);
                if (lits[0].toDimacs() == 1 and
                    lits[1].toDimacs() == 2 and
                    lits[2].toDimacs() == -34)
                {
                    cref_long = cref;
                    break;
                }
            }
            cref += span;
        }
    }
    try testing.expect(cref_long != std.math.maxInt(u32));

    _ = try solver.propagate();

    const r = try solver.preprocessSubsume();
    try testing.expect(r == null);

    // The long clause must be marked deleted.
    try testing.expect(solver.clauseIsDeleted(cref_long));

    // bin_watchers must contain the new binary (1, -34).
    try testing.expect(hasBinary(
        &solver,
        Literal.fromDimacs(1),
        Literal.fromDimacs(-34),
    ));

    try testing.expectEqual(@as(u64, 1), solver.stats.strengthened_clauses);
}

test "subsume: deleted-skip — two calls don't re-process deleted clauses" {
    // (1 2 3) gets subsumed by (1 2) on the first call. A second call
    // must walk the arena without re-emitting deletes or tripping any
    // assertions inside checkSubsumeOrSSR / strengthenLongClause.
    const src =
        \\p cnf 3 2
        \\1 2 3 0
        \\1 2 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    _ = try solver.propagate();

    const r1 = try solver.preprocessSubsume();
    try testing.expect(r1 == null);
    const subsumed_after_first = solver.stats.subsumed_clauses;
    try testing.expect(subsumed_after_first >= 1);

    const r2 = try solver.preprocessSubsume();
    try testing.expect(r2 == null);
    // Stats may not increment further; at minimum the call must not
    // crash or produce unsat.
    try testing.expectEqual(subsumed_after_first, solver.stats.subsumed_clauses);
}

test "subsume: a level-0 reason clause is never a subsumption target" {
    // The units make (1 2 3 4) the reason for 1; (1 2 3) subsumes it.
    const src =
        \\p cnf 4 5
        \\1 2 3 4 0
        \\1 2 3 0
        \\-2 0
        \\-3 0
        \\-4 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    const locked_cref: ClauseRef = 0;
    try testing.expectEqual(@as(u32, 4), solver.clauseLen(locked_cref));

    // Propagate the units so BCP locks (1 2 3 4) as the reason for 1.
    const conflict = try solver.propagate();
    try testing.expect(conflict == null);

    // Confirm the setup actually locked the clause via a long-clause
    // reason. (Binary reasons are tagged differently and wouldn't lock
    // a long clause.)
    const v0_info = solver.assignment.vars[0];
    try testing.expectEqual(assignment_mod.Value.true, v0_info.value);
    try testing.expectEqual(@as(u32, 0), v0_info.level);
    try testing.expect(!v0_info.reason.isNone());
    try testing.expect(!v0_info.reason.isBinary());
    try testing.expectEqual(locked_cref, v0_info.reason.clauseRef());

    const r = try solver.preprocessSubsume();
    try testing.expect(r == null);

    try testing.expect(!solver.clauseIsDeleted(locked_cref));
}

test "subsume: unsat — (1 2), (1 -2), (-1) derives contradiction" {
    // SSR derives the unit (1) from (1 2) ⊕ (1 -2). With (-1) also in
    // the formula, the level-0 propagation that subsume runs at the
    // end finds the conflict and returns .unsat.
    const src =
        \\p cnf 2 3
        \\1 2 0
        \\1 -2 0
        \\-1 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    // Propagate the (-1) unit first so BCP is at fixpoint before
    // preprocessSubsume is invoked (invariant required by subsume).
    _ = try solver.propagate();

    const r = try solver.preprocessSubsume();
    try testing.expectEqual(solver_mod.Result.unsat, r.?);
}

test "bve: resolves (1 2) and (-1 3) into (2 3)" {
    // Vars 2 and 3 each occur in two -2 / -3 clauses, so var 1 has the
    // smallest occurrence product among the non-pure variables and is
    // resolved before 2 and 3 become pure. Vars 4..11 are pure from the
    // start and go first with zero resolvents.
    const src =
        \\p cnf 11 6
        \\1 2 0
        \\-1 3 0
        \\-2 4 5 0
        \\-2 6 7 0
        \\-3 8 9 0
        \\-3 10 11 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    _ = try solver.propagate();

    const r = try solver.preprocessBVE();
    try testing.expect(r == null);

    try testing.expect(hasEliminated(&solver, 0));
    try testing.expectEqual(@as(u64, 1), solver.stats.resolvents_added);
}

test "bve: growth skip — eliminating a var would create more resolvents than originals" {
    // Two +1 clauses and two -1 clauses, chosen so none of the four
    // resolvents is tautological and all are length ≤ 16. 2+2 originals
    // vs 4 resolvents: 4 > 2+2+0 so the growth test skips the variable.
    //
    // +1 clauses: (1 2 3), (1 4 5)     — longs go to the arena
    // -1 clauses: (-1 6 7), (-1 8 9)
    // Resolvents over var 1: (2,3,6,7), (2,3,8,9), (4,5,6,7), (4,5,8,9)
    // All distinct, no tautology, length 4 ≤ 16. 4 > 4 → skip var 1.
    const src =
        \\p cnf 9 4
        \\1 2 3 0
        \\1 4 5 0
        \\-1 6 7 0
        \\-1 8 9 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    _ = try solver.propagate();

    const r = try solver.preprocessBVE();
    try testing.expect(r == null);

    try testing.expect(!hasEliminated(&solver, 0));
}

test "bve: length cap — resolvent would exceed max_resolvent_len, skip" {
    // Pair one +1 clause of length 9 with one -1 clause of length 9,
    // all variables distinct, so the unique resolvent has length 16.
    // That's ≤ 16, still allowed. Bump to length 10 × length 9 → 17,
    // which trips the cap and forces abandonment.
    const src =
        \\p cnf 19 2
        \\1 2 3 4 5 6 7 8 9 10 0
        \\-1 11 12 13 14 15 16 17 18 19 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    _ = try solver.propagate();

    const r = try solver.preprocessBVE();
    try testing.expect(r == null);

    try testing.expect(!hasEliminated(&solver, 0));
}

test "bve: unsat — (1), (-1) derives the empty clause" {
    // Two singleton clauses contradict directly. Either BVE sees both
    // and returns .unsat, or upstream propagate catches the conflict
    // before preprocessBVE runs. Both are acceptable outcomes.
    const src =
        \\p cnf 1 2
        \\1 0
        \\-1 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    // Units are unit-propagated during Solver.init; the second unit
    // either conflicts in init (unsat_at_init), conflicts in the first
    // propagate, or shows up to BVE as a length-1 resolvent situation.
    // Any path that terminates in .unsat is correct.
    if (solver.unsat_at_init) return;
    const first = try solver.propagate();
    if (first != null) return;
    const r = try solver.preprocessBVE();
    try testing.expectEqual(solver_mod.Result.unsat, r.?);
}

test "bve: sat reconstruction end-to-end on a formula with an eliminated var" {
    // BVE eliminates var 1 (its clauses are satisfied at level 0 by the
    // units, so the only resolvent is dropped); the reconstructed value
    // must still satisfy (1 2) and (-1 3).
    const src =
        \\p cnf 3 4
        \\1 2 0
        \\-1 3 0
        \\2 0
        \\3 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    const result = try solver.solve();
    try testing.expectEqual(solver_mod.Result.sat, result);
    solver.extendModel();
    try testing.expectEqual(@as(?usize, null), solver.findFalsifiedClause(&formula));
}

test "bve: locked protection — a clause that reasons a level-0 unit stays untouched" {
    // Setup: (1 2 3), unit (-2), unit (-3). BCP forces x1=true with
    // reason = cref(1 2 3). That clause is locked and must not be
    // eliminated away. Variable 1 has +1 only in the locked clause,
    // no -1 clauses, so the elimination attempt would normally succeed
    // with 0 resolvents; the locked gate must stop it.
    const src =
        \\p cnf 3 3
        \\1 2 3 0
        \\-2 0
        \\-3 0
    ;
    const gpa = testing.allocator;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(gpa, &formula);
    defer solver.deinit();

    const conflict = try solver.propagate();
    try testing.expect(conflict == null);

    const v0_info = solver.assignment.vars[0];
    try testing.expectEqual(assignment_mod.Value.true, v0_info.value);
    try testing.expectEqual(@as(u32, 0), v0_info.level);
    try testing.expect(!v0_info.reason.isNone());
    try testing.expect(!v0_info.reason.isBinary());

    const r = try solver.bve();
    try testing.expect(r == null);
    try testing.expect(!hasEliminated(&solver, 0));
}

fn addLearnedClause(solver: *solver_mod.Solver, dimacs: []const i32, lbd: u32) !ClauseRef {
    var lits: [16]Literal = undefined;
    for (dimacs, 0..) |d, i| lits[i] = Literal.fromDimacs(d);
    const cref = try solver.addClauseToArena(lits[0..dimacs.len], true, lbd);
    try solver.learned_clauses.append(testing.allocator, cref);
    try solver.attachWatches(cref);
    return cref;
}

fn isLiteralSet(lits: []const Literal, dimacs: []const i32) bool {
    if (lits.len != dimacs.len) return false;
    for (dimacs) |d| {
        const wanted = Literal.fromDimacs(d);
        for (lits) |lit| {
            if (lit.eql(wanted)) break;
        } else return false;
    }
    return true;
}

fn lastLearnedClause(solver: *solver_mod.Solver) ClauseRef {
    return solver.learned_clauses.items[solver.learned_clauses.items.len - 1];
}

fn randomThreeSat(seed: u64, num_vars: u32, num_clauses: usize) !cnf.Formula {
    var formula = cnf.Formula.init(testing.allocator, num_vars);
    errdefer formula.deinit();
    var prng = std.Random.DefaultPrng.init(seed);
    const random = prng.random();
    for (0..num_clauses) |_| {
        var lits: [3]Literal = undefined;
        for (&lits) |*lit| lit.* = Literal.init(random.uintLessThan(u32, num_vars), random.boolean());
        try formula.addClause(&lits);
    }
    return formula;
}

test "every long clause learned during search has an LBD of at least 2" {
    // A long learned clause holds the UIP at the conflict level plus
    // literals from lower, non-zero levels, so its true LBD is >= 2.
    var formula = try randomThreeSat(1, 100, 430);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();

    _ = try solver.solve();

    // Below 10k conflicts no inprocessing pass has rewritten an LBD.
    try testing.expect(solver.stats.conflicts < 10_000);
    var long_learned: usize = 0;
    var below_two: usize = 0;
    for (solver.learned_clauses.items) |cref| {
        if (solver.clauseIsDeleted(cref)) continue;
        long_learned += 1;
        if (solver.clauseLbd(cref) < 2) below_two += 1;
    }
    try testing.expect(long_learned > 0);
    try testing.expectEqual(@as(usize, 0), below_two);
}

test "a learned clause shortened by vivify keeps a non-zero LBD" {
    var formula = try parseSource("p cnf 5 1\n1 2 3 0\n");
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try addLearnedClause(&solver, &.{ 1, 2, 3, 4, 5 }, 3);
    _ = try solver.propagate();

    const r = try solver.vivify();

    try testing.expect(r == null);
    const shortened = lastLearnedClause(&solver);
    try testing.expect(isLiteralSet(solver.clauseLits(shortened), &.{ 1, 2, 3 }));
    try testing.expectEqual(@as(u32, 3), solver.clauseLbd(shortened));
}

test "a learned clause strengthened by subsume keeps a non-zero LBD" {
    // -34 collides with -2 in the literal abstract; see the SSR-to-binary test.
    var formula = try parseSource("p cnf 34 2\n1 -2 0\n-2 5 6 0\n");
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try addLearnedClause(&solver, &.{ 1, 2, -34, 7 }, 3);
    _ = try solver.propagate();

    const r = try solver.subsume();

    try testing.expect(r == null);
    const strengthened = lastLearnedClause(&solver);
    try testing.expect(isLiteralSet(solver.clauseLits(strengthened), &.{ 1, -34, 7 }));
    try testing.expectEqual(@as(u32, 3), solver.clauseLbd(strengthened));
}

test "a learned clause rewritten by equiv keeps a non-zero LBD" {
    var formula = try parseSource("p cnf 4 2\n-1 2 0\n1 -2 0\n");
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try addLearnedClause(&solver, &.{ 2, 3, 4 }, 2);
    _ = try solver.propagate();

    const r = try solver.equiv();

    try testing.expect(r == null);
    const rewritten = lastLearnedClause(&solver);
    try testing.expect(isLiteralSet(solver.clauseLits(rewritten), &.{ 1, 3, 4 }));
    try testing.expectEqual(@as(u32, 2), solver.clauseLbd(rewritten));
}

fn countLiveClauses(solver: *solver_mod.Solver, dimacs: []const i32, learned: bool) usize {
    var count: usize = 0;
    var cref: ClauseRef = 0;
    while (cref < solver.arena.items.len) {
        const len = solver.clauseLen(cref);
        if (!solver.clauseIsDeleted(cref) and solver.clauseIsLearned(cref) == learned and
            isLiteralSet(solver.clauseLits(cref), dimacs)) count += 1;
        cref += clause_mod.header_slots + len;
    }
    return count;
}

fn addClauseDimacs(formula: *cnf.Formula, dimacs: []const i32) !void {
    var lits: [16]Literal = undefined;
    for (dimacs, 0..) |d, i| lits[i] = Literal.fromDimacs(d);
    try formula.addClause(lits[0..dimacs.len]);
}

// Each variable of `dimacs` then occurs 101 times per polarity, so its
// occurrence product exceeds bve.max_occ_product and BVE never picks it.
fn addBveShield(formula: *cnf.Formula, dimacs: []const i32) !void {
    var pos: [16]Literal = undefined;
    var neg: [16]Literal = undefined;
    for (dimacs, 0..) |d, i| {
        pos[i] = Literal.fromDimacs(d);
        neg[i] = Literal.fromDimacs(-d);
    }
    for (0..101) |_| {
        try formula.addClause(pos[0..dimacs.len]);
        try formula.addClause(neg[0..dimacs.len]);
    }
}

// Variable 1 occurs in the irredundant (1 2 3) and the learned (-1 4 5).
fn initLearnedPivotSolver(formula: *cnf.Formula) !solver_mod.Solver {
    try addClauseDimacs(formula, &.{ 1, 2, 3 });
    try addBveShield(formula, &.{ 2, 3, 4, 5, 6 });
    var solver = try solver_mod.Solver.init(testing.allocator, formula);
    errdefer solver.deinit();
    _ = try addLearnedClause(&solver, &.{ -1, 4, 5 }, 2);
    _ = try solver.propagate();
    return solver;
}

test "bve never installs a resolvent of a learned clause as an irredundant clause" {
    var formula = cnf.Formula.init(testing.allocator, 6);
    defer formula.deinit();
    var solver = try initLearnedPivotSolver(&formula);
    defer solver.deinit();

    const r = try solver.preprocessBVE();

    try testing.expect(r == null);
    try testing.expect(hasEliminated(&solver, 0));
    try testing.expectEqual(@as(usize, 0), countLiveClauses(&solver, &.{ 2, 3, 4, 5 }, false));
}

test "bve deletes the learned clauses of a variable it eliminates" {
    var formula = cnf.Formula.init(testing.allocator, 6);
    defer formula.deinit();
    var solver = try initLearnedPivotSolver(&formula);
    defer solver.deinit();

    _ = try solver.preprocessBVE();

    try testing.expect(hasEliminated(&solver, 0));
    try testing.expectEqual(@as(usize, 0), countLiveClauses(&solver, &.{ -1, 4, 5 }, true));
    try testing.expectEqual(@as(usize, 0), solver.learned_clauses.items.len);
}

test "bve witness records only irredundant clauses" {
    var formula = cnf.Formula.init(testing.allocator, 6);
    defer formula.deinit();
    var solver = try initLearnedPivotSolver(&formula);
    defer solver.deinit();

    _ = try solver.preprocessBVE();

    try testing.expect(hasEliminated(&solver, 0));
    const lits = solver.bve_witness_lits.items;
    for (solver.bve_witness_frames.items) |frame| {
        var cursor = frame.pos_start;
        while (cursor < frame.end) {
            const len = lits[cursor].raw;
            const run = lits[cursor + 1 .. cursor + 1 + len];
            try testing.expect(!isLiteralSet(run, &.{ -1, 4, 5 }));
            cursor += 1 + len;
        }
    }
}

test "bve growth bound counts only irredundant clauses" {
    // Irredundant: 3 clauses with +1, 2 with -1, 6 resolvents > 5, so var 1
    // stays. The learned (1 -5 -6) only adds tautological resolvents.
    var formula = cnf.Formula.init(testing.allocator, 7);
    defer formula.deinit();
    for ([_][2]i32{ .{ 1, 2 }, .{ 1, 3 }, .{ 1, 4 }, .{ -1, 5 }, .{ -1, 6 } }) |c| {
        try addClauseDimacs(&formula, &c);
    }
    try addBveShield(&formula, &.{ 2, 3, 4, 5, 6, 7 });
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try addLearnedClause(&solver, &.{ 1, -5, -6 }, 2);
    _ = try solver.propagate();

    const r = try solver.preprocessBVE();

    try testing.expect(r == null);
    try testing.expect(!hasEliminated(&solver, 0));
}

test "probe never assigns an eliminated variable" {
    // Probing assigns a variable both ways at level 1, and each backtrack
    // saves its phase, so a probed variable ends with its saved phase flipped.
    const src =
        \\p cnf 11 6
        \\1 2 0
        \\-1 3 0
        \\-2 4 5 0
        \\-2 6 7 0
        \\-3 8 9 0
        \\-3 10 11 0
    ;
    var formula = try parseSource(src);
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try solver.propagate();
    _ = try solver.preprocessBVE();
    try testing.expect(hasEliminated(&solver, 0));
    const phases_before = try testing.allocator.dupe(bool, solver.assignment.saved_phases);
    defer testing.allocator.free(phases_before);

    const r = try solver.probe();

    try testing.expect(r == null);
    var v: u32 = 0;
    while (v < solver.num_vars) : (v += 1) {
        if (!hasEliminated(&solver, v)) continue;
        try testing.expectEqual(phases_before[v], solver.assignment.saved_phases[v]);
    }
}

test "a long clause strengthened by subsume propagates its last non-false literal" {
    // With 34 and 35 true at level 0, SSR turns (1 2 -34 -35) into
    // (1 -34 -35), which forces 1.
    var formula = try parseSource("p cnf 35 5\n1 2 -34 -35 0\n1 -2 0\n-2 5 6 0\n34 0\n35 0\n");
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try solver.propagate();

    const r = try solver.preprocessSubsume();

    try testing.expect(r == null);
    try testing.expect(solver.stats.strengthened_clauses >= 1);
    try testing.expectEqual(assignment_mod.Value.true, solver.assignment.valueOfVar(0));
}

test "a clause subsume strengthens to a binary with a level-0 false literal propagates" {
    // SSR turns (1 2 -34) into (1 -34), and 34 is true at level 0.
    var formula = try parseSource("p cnf 34 4\n1 2 -34 0\n1 -2 0\n-2 5 6 0\n34 0\n");
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try solver.propagate();

    const r = try solver.preprocessSubsume();

    try testing.expect(r == null);
    try testing.expect(solver.stats.strengthened_clauses >= 1);
    try testing.expectEqual(assignment_mod.Value.true, solver.assignment.valueOfVar(0));
}

test "vivify run right after a learned unit keeps the unit's level-0 implications" {
    // Mirrors solve.zig: the learned unit 1 is asserted at level 0 and
    // vivify runs before anything propagates it. (-1 -2) then forces -2.
    var formula = try parseSource("p cnf 4 1\n-1 -2 0\n");
    defer formula.deinit();
    var solver = try solver_mod.Solver.init(testing.allocator, &formula);
    defer solver.deinit();
    _ = try addLearnedClause(&solver, &.{ 2, 3, 4 }, 2);
    _ = try solver.propagate();
    try solver.assignment.assignAtLevel(Literal.fromDimacs(1), Reason.none, 0);

    const r = try solver.vivify();

    try testing.expect(r == null);
    try testing.expectEqual(assignment_mod.Value.false, solver.assignment.valueOfVar(1));
    try testing.expectEqual(@as(u32, 0), solver.assignment.vars[1].level);
}

test "parser rejects -0 instead of reading it as a clause terminator" {
    try testing.expectError(error.InvalidToken, parseSource("p cnf 1 1\n1 -0 0\n"));
}

test "trimming unused variables keeps only those up to the highest a clause mentions" {
    var formula = try parseSource("p cnf 1073741824 2\n1 -3 0\n2 0\n");
    defer formula.deinit();

    formula.trimUnusedVars();

    try testing.expectEqual(@as(u32, 3), formula.num_vars);
}

test "trimming unused variables leaves an empty formula with none" {
    var formula = try parseSource("p cnf 50 0\n");
    defer formula.deinit();

    formula.trimUnusedVars();

    try testing.expectEqual(@as(u32, 0), formula.num_vars);
}

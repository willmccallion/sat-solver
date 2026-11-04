// Clause primitives shared by the inprocessing passes, which run at level 0.

const core = @import("core");
const Literal = core.cnf.Literal;
const Assignment = core.assignment.Assignment;

// Keeps the literals of `lits` that are unassigned, in order, dropping the
// false ones; null when one is true. A watch on a false literal would never
// fire, since its negation is already past qhead.
pub fn unassignedAtRoot(assignment: *const Assignment, lits: []Literal) ?[]Literal {
    var kept: usize = 0;
    for (lits) |lit| {
        switch (assignment.valueOfLiteral(lit)) {
            .true => return null,
            .false => {},
            .unassigned => {
                lits[kept] = lit;
                kept += 1;
            },
        }
    }
    return lits[0..kept];
}

// `lits` sorted, deduplicated and stripped of literals false at level 0;
// null when it is a tautology or already satisfied.
pub fn normalizeAtRoot(assignment: *const Assignment, lits: []Literal) ?[]Literal {
    return unassignedAtRoot(assignment, core.cnf.sortedDistinct(lits) orelse return null);
}

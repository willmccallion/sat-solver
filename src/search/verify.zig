const core = @import("core");
const ClauseRef = core.cnf.ClauseRef;
const clause_mod = core.clause;

const state = @import("state.zig");
const Solver = state.Solver;

// Walks only the original, non-deleted clauses. Learned clauses are
// implied by the originals, and deleted clauses are holes in the arena
// that no longer participate in the problem. Original binaries don't
// live in the arena — they're checked separately out of original_binaries.
pub fn verifyModel(self: *Solver) bool {
    var cref: ClauseRef = 0;
    while (cref < self.arena.items.len) {
        const header = self.arena.items[cref].raw;
        const len = header & clause_mod.len_mask;
        const is_learned = (header & clause_mod.learned_bit) != 0;
        const is_deleted = (header & clause_mod.deleted_bit) != 0;
        if (!is_learned and !is_deleted) {
            var satisfied = false;
            var k: usize = 0;
            while (k < len) : (k += 1) {
                const lit = self.arena.items[cref + clause_mod.header_slots + k];
                if (self.assignment.valueOfLiteral(lit) == .@"true") {
                    satisfied = true;
                    break;
                }
            }
            if (!satisfied) return false;
        }
        cref += clause_mod.header_slots + len;
    }
    for (self.original_binaries.items) |pair| {
        if (self.assignment.valueOfLiteral(pair[0]) != .@"true" and
            self.assignment.valueOfLiteral(pair[1]) != .@"true")
        {
            return false;
        }
    }
    return true;
}

const std = @import("std");
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
            if (!satisfied) {
                std.debug.print("c VERIFY FAIL arena cref={d} len={d}:", .{ cref, len });
                var k2: usize = 0;
                while (k2 < len) : (k2 += 1) {
                    const lit = self.arena.items[cref + clause_mod.header_slots + k2];
                    const v = lit.variable();
                    const val = self.assignment.valueOfLiteral(lit);
                    const is_elim = self.eliminated.isSet(v);
                    var in_equiv = false;
                    var rep_signed: i32 = 0;
                    for (self.equiv_witness.items) |ef| {
                        if (ef.eliminated_var == v) {
                            in_equiv = true;
                            const rv: i32 = @intCast(ef.rep_lit.variable() + 1);
                            rep_signed = if (ef.rep_lit.raw & 1 == 0) rv else -rv;
                            break;
                        }
                    }
                    var in_bve = false;
                    for (self.bve_witness_frames.items) |bf| {
                        if (bf.pivot == v) {
                            in_bve = true;
                            break;
                        }
                    }
                    std.debug.print(
                        " {d}(val={any} elim={any} bve={any} equiv={any} rep={d})",
                        .{
                            if (lit.raw & 1 == 0) @as(i32, @intCast(v + 1)) else -@as(i32, @intCast(v + 1)),
                            val,
                            is_elim,
                            in_bve,
                            in_equiv,
                            rep_signed,
                        },
                    );
                }
                std.debug.print("\n", .{});
                return false;
            }
        }
        cref += clause_mod.header_slots + len;
    }
    for (self.original_binaries.items) |pair| {
        if (self.assignment.valueOfLiteral(pair[0]) != .@"true" and
            self.assignment.valueOfLiteral(pair[1]) != .@"true")
        {
            std.debug.print("c VERIFY FAIL bin:", .{});
            for (pair) |lit| {
                const v = lit.variable();
                const val = self.assignment.valueOfLiteral(lit);
                const is_elim = self.eliminated.isSet(v);
                std.debug.print(" {d}(val={any} elim={any})", .{
                    if (lit.raw & 1 == 0) @as(i32, @intCast(v + 1)) else -@as(i32, @intCast(v + 1)),
                    val,
                    is_elim,
                });
            }
            std.debug.print("\n", .{});
            return false;
        }
    }
    return true;
}

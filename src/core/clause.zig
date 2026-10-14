const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const ClauseRef = cnf.ClauseRef;

// Clause arena header layout. Every clause lives in a single flat buffer
// `arena: ArrayList(Literal)`; a ClauseRef is the arena index of its header.
// Per clause:
//   arena[cref + 0]  header — .raw = flags | length
//   arena[cref + 1]  lbd
//   arena[cref + 2..] literals
//
// The header reserves bits 30–31 for the learned and deleted flags, which
// caps live ClauseRef indices below 2^30. Reason encodings in
// assignment.Reason rely on this — binary reasons use the top bit as a
// discriminator that must not collide with a clause index.
pub const learned_bit: u32 = 0x8000_0000;
pub const deleted_bit: u32 = 0x4000_0000;
pub const len_mask: u32 = 0x3fff_ffff;
pub const header_slots: u32 = 2;

// Long-clause watcher. `blocker` is a literal from the same clause that
// propagate can check first without loading the clause body: if it's
// already true, the clause is satisfied and we can skip the arena fetch.
pub const Watcher = struct {
    clause: ClauseRef,
    blocker: Literal,
};

// Binary-clause watcher. 2-literal clauses never need the "find a new
// watch" dance of the two-watched scheme — the other literal IS the only
// alternative, so BCP is a single value lookup. Eliminating the arena
// touch per binary watcher is one of the bigger BCP wins.
pub const BinaryWatch = struct {
    other: Literal,
};

// Ensures room for one more entry in a per-literal list (watches,
// occurrences), doubling from a small minimum. ArrayList's own policy
// reserves a full cache line (128 bytes on x86-64) on top of every
// growth, which across millions of short per-literal lists costs
// gigabytes.
pub inline fn reserveSlot(comptime T: type, list: *std.ArrayList(T), allocator: Allocator) Allocator.Error!void {
    if (list.items.len == list.capacity) {
        @branchHint(.cold);
        try list.ensureTotalCapacityPrecise(allocator, @max(list.capacity * 2, min_slot_capacity));
    }
}

const min_slot_capacity: usize = 4;

// Propagate's result on conflict. The long-clause variant references an
// arena clause ref. The binary variant inlines the two literals of the
// falsified 2-clause because those clauses do not live in the arena.
pub const Conflict = union(enum) {
    clause: ClauseRef,
    binary: [2]Literal,
};

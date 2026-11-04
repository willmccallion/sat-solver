const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const ClauseRef = cnf.ClauseRef;

// Clause arena layout. Every long clause lives in one flat buffer of slots;
// a ClauseRef is the index of its header.
// Per clause:
//   arena[cref + 0]  header — .raw = flags | length
//   arena[cref + 1]  lbd
//   arena[cref + 2..] literals
//
// The header reserves bits 30–31 for the learned and deleted flags, which
// caps clause length below 2^30 (guaranteed by cnf.max_vars, since no
// clause repeats a variable). assignment.Reason tags binary reasons with
// bit 31, so every ClauseRef must stay below max_arena_slots.
const learned_bit: u32 = 0x8000_0000;
const deleted_bit: u32 = 0x4000_0000;
const len_mask: u32 = 0x3fff_ffff;
const max_arena_slots: usize = 1 << 31;
const header_slots: u32 = 2;

// Learned clauses are implied by the irredundant ones, so reduceDB may
// delete them.
pub const ClauseKind = enum { irredundant, learned };

pub const ClauseArena = struct {
    slots: std.ArrayList(Literal) = .empty,
    // Slots held by deleted clauses, which compaction reclaims.
    dead_slots: usize = 0,

    pub const AddError = Allocator.Error || error{ClauseArenaFull};

    pub fn deinit(self: *ClauseArena, allocator: Allocator) void {
        self.slots.deinit(allocator);
    }

    // Reserves exactly the room for `clause_count` clauses totalling
    // `literal_count` literals.
    pub fn reserve(self: *ClauseArena, allocator: Allocator, clause_count: usize, literal_count: usize) Allocator.Error!void {
        try self.slots.ensureTotalCapacityPrecise(allocator, clause_count * header_slots + literal_count);
    }

    pub fn add(self: *ClauseArena, allocator: Allocator, lits: []const Literal, clause_kind: ClauseKind, clause_lbd: u32) AddError!ClauseRef {
        if (self.slots.items.len + header_slots + lits.len > max_arena_slots) return error.ClauseArenaFull;
        const cref: ClauseRef = @intCast(self.slots.items.len);
        const header: u32 = @as(u32, @intCast(lits.len)) | (if (clause_kind == .learned) learned_bit else 0);
        try self.slots.ensureUnusedCapacity(allocator, header_slots + lits.len);
        self.slots.appendSliceAssumeCapacity(&.{ .{ .raw = header }, .{ .raw = clause_lbd } });
        self.slots.appendSliceAssumeCapacity(lits);
        return cref;
    }

    pub inline fn length(self: *const ClauseArena, cref: ClauseRef) u32 {
        return self.slots.items[cref].raw & len_mask;
    }

    pub inline fn isLearned(self: *const ClauseArena, cref: ClauseRef) bool {
        return (self.slots.items[cref].raw & learned_bit) != 0;
    }

    pub inline fn kind(self: *const ClauseArena, cref: ClauseRef) ClauseKind {
        return if (self.isLearned(cref)) .learned else .irredundant;
    }

    pub inline fn isDeleted(self: *const ClauseArena, cref: ClauseRef) bool {
        return (self.slots.items[cref].raw & deleted_bit) != 0;
    }

    pub inline fn lbd(self: *const ClauseArena, cref: ClauseRef) u32 {
        return self.slots.items[cref + 1].raw;
    }

    // Mutable, since propagation reorders a clause's watched literals.
    pub inline fn literals(self: *ClauseArena, cref: ClauseRef) []Literal {
        const start: usize = @as(usize, cref) + header_slots;
        return self.slots.items[start .. start + self.length(cref)];
    }

    // Where propagation prefetches a clause from.
    pub inline fn base(self: *const ClauseArena) [*]const Literal {
        return self.slots.items.ptr;
    }

    // A learned clause that subsumes an irredundant one takes over its
    // role in the formula, so it must no longer be eligible for reduceDB.
    pub fn promoteToIrredundant(self: *ClauseArena, cref: ClauseRef) void {
        self.slots.items[cref].raw &= ~learned_bit;
    }

    pub fn markDeleted(self: *ClauseArena, cref: ClauseRef) void {
        std.debug.assert(!self.isDeleted(cref));
        self.dead_slots += header_slots + self.length(cref);
        self.slots.items[cref].raw |= deleted_bit;
    }

    pub fn isMostlyHoles(self: *const ClauseArena) bool {
        return self.dead_slots * 2 > self.slots.items.len;
    }

    pub fn liveClauses(self: *const ClauseArena) LiveClauses {
        return .{ .arena = self };
    }

    // Moves the live clauses, in order, into new storage without the holes
    // deleted ones leave. The returned map gives each old ref its new one
    // until the caller has rewritten every ref it holds. Nothing changes if
    // allocating the new storage fails.
    pub fn compact(self: *ClauseArena, allocator: Allocator) Allocator.Error!Relocation {
        var fresh: std.ArrayList(Literal) = try .initCapacity(allocator, self.slots.items.len - self.dead_slots);
        var live = self.liveClauses();
        while (live.next()) |cref| {
            const new_cref: ClauseRef = @intCast(fresh.items.len);
            const end = @as(usize, cref) + header_slots + self.length(cref);
            fresh.appendSliceAssumeCapacity(self.slots.items[cref..end]);
            // The old LBD slot now records where the clause went.
            self.slots.items[cref + 1].raw = new_cref;
        }
        const old = self.*;
        self.* = .{ .slots = fresh };
        return .{ .old = old };
    }
};

// The arena's clauses that are not marked deleted, in arena order.
pub const LiveClauses = struct {
    arena: *const ClauseArena,
    next_cref: ClauseRef = 0,

    pub fn next(self: *LiveClauses) ?ClauseRef {
        while (self.next_cref < self.arena.slots.items.len) {
            const cref = self.next_cref;
            self.next_cref += header_slots + self.arena.length(cref);
            if (!self.arena.isDeleted(cref)) return cref;
        }
        return null;
    }
};

// Maps each clause of a compacted arena to its new ref.
pub const Relocation = struct {
    old: ClauseArena,

    pub fn deinit(self: *Relocation, allocator: Allocator) void {
        self.old.deinit(allocator);
    }

    // Null for a clause that was deleted and so was not moved.
    pub fn newRef(self: *const Relocation, old_cref: ClauseRef) ?ClauseRef {
        if (self.old.isDeleted(old_cref)) return null;
        return self.old.lbd(old_cref);
    }
};

// The LBD of a clause rewritten to `new_len` literals by inprocessing at
// level 0, where the levels that would recompute it are gone: its old LBD,
// capped at the new length.
pub fn rewrittenLbd(old_lbd: u32, new_len: usize) u32 {
    return @min(old_lbd, @as(u32, @intCast(new_len)));
}

// Long-clause watcher. `blocker` is a literal from the same clause that
// propagate can check first without loading the clause body: if it's
// already true, the clause is satisfied and we can skip the arena fetch.
pub const Watcher = struct {
    clause: ClauseRef,
    blocker: Literal,
};

// Binary-clause watcher. 2-literal clauses never need the "find a new
// watch" dance of the two-watched scheme — the other literal IS the only
// alternative, so BCP is a single value lookup that never touches the arena.
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

const std = @import("std");
const core = @import("core");
const Literal = core.cnf.Literal;
const ClauseRef = core.cnf.ClauseRef;
const Reason = core.assignment.Reason;
const clause_mod = core.clause;

const state = @import("../state.zig");
const Solver = state.Solver;
const EquivFrame = state.EquivFrame;
const solver_mod = @import("../solver.zig");
const Result = solver_mod.Result;

// Equivalent-literal substitution via binary-implication-graph SCC.
//
// Build a digraph on 2*num_vars literal nodes where `l → other` is an
// edge iff `bin_watchers[l.raw]` holds a `{other}` entry — equivalently,
// the binary clause `(¬l ∨ other)` is in the formula. Run Tarjan's SCC
// iteratively; two literals in the same SCC are provably equivalent. If
// an SCC contains both `l` and `¬l` the formula is unsat. Otherwise pick
// a representative per SCC (min raw) and substitute every non-rep
// occurrence across the arena and bin_watchers.
//
// After substitution a long clause may collapse to a unit, a binary, a
// shorter long, or a tautology; binaries may collapse to a unit or a
// tautology. Duplicates are merged by sort+dedupe before classification.
//
// DRAT ordering: emit ALL add-new clauses first, then ALL delete-old
// clauses. The equivalence-edge binaries that justify each add under
// RUP are still in the formula during every add, so every emitted add
// validates. The delete phase then strips both the originals and the
// tautologized equivalence binaries.
//
// Model reconstruction: each eliminated variable pushes a frame onto
// `equiv_witness`; `reconstructEquivVars` walks the stack in reverse
// and copies each variable's value from the current valueOfLiteral of
// its representative.

pub const inprocess_initial_interval: u64 = 10_000;
pub const grow_num: u64 = 3;
pub const grow_den: u64 = 2;

pub fn equiv(self: *Solver) !?Result {
    std.debug.assert(self.assignment.level == 0);

    const num_vars = self.num_vars;
    const num_lits: usize = @as(usize, num_vars) * 2;
    if (num_lits == 0) return null;

    const unvisited: u32 = std.math.maxInt(u32);

    const index_arr = try self.allocator.alloc(u32, num_lits);
    defer self.allocator.free(index_arr);
    const lowlink = try self.allocator.alloc(u32, num_lits);
    defer self.allocator.free(lowlink);
    const on_stack = try self.allocator.alloc(bool, num_lits);
    defer self.allocator.free(on_stack);
    const scc_id = try self.allocator.alloc(u32, num_lits);
    defer self.allocator.free(scc_id);

    @memset(index_arr, unvisited);
    @memset(lowlink, 0);
    @memset(on_stack, false);
    @memset(scc_id, unvisited);

    const DfsFrame = struct { node: u32, cursor: u32 };
    var tarjan_stack: std.ArrayList(u32) = .empty;
    defer tarjan_stack.deinit(self.allocator);
    var dfs_stack: std.ArrayList(DfsFrame) = .empty;
    defer dfs_stack.deinit(self.allocator);

    var next_index: u32 = 0;
    var next_scc_id: u32 = 0;

    // Filter: skip literals whose variable is assigned at level 0 or
    // already eliminated. Their equivalence is moot and their
    // bin_watchers entries may be stale.
    const isLitSkippable = struct {
        fn f(s: *const Solver, raw: u32) bool {
            const v = raw >> 1;
            if (s.assignment.vars[v].value != .unassigned) return true;
            if (s.eliminated.isSet(v)) return true;
            return false;
        }
    }.f;

    var start: u32 = 0;
    while (start < num_lits) : (start += 1) {
        if (index_arr[start] != unvisited) continue;
        if (isLitSkippable(self, start)) continue;

        index_arr[start] = next_index;
        lowlink[start] = next_index;
        next_index += 1;
        try tarjan_stack.append(self.allocator, start);
        on_stack[start] = true;
        try dfs_stack.append(self.allocator, .{ .node = start, .cursor = 0 });

        while (dfs_stack.items.len > 0) {
            const dfs_top = dfs_stack.items.len - 1;
            const node = dfs_stack.items[dfs_top].node;
            const successors = self.bin_watchers[node].items;

            var pushed = false;
            while (dfs_stack.items[dfs_top].cursor < successors.len) {
                const cursor = dfs_stack.items[dfs_top].cursor;
                dfs_stack.items[dfs_top].cursor = cursor + 1;
                const next_raw = successors[cursor].other.raw;
                if (next_raw == node) continue;
                if (isLitSkippable(self, next_raw)) continue;

                if (index_arr[next_raw] == unvisited) {
                    index_arr[next_raw] = next_index;
                    lowlink[next_raw] = next_index;
                    next_index += 1;
                    try tarjan_stack.append(self.allocator, next_raw);
                    on_stack[next_raw] = true;
                    try dfs_stack.append(
                        self.allocator,
                        .{ .node = next_raw, .cursor = 0 },
                    );
                    pushed = true;
                    break;
                } else if (on_stack[next_raw]) {
                    if (index_arr[next_raw] < lowlink[node]) {
                        lowlink[node] = index_arr[next_raw];
                    }
                }
            }
            if (pushed) continue;

            if (lowlink[node] == index_arr[node]) {
                while (true) {
                    const w = tarjan_stack.pop().?;
                    on_stack[w] = false;
                    scc_id[w] = next_scc_id;
                    if (w == node) break;
                }
                next_scc_id += 1;
            }

            _ = dfs_stack.pop();
            if (dfs_stack.items.len > 0) {
                const parent = dfs_stack.items[dfs_stack.items.len - 1].node;
                if (lowlink[node] < lowlink[parent]) {
                    lowlink[parent] = lowlink[node];
                }
            }
        }
    }

    // UNSAT detection and representative selection
    {
        var v: u32 = 0;
        while (v < num_vars) : (v += 1) {
            const pos = v << 1;
            const neg = pos | 1;
            if (scc_id[pos] != unvisited and scc_id[pos] == scc_id[neg]) {
                // x reaches ¬x, so the unit ¬x is RUP; only after it is
                // the empty clause RUP as well.
                try self.proof.addClause(&.{Literal{ .raw = neg }});
                try self.proof.empty();
                return .unsat;
            }
        }
    }

    const scc_rep = try self.allocator.alloc(u32, @max(next_scc_id, 1));
    defer self.allocator.free(scc_rep);
    @memset(scc_rep, std.math.maxInt(u32));
    {
        var lr: u32 = 0;
        while (lr < num_lits) : (lr += 1) {
            const id = scc_id[lr];
            if (id == unvisited) continue;
            if (lr < scc_rep[id]) scc_rep[id] = lr;
        }
    }

    const lit_remap = try self.allocator.alloc(Literal, num_lits);
    defer self.allocator.free(lit_remap);
    {
        var lr: u32 = 0;
        while (lr < num_lits) : (lr += 1) {
            const id = scc_id[lr];
            if (id == unvisited) {
                lit_remap[lr] = .{ .raw = lr };
            } else {
                lit_remap[lr] = .{ .raw = scc_rep[id] };
            }
        }
    }

    // Early out if nothing to substitute
    {
        var any_substitution = false;
        var v: u32 = 0;
        while (v < num_vars) : (v += 1) {
            if (self.assignment.vars[v].value != .unassigned) continue;
            if (self.eliminated.isSet(v)) continue;
            const pos = v << 1;
            if (lit_remap[pos].raw != pos) {
                any_substitution = true;
                break;
            }
        }
        if (!any_substitution) return null;
    }

    // Collect long-clause work
    // We buffer (old_cref, snapshotted old lits, substituted new lits) and
    // emit all adds + all deletes BEFORE mutating state, so every DRAT-add
    // sees the full equivalence-binary set and validates under RUP.

    const LongWork = struct {
        old_cref: ClauseRef,
        is_learned: bool,
        new_off: u32,
        new_len: u32,
        old_off: u32,
        old_len: u32,
    };

    var long_work: std.ArrayList(LongWork) = .empty;
    defer long_work.deinit(self.allocator);
    var work_old_lits: std.ArrayList(Literal) = .empty;
    defer work_old_lits.deinit(self.allocator);
    var work_new_lits: std.ArrayList(Literal) = .empty;
    defer work_new_lits.deinit(self.allocator);
    var scratch: std.ArrayList(Literal) = .empty;
    defer scratch.deinit(self.allocator);

    {
        var cref: ClauseRef = 0;
        while (cref < self.arena.items.len) {
            const header = self.arena.items[cref].raw;
            const len = header & clause_mod.len_mask;
            const span = clause_mod.header_slots + len;
            defer cref += span;
            if ((header & clause_mod.deleted_bit) != 0) continue;
            if (len < 3) continue;

            const lits = self.clauseLits(cref);
            var any_changed = false;
            for (lits) |lit| {
                if (lit_remap[lit.raw].raw != lit.raw) {
                    any_changed = true;
                    break;
                }
            }
            if (!any_changed) continue;
            if (clauseIsLockedAtLevel0(self, cref)) continue;

            // Build substituted literal list: rename, sort, dedupe,
            // detect tautology.
            scratch.clearRetainingCapacity();
            try scratch.ensureTotalCapacity(self.allocator, lits.len);
            for (lits) |lit| {
                scratch.appendAssumeCapacity(lit_remap[lit.raw]);
            }
            std.mem.sort(Literal, scratch.items, {}, struct {
                fn f(_: void, a: Literal, b: Literal) bool {
                    return a.raw < b.raw;
                }
            }.f);
            var w: usize = 0;
            var is_taut = false;
            var prev_raw: u32 = std.math.maxInt(u32);
            for (scratch.items) |lit| {
                if (lit.raw == prev_raw) continue;
                if (prev_raw != std.math.maxInt(u32) and (prev_raw ^ 1) == lit.raw) {
                    is_taut = true;
                    break;
                }
                scratch.items[w] = lit;
                w += 1;
                prev_raw = lit.raw;
            }

            // Level-0 simplification: drop false-at-level-0 lits; if any is
            // true-at-level-0, the rewritten clause is tautologically
            // satisfied (treat like .taut). Without this, attachWatches can
            // bind to false literals past qhead — orphaned watcher.
            var sw: usize = 0;
            var sat_at_l0 = false;
            if (!is_taut) {
                for (scratch.items[0..w]) |lit| {
                    const val = self.assignment.valueOfLiteral(lit);
                    switch (val) {
                        .@"true" => {
                            sat_at_l0 = true;
                            break;
                        },
                        .@"false" => {},
                        .unassigned => {
                            scratch.items[sw] = lit;
                            sw += 1;
                        },
                    }
                }
            }
            const new_len: u32 = if (is_taut or sat_at_l0) 0 else @intCast(sw);

            const old_off: u32 = @intCast(work_old_lits.items.len);
            try work_old_lits.appendSlice(self.allocator, lits);
            const new_off: u32 = @intCast(work_new_lits.items.len);
            if (new_len > 0) {
                try work_new_lits.appendSlice(
                    self.allocator,
                    scratch.items[0..new_len],
                );
            }
            try long_work.append(self.allocator, .{
                .old_cref = cref,
                .is_learned = (header & clause_mod.learned_bit) != 0,
                .new_off = new_off,
                .new_len = new_len,
                .old_off = old_off,
                .old_len = len,
            });
        }
    }

    // Collect binary work
    const BinKind = enum { tautology, unit, rebind };
    const BinWork = struct {
        old_a: Literal,
        old_b: Literal,
        new_a: Literal, // meaningful when kind != tautology
        new_b: Literal, // meaningful when kind == rebind
        kind: BinKind,
    };
    var bin_work: std.ArrayList(BinWork) = .empty;
    defer bin_work.deinit(self.allocator);

    {
        var lr: u32 = 0;
        while (lr < num_lits) : (lr += 1) {
            const watcher_lit = Literal{ .raw = lr };
            const a = watcher_lit.negate();
            for (self.bin_watchers[lr].items) |entry| {
                const b = entry.other;
                if (a.raw >= b.raw) continue;
                const a_new_raw = lit_remap[a.raw].raw;
                const b_new_raw = lit_remap[b.raw].raw;
                if (a_new_raw == a.raw and b_new_raw == b.raw) continue;
                const a_new = Literal{ .raw = a_new_raw };
                const b_new = Literal{ .raw = b_new_raw };
                if (a_new.raw == (b_new.raw ^ 1)) {
                    try bin_work.append(self.allocator, .{
                        .old_a = a,
                        .old_b = b,
                        .new_a = a_new,
                        .new_b = b_new,
                        .kind = .tautology,
                    });
                } else if (a_new.raw == b_new.raw) {
                    try bin_work.append(self.allocator, .{
                        .old_a = a,
                        .old_b = b,
                        .new_a = a_new,
                        .new_b = b_new,
                        .kind = .unit,
                    });
                } else {
                    try bin_work.append(self.allocator, .{
                        .old_a = a,
                        .old_b = b,
                        .new_a = a_new,
                        .new_b = b_new,
                        .kind = .rebind,
                    });
                }
            }
        }
    }

    if (long_work.items.len == 0 and bin_work.items.len == 0) return null;

    // Record witness frames and mark eliminated
    {
        var v: u32 = 0;
        while (v < num_vars) : (v += 1) {
            if (self.assignment.vars[v].value != .unassigned) continue;
            if (self.eliminated.isSet(v)) continue;
            const pos = v << 1;
            const rep_raw = lit_remap[pos].raw;
            if (rep_raw == pos) continue;
            try self.equiv_witness.append(
                self.allocator,
                .{ .eliminated_var = v, .rep_lit = .{ .raw = rep_raw } },
            );
            self.eliminated.set(v);
            self.stats.equiv_eliminated += 1;
        }
    }

    // Rewrite BVE witness under the new remap
    // Earlier BVE passes may have recorded clauses that mention literals
    // we're about to eliminate here. reconstructEliminatedVars walks those
    // clauses before reconstructEquivVars fills in equiv-eliminated values,
    // so any un-remapped reference would read `.unassigned` and bias the
    // pivot choice. Rewriting the buffer in place keeps BVE reconstruction
    // self-contained: it only needs values of live-or-BVE-eliminated vars.
    for (self.bve_witness_frames.items) |frame| {
        var cursor: u32 = frame.pos_start;
        while (cursor < frame.end) {
            const clen: u32 = self.bve_witness_lits.items[cursor].raw;
            const lit_start = cursor + 1;
            const lit_end = lit_start + clen;
            var k: u32 = lit_start;
            while (k < lit_end) : (k += 1) {
                const lit = self.bve_witness_lits.items[k];
                self.bve_witness_lits.items[k] = lit_remap[lit.raw];
            }
            cursor = lit_end;
        }
    }

    // Phase A: emit all DRAT adds
    for (long_work.items) |lw| {
        if (lw.new_len == 0) continue;
        const new_lits = work_new_lits.items[lw.new_off .. lw.new_off + lw.new_len];
        try self.proof.addClause(new_lits);
    }
    for (bin_work.items) |bw| {
        switch (bw.kind) {
            .tautology => {},
            .unit => try self.proof.addClause(&[_]Literal{bw.new_a}),
            .rebind => try self.proof.addClause(&[_]Literal{ bw.new_a, bw.new_b }),
        }
    }

    // Phase B: emit all DRAT deletes
    for (long_work.items) |lw| {
        const old_lits = work_old_lits.items[lw.old_off .. lw.old_off + lw.old_len];
        try self.proof.deleteClause(old_lits);
    }
    for (bin_work.items) |bw| {
        try self.proof.deleteClause(&[_]Literal{ bw.old_a, bw.old_b });
    }

    // Phase C: mutate state for long clauses
    var any_deleted = false;
    var unsat_derived = false;

    for (long_work.items) |lw| {
        if (unsat_derived) break;
        // Mark old clause deleted first. We never read it again after this.
        self.arena.items[lw.old_cref].raw |= clause_mod.deleted_bit;
        any_deleted = true;

        if (lw.new_len == 0) continue; // tautology

        const new_lits = work_new_lits.items[lw.new_off .. lw.new_off + lw.new_len];

        if (lw.new_len == 1) {
            const unit = new_lits[0];
            const val = self.assignment.valueOfLiteral(unit);
            if (val == .@"false") {
                unsat_derived = true;
                break;
            }
            if (val == .unassigned) {
                try self.assignment.assign(unit, Reason.none);
            }
            continue;
        }

        if (lw.new_len == 2) {
            const a = new_lits[0];
            const b = new_lits[1];
            try self.addBinary(a, b);
            continue;
        }

        // new_len >= 3: install as arena clause. addClauseToArena may
        // reallocate self.arena; new_lits is a slice into work_new_lits
        // which is a separate allocation, so it stays valid.
        const lbd: u32 = self.computeLbd(new_lits);
        const new_cref = try self.addClauseToArena(new_lits, lw.is_learned, lbd);
        try self.attachWatches(new_cref);
        if (lw.is_learned) {
            try self.learned_clauses.append(self.allocator, new_cref);
        }
    }

    if (unsat_derived) {
        try self.proof.empty();
        return .unsat;
    }

    // Phase D: mutate state for binaries
    for (bin_work.items) |bw| {
        if (unsat_derived) break;
        removeBinary(self, bw.old_a, bw.old_b);
        switch (bw.kind) {
            .tautology => {},
            .unit => {
                const val = self.assignment.valueOfLiteral(bw.new_a);
                if (val == .@"false") {
                    unsat_derived = true;
                    break;
                }
                if (val == .unassigned) {
                    try self.assignment.assign(bw.new_a, Reason.none);
                }
            },
            .rebind => {
                try self.addBinary(bw.new_a, bw.new_b);
            },
        }
    }

    if (unsat_derived) {
        try self.proof.empty();
        return .unsat;
    }

    // Watcher and learned-clauses sweep
    if (any_deleted) {
        for (self.watchers) |*wlist| {
            var j: usize = 0;
            for (wlist.items) |entry| {
                if (!self.clauseIsDeleted(entry.clause)) {
                    wlist.items[j] = entry;
                    j += 1;
                }
            }
            wlist.shrinkRetainingCapacity(j);
        }

        var j: usize = 0;
        for (self.learned_clauses.items) |cref| {
            if (!self.clauseIsDeleted(cref)) {
                self.learned_clauses.items[j] = cref;
                j += 1;
            }
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }

    if ((try self.propagate()) != null) {
        try self.proof.empty();
        return .unsat;
    }

    self.stats.equivs += 1;
    return null;
}

// Returns true when `cref` is currently the reason for a level-0 literal.
fn clauseIsLockedAtLevel0(self: *Solver, cref: ClauseRef) bool {
    const lits = self.clauseLits(cref);
    for (lits) |lit| {
        const vi = self.assignment.vars[lit.variable()];
        if (vi.level == 0 and !vi.reason.isNone() and
            !vi.reason.isBinary() and vi.reason.clauseRef() == cref)
        {
            return true;
        }
    }
    return false;
}

// Swap-remove the binary (a, other) from both sides of bin_watchers.
fn removeBinary(self: *Solver, a: Literal, other: Literal) void {
    const a_neg_idx = a.negate().raw;
    var i: usize = 0;
    while (i < self.bin_watchers[a_neg_idx].items.len) {
        if (self.bin_watchers[a_neg_idx].items[i].other.raw == other.raw) {
            _ = self.bin_watchers[a_neg_idx].swapRemove(i);
            break;
        }
        i += 1;
    }
    const other_neg_idx = other.negate().raw;
    var j: usize = 0;
    while (j < self.bin_watchers[other_neg_idx].items.len) {
        if (self.bin_watchers[other_neg_idx].items[j].other.raw == a.raw) {
            _ = self.bin_watchers[other_neg_idx].swapRemove(j);
            break;
        }
        j += 1;
    }
}

// Walk `equiv_witness` in reverse and synthesize a value for every
// equiv-substituted variable from the current value of its representative.
// An unassigned rep (the rep variable was never branched or propagated)
// defaults to `true`; the caller has already run model verification so
// this only runs on .sat, where every non-eliminated variable has a value.
pub fn reconstructEquivVars(self: *Solver) void {
    const frames = self.equiv_witness.items;
    if (frames.len == 0) return;

    var idx: usize = frames.len;
    while (idx > 0) {
        idx -= 1;
        const frame = frames[idx];
        const v = frame.eliminated_var;
        var val = self.assignment.valueOfLiteral(frame.rep_lit);
        if (val == .unassigned) val = .@"true";
        const pos_slot = v << 1;
        self.assignment.vars[v].value = val;
        self.assignment.lit_values[pos_slot] = val;
        self.assignment.lit_values[pos_slot | 1] =
            if (val == .@"true") .@"false" else .@"true";
    }
}

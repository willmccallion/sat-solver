const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const Formula = cnf.Formula;
const ClauseRef = cnf.ClauseRef;
const assignment_mod = @import("assignment.zig");
const Assignment = assignment_mod.Assignment;
const Value = assignment_mod.Value;
const Reason = assignment_mod.Reason;

pub const Result = enum { sat, unsat, unknown };

/// Atomic interrupt flag. main.zig sets this from a signal handler
/// (SIGINT/SIGTERM/SIGXCPU) and/or a time-limit thread. Solver.solve()
/// polls it at the top of each conflict iteration and returns
/// .unknown if it's been raised — so a paused or killed solver emits
/// `s UNKNOWN` + exit 0 rather than a bogus verdict.
pub var interrupted: std.atomic.Value(bool) = .init(false);

// ---------------------------------------------------------------------------
// Clause arena.
//
// Every clause — original or learned — lives inside a single flat buffer
// `arena: ArrayList(Literal)`. A `ClauseRef` is the arena index of the clause
// header. Per clause the layout is:
//
//   arena[cref + 0]  header  — .raw = (learned_bit << 31) | length
//   arena[cref + 1]  lbd     — literal block distance (unused for originals)
//   arena[cref + 2]  lit 0
//   arena[cref + 3]  lit 1
//   ...
//   arena[cref + 1 + N] lit N-1
//
// The goal of this layout is cache behavior: a typical 3-literal clause is
// 20 bytes, so its header and all literals land on the same cache line, and
// walking `lits[2..]` during two-watched BCP is a sequential read inside
// that line. Before this refactor, each clause was a `StoredClause` record
// pointing at a separately-allocated literal slice — every access was two
// loads on unrelated cache lines, which showed up as a 4 % L1d miss rate
// on uf200-860.
//
// Important invariant: the arena is NEVER mutated while a literal slice is
// held across a suspend point. `propagate` takes `clauseLits` slices into
// the arena, but it only ever mutates existing clause slots (swapping
// watched literals), never appends. `addLearnedClause` appends to the
// arena, which may reallocate and invalidate in-flight slices — but it is
// only called from `solve`, after `analyze` has already returned.
// ---------------------------------------------------------------------------

const learned_bit: u32 = 0x8000_0000;
const deleted_bit: u32 = 0x4000_0000;
const len_mask: u32 = 0x3fff_ffff;
const header_slots: u32 = 2;

const Watcher = struct {
    clause: ClauseRef,
    blocker: Literal,
};

// Specialized watcher for 2-literal clauses. Binary clauses never need
// the blocker optimization or the "find a new watch" dance of the
// two-watched scheme — the other literal IS the only alternative, so
// BCP on a binary is a single value-lookup + branch. Eliminating the
// 4-byte clause-ref load per watcher is measurable; eliminating the
// ~24-byte clause-body load (header + lbd + 2 lits) is what actually
// matters, and with BinaryWatch + inline reasons we skip that entirely.
const BinaryWatch = struct {
    other: Literal,
};

// Propagate's result on conflict. The long-clause variant references an
// arena clause ref. The binary variant inlines the two literals of the
// falsified 2-clause because those clauses do not live in the arena.
const Conflict = union(enum) {
    clause: ClauseRef,
    binary: [2]Literal,
};

const var_decay: f64 = 0.95;
const rescale_threshold: f64 = 1e100;

// Glucose-style adaptive restart. Two EMAs of learned-clause LBD
// (fast = recent window, slow = long-run baseline) plus a "trail"
// EMA of the trail length at conflict time. Restart when recent LBD
// trends worse than the long-run average — unless the current stack
// is much deeper than the recent trail average, meaning search is
// clearly making progress and we shouldn't throw it away.
//
// Canonical Glucose tunings: fast window ~50, slow window ~1e4,
// ratio 1.25 (equivalent to Glucose's K=0.8 on the inverse form),
// blocker R=1.4. Both EMAs are bias-corrected (Adam style) so the
// ratio is meaningful from the very first conflict — without that
// correction, slow_raw << fast_raw during the first ~1/alpha_slow
// conflicts and the ratio runs away, causing a restart storm on
// short searches.
const lbd_fast_alpha: f64 = 1.0 / 50.0;
const lbd_slow_alpha: f64 = 1.0 / 10_000.0;
const restart_ratio: f64 = 1.25;
const trail_block_ratio: f64 = 1.4;
const restart_min_conflicts: u64 = 50;

// ReduceDB cadence — fires on its own conflict-count budget,
// independent of restarts. The interval grows by `reduce_grow` each
// trigger so long searches don't pay a log-N reduce every few
// thousand conflicts.
const reduce_initial: u64 = 2000;
const reduce_grow: u64 = 300;

pub const Stats = struct {
    decisions: u64 = 0,
    propagations: u64 = 0,
    conflicts: u64 = 0,
    restarts: u64 = 0,
    learned: u64 = 0,
    reductions: u64 = 0,
    deleted: u64 = 0,
};

pub const Solver = struct {
    allocator: Allocator,
    num_vars: u32,

    arena: std.ArrayList(Literal),
    watchers: []std.ArrayList(Watcher),

    // Per-literal binary watcher lists. Indexed by literal.raw, with
    // entries that carry the partner literal directly — no clause ref,
    // no arena load. A binary clause (a ∨ b) registers b under ¬a and
    // a under ¬b, same shape as regular watches, but the watcher can
    // be processed without ever touching a clause header.
    //
    // Unlike the long-clause watcher lists, these are monotonic: entries
    // are never moved or removed, because there is no "find a different
    // literal to watch" step for a 2-clause. That also means no
    // compaction cost in propagate.
    bin_watchers: []std.ArrayList(BinaryWatch),

    // Input-provided 2-literal clauses, kept verbatim for verifyModel.
    // They are NOT in the arena — verifying a binary via bin_watchers
    // would double-count (each clause appears as two watcher entries),
    // so we record the original pairs here at load time.
    original_binaries: std.ArrayList([2]Literal),

    assignment: Assignment,

    activities: []f64,
    var_inc: f64,
    order_heap: OrderHeap,

    analyze_seen: []bool,
    analyze_learned: std.ArrayList(Literal),
    analyze_levels: std.ArrayList(u32),
    analyze_to_clear: std.ArrayList(u32),
    analyze_stack: std.ArrayList(u32),

    learned_clauses: std.ArrayList(ClauseRef),
    max_learned: usize,

    proof_writer: ?*std.Io.Writer,

    // Glucose restart state. Each EMA carries a bias-correction
    // accumulator (`_bc`) that normalizes the raw sum for the Adam-
    // style `value / bc` unbiased estimate. The bc fields start at 0
    // and asymptote to 1.
    lbd_fast: f64,
    lbd_fast_bc: f64,
    lbd_slow: f64,
    lbd_slow_bc: f64,
    trail_fast: f64,
    trail_fast_bc: f64,
    conflicts_since_restart: u64,

    // Independent ReduceDB cadence.
    next_reduce: u64,
    reduce_interval: u64,

    unsat_at_init: bool,

    stats: Stats,

    pub fn init(allocator: Allocator, formula_in: Formula) !Solver {
        var formula = formula_in;
        defer formula.deinit();

        var self: Solver = .{
            .allocator = allocator,
            .num_vars = formula.num_vars,
            .arena = .empty,
            .watchers = &.{},
            .bin_watchers = &.{},
            .original_binaries = .empty,
            .assignment = try Assignment.init(allocator, formula.num_vars),
            .activities = &.{},
            .var_inc = 1.0,
            .order_heap = undefined,
            .analyze_seen = &.{},
            .analyze_learned = .empty,
            .analyze_levels = .empty,
            .analyze_to_clear = .empty,
            .analyze_stack = .empty,
            .learned_clauses = .empty,
            .max_learned = @max(formula.clauses.items.len, 1000),
            .proof_writer = null,
            .lbd_fast = 0,
            .lbd_fast_bc = 0,
            .lbd_slow = 0,
            .lbd_slow_bc = 0,
            .trail_fast = 0,
            .trail_fast_bc = 0,
            .conflicts_since_restart = 0,
            .next_reduce = reduce_initial,
            .reduce_interval = reduce_initial,
            .unsat_at_init = false,
            .stats = .{},
        };
        errdefer self.assignment.deinit();

        self.watchers = try allocator.alloc(std.ArrayList(Watcher), formula.num_vars * 2);
        for (self.watchers) |*w| w.* = .empty;
        errdefer {
            for (self.watchers) |*w| w.deinit(allocator);
            allocator.free(self.watchers);
        }

        self.bin_watchers = try allocator.alloc(std.ArrayList(BinaryWatch), formula.num_vars * 2);
        for (self.bin_watchers) |*w| w.* = .empty;
        errdefer {
            for (self.bin_watchers) |*w| w.deinit(allocator);
            allocator.free(self.bin_watchers);
        }
        errdefer self.original_binaries.deinit(allocator);

        self.activities = try allocator.alloc(f64, formula.num_vars);
        @memset(self.activities, 0);
        errdefer allocator.free(self.activities);

        self.analyze_seen = try allocator.alloc(bool, formula.num_vars);
        @memset(self.analyze_seen, false);
        errdefer allocator.free(self.analyze_seen);

        // Stacks used by recursive clause minimization in `analyze`. A var
        // can be pushed at most once per analyze (the `seen` flag filters
        // duplicates), so num_vars is a safe upper bound. Reserving up
        // front lets litRedundant use appendAssumeCapacity and stay
        // non-throwing in the hot loop.
        try self.analyze_stack.ensureTotalCapacity(allocator, formula.num_vars);
        errdefer self.analyze_stack.deinit(allocator);
        try self.analyze_to_clear.ensureTotalCapacity(allocator, formula.num_vars);
        errdefer self.analyze_to_clear.deinit(allocator);

        self.order_heap = try OrderHeap.init(allocator, formula.num_vars, self.activities);
        errdefer self.order_heap.deinit(allocator);
        {
            var v: u32 = 0;
            while (v < formula.num_vars) : (v += 1) {
                self.order_heap.insert(v);
            }
        }

        // Reserve a tight upper bound for the arena. Binaries live in
        // bin_watchers (and original_binaries for verifyModel), not in
        // the arena, so only length-3+ originals contribute here.
        // Along the way, tally how many long-clause watchers each
        // literal will receive so we can pre-size watcher lists and
        // skip the initial zero→8 growth alloc on first attach.
        var total_slots: usize = 0;
        var original_binary_count: usize = 0;
        const watch_counts = try allocator.alloc(u32, @as(usize, formula.num_vars) * 2);
        defer allocator.free(watch_counts);
        @memset(watch_counts, 0);
        for (formula.clauses.items) |lits| {
            if (lits.len >= 3) {
                total_slots += lits.len + header_slots;
                watch_counts[lits[0].negate().raw] += 1;
                watch_counts[lits[1].negate().raw] += 1;
            }
            if (lits.len == 2) original_binary_count += 1;
        }
        try self.arena.ensureTotalCapacity(allocator, total_slots);
        errdefer self.arena.deinit(allocator);
        try self.original_binaries.ensureTotalCapacity(allocator, original_binary_count);
        for (self.watchers, watch_counts) |*w, n| {
            if (n > 0) try w.ensureTotalCapacity(allocator, n);
        }

        for (formula.clauses.items) |lits| {
            if (self.unsat_at_init) continue;
            if (lits.len == 0) {
                self.unsat_at_init = true;
                continue;
            }
            if (lits.len == 1) {
                const lit = lits[0];
                const val = self.assignment.valueOfLiteral(lit);
                if (val == .@"false") {
                    self.unsat_at_init = true;
                } else if (val == .unassigned) {
                    try self.assignment.assign(lit, Reason.none);
                }
                continue;
            }
            if (lits.len == 2) {
                // Binaries skip the arena entirely. Originals are also
                // recorded in original_binaries so verifyModel can check
                // them at the end.
                self.original_binaries.appendAssumeCapacity(.{ lits[0], lits[1] });
                try self.bin_watchers[lits[0].negate().raw].append(
                    allocator,
                    .{ .other = lits[1] },
                );
                try self.bin_watchers[lits[1].negate().raw].append(
                    allocator,
                    .{ .other = lits[0] },
                );
                continue;
            }
            const cref = try self.addClauseToArena(lits, false, 0);
            try self.attachWatches(cref);
        }

        return self;
    }

    pub fn deinit(self: *Solver) void {
        self.arena.deinit(self.allocator);
        for (self.watchers) |*w| w.deinit(self.allocator);
        self.allocator.free(self.watchers);
        for (self.bin_watchers) |*w| w.deinit(self.allocator);
        self.allocator.free(self.bin_watchers);
        self.original_binaries.deinit(self.allocator);
        self.allocator.free(self.activities);
        self.allocator.free(self.analyze_seen);
        self.analyze_learned.deinit(self.allocator);
        self.analyze_levels.deinit(self.allocator);
        self.analyze_to_clear.deinit(self.allocator);
        self.analyze_stack.deinit(self.allocator);
        self.learned_clauses.deinit(self.allocator);
        self.order_heap.deinit(self.allocator);
        self.assignment.deinit();
        self.* = undefined;
    }

    // --- clause accessors --------------------------------------------------

    inline fn clauseLen(self: *const Solver, cref: ClauseRef) u32 {
        return self.arena.items[cref].raw & len_mask;
    }

    inline fn clauseIsLearned(self: *const Solver, cref: ClauseRef) bool {
        return (self.arena.items[cref].raw & learned_bit) != 0;
    }

    inline fn clauseIsDeleted(self: *const Solver, cref: ClauseRef) bool {
        return (self.arena.items[cref].raw & deleted_bit) != 0;
    }

    // --- DRAT proof emission ---------------------------------------------
    //
    // A DRAT proof is a sequence of clause additions ("a" lines, or no
    // prefix) and deletions ("d " lines), terminated by the empty clause
    // `0\n` once the solver has derived UNSAT. The input formula is
    // implicit — the proof only describes derived clauses. Checkers like
    // `drat-trim` replay the proof against the original .cnf to verify
    // UNSAT verdicts, which most SAT Competition tracks require.
    //
    // All three helpers are no-ops when proof_writer is null, so the
    // non-proof solve path pays only a load + branch per call.

    pub fn setProofWriter(self: *Solver, w: *std.Io.Writer) void {
        self.proof_writer = w;
    }

    fn proofAdd(self: *Solver, lits: []const Literal) !void {
        const w = self.proof_writer orelse return;
        for (lits) |lit| try w.print("{d} ", .{lit.toDimacs()});
        try w.writeAll("0\n");
    }

    fn proofDelete(self: *Solver, cref: ClauseRef) !void {
        const w = self.proof_writer orelse return;
        try w.writeAll("d ");
        for (self.clauseLits(cref)) |lit| try w.print("{d} ", .{lit.toDimacs()});
        try w.writeAll("0\n");
    }

    fn proofEmpty(self: *Solver) !void {
        const w = self.proof_writer orelse return;
        try w.writeAll("0\n");
    }

    inline fn clauseLbd(self: *const Solver, cref: ClauseRef) u32 {
        return self.arena.items[cref + 1].raw;
    }

    inline fn clauseLits(self: *Solver, cref: ClauseRef) []Literal {
        const len = self.clauseLen(cref);
        const start: usize = @as(usize, cref) + header_slots;
        return self.arena.items[start .. start + len];
    }

    fn addClauseToArena(
        self: *Solver,
        lits: []const Literal,
        learned: bool,
        lbd: u32,
    ) !ClauseRef {
        const ref: ClauseRef = @intCast(self.arena.items.len);
        const header_raw: u32 = @as(u32, @intCast(lits.len)) |
            (if (learned) learned_bit else 0);
        try self.arena.append(self.allocator, .{ .raw = header_raw });
        try self.arena.append(self.allocator, .{ .raw = lbd });
        try self.arena.appendSlice(self.allocator, lits);
        return ref;
    }

    fn attachWatches(self: *Solver, cref: ClauseRef) !void {
        const lits = self.clauseLits(cref);
        // Binaries go through bin_watchers, not here. The arena never
        // holds a length-2 clause, so this must be length >= 3.
        std.debug.assert(lits.len >= 3);
        try self.watchers[lits[0].negate().raw].append(self.allocator, .{
            .clause = cref,
            .blocker = lits[1],
        });
        try self.watchers[lits[1].negate().raw].append(self.allocator, .{
            .clause = cref,
            .blocker = lits[0],
        });
    }

    // --- BCP ---------------------------------------------------------------

    // Two-watched-literal propagation with a specialized binary-clause
    // fast path. Processes the trail from propagation_head to the end,
    // firing unit clauses as they appear. Returns a Conflict on conflict
    // or null on clean completion.
    //
    // For each trail literal p we first sweep bin_watchers[p.raw]: every
    // entry is a 2-clause (¬p ∨ other), so a single lit_values load on
    // `other` resolves it — no arena touch, no compaction, no inner
    // search loop. Only after binaries are exhausted do we fall through
    // to the long-clause loop with its full two-watched dance.
    fn propagate(self: *Solver) !?Conflict {
        // Hoist into register-friendly locals. Neither pointer changes
        // across the body of propagate: assign() writes into lit_values
        // through the same allocation, and the arena is never grown
        // from inside propagate (addClauseToArena is only called from
        // solve, after analyze has returned). Zig sometimes
        // rematerialises `self.*.items.ptr` on every access; pinning
        // them here keeps both in a register.
        const lit_values = self.assignment.lit_values.ptr;
        const arena_ptr = self.arena.items.ptr;

        while (self.assignment.propagation_head < self.assignment.trail.items.len) {
            const p = self.assignment.trail.items[self.assignment.propagation_head];
            self.assignment.propagation_head += 1;
            self.stats.propagations += 1;

            // --- Binary fast path ------------------------------------------
            // bin_watchers entries are permanent (no compaction), so we
            // just iterate the snapshot. An `assign` below may cascade
            // onto the trail — that's handled by the outer while loop.
            const bws = self.bin_watchers[p.raw].items;
            for (bws) |b| {
                const v = lit_values[b.other.raw];
                if (v == .@"true") continue;
                if (v == .@"false") {
                    @branchHint(.cold);
                    // Conflict: clause (¬p ∨ b.other) has both lits
                    // falsified. p is on the trail, so ¬p is false;
                    // b.other is also false by the check above.
                    self.assignment.propagation_head = self.assignment.trail.items.len;
                    return Conflict{ .binary = .{ p.negate(), b.other } };
                }
                // Unit: force b.other, recording that the partner in the
                // implicit binary clause is ¬p.
                try self.assignment.assign(b.other, Reason.fromBinary(p.negate()));
            }

            // --- Long-clause path ------------------------------------------
            const ws = &self.watchers[p.raw];
            var i: usize = 0;
            var j: usize = 0;
            const end = ws.items.len;

            outer: while (i < end) {
                const w = ws.items[i];
                i += 1;

                // Blocker-satisfied is the dominant exit on the bench
                // (~70%). Tagging it .likely keeps the frontend
                // speculating past the clause load in the common case.
                if (lit_values[w.blocker.raw] == .@"true") {
                    @branchHint(.likely);
                    ws.items[j] = w;
                    j += 1;
                    continue;
                }

                // Prefetch the next watcher's clause line before we
                // touch this one's. The clause-body load was the top
                // instruction in the old perf profile at 12%; issuing
                // this prefetch hides its L2/L3 latency behind the
                // current iteration's arithmetic. Prefetching a stale
                // or past-end address is harmless.
                if (i < end) {
                    const next_cref = ws.items[i].clause;
                    @prefetch(arena_ptr + next_cref, .{ .locality = 3 });
                }

                const lits = self.clauseLits(w.clause);
                const false_lit = p.negate();

                if (lits[0].eql(false_lit)) {
                    lits[0] = lits[1];
                    lits[1] = false_lit;
                }
                std.debug.assert(lits[1].eql(false_lit));

                const other = lits[0];
                const new_w: Watcher = .{ .clause = w.clause, .blocker = other };

                if (!other.eql(w.blocker) and lit_values[other.raw] == .@"true") {
                    ws.items[j] = new_w;
                    j += 1;
                    continue;
                }

                var k: usize = 2;
                while (k < lits.len) : (k += 1) {
                    if (lit_values[lits[k].raw] != .@"false") {
                        lits[1] = lits[k];
                        lits[k] = false_lit;
                        try self.watchers[lits[1].negate().raw].append(
                            self.allocator,
                            .{ .clause = w.clause, .blocker = other },
                        );
                        continue :outer;
                    }
                }

                // No replacement — clause is unit or conflicting.
                ws.items[j] = new_w;
                j += 1;

                if (lit_values[other.raw] == .@"false") {
                    @branchHint(.cold);
                    while (i < end) : ({
                        i += 1;
                        j += 1;
                    }) {
                        ws.items[j] = ws.items[i];
                    }
                    ws.shrinkRetainingCapacity(j);
                    self.assignment.propagation_head = self.assignment.trail.items.len;
                    return Conflict{ .clause = w.clause };
                } else {
                    try self.assignment.assign(other, Reason.fromClause(w.clause));
                }
            }

            ws.shrinkRetainingCapacity(j);
        }

        return null;
    }

    // --- conflict analysis -------------------------------------------------

    // Iterative MiniSat-2.2 redundancy check. Returns true if the literal
    // of `start_var` (which is in the learned clause, with a non-null
    // reason) is implied by the rest of the learned clause, i.e. can be
    // removed by self-subsuming resolution.
    //
    // Walks back through reason chains; a literal `q` in some reason is
    // acceptable if it is already `seen` (i.e. already in the learned
    // clause or transitively marked) OR itself has a reason and its
    // decision level falls in `abstract_levels`, in which case we recurse.
    // Any other case — a decision, a level-0 literal, or a literal whose
    // level isn't in the mask — aborts the probe and rolls back any seen
    // flags set since entering this call. On success, the new seen flags
    // are kept (the caller clears analyze_to_clear at end of analyze).
    //
    // Precondition: `self.assignment.vars[start_var].reason` is non-none
    // and `analyze_stack` / `analyze_to_clear` have capacity >= num_vars.
    fn litRedundant(self: *Solver, start_var: u32, abstract_levels: u64) bool {
        self.analyze_stack.clearRetainingCapacity();
        self.analyze_stack.appendAssumeCapacity(start_var);
        const top = self.analyze_to_clear.items.len;

        // Scratch for synthesizing the 2-lit view of a binary reason.
        // lits[0] is the forced literal (which we skip below), so we
        // leave it undefined and only populate lits[1].
        var binary_scratch: [2]Literal = undefined;

        while (self.analyze_stack.items.len > 0) {
            const v = self.analyze_stack.pop().?;
            const reason = self.assignment.vars[v].reason;
            std.debug.assert(!reason.isNone());

            const lits: []const Literal = if (reason.isBinary()) blk: {
                binary_scratch[1] = reason.binaryOther();
                break :blk binary_scratch[0..2];
            } else self.clauseLits(reason.clauseRef());

            // lits[0] is the literal forced by this clause (== literal of
            // v) — skip it and scan the predecessor literals.
            var k: usize = 1;
            while (k < lits.len) : (k += 1) {
                const q = lits[k];
                const qv = q.variable();
                const qlevel = self.assignment.vars[qv].level;
                if (self.analyze_seen[qv] or qlevel == 0) continue;

                if (!self.assignment.vars[qv].reason.isNone() and
                    (abstract_levels & (@as(u64, 1) << @intCast(qlevel & 63))) != 0)
                {
                    self.analyze_seen[qv] = true;
                    self.analyze_stack.appendAssumeCapacity(qv);
                    self.analyze_to_clear.appendAssumeCapacity(qv);
                } else {
                    // Abort — undo the seen flags set during this probe.
                    for (self.analyze_to_clear.items[top..]) |cv| {
                        self.analyze_seen[cv] = false;
                    }
                    self.analyze_to_clear.shrinkRetainingCapacity(top);
                    return false;
                }
            }
        }
        return true;
    }

    // 1-UIP conflict analysis. Builds the learned clause into
    // analyze_learned, asserting literal at index 0, next-highest-level
    // literal at index 1 (ready to be the second watch). Returns the
    // backjump level.
    //
    // Accepts both arena-backed (long) and implicit (binary) conflicts.
    // When walking the reason chain, a binary reason is synthesized on
    // the fly into a 2-lit view [forced_lit, binaryOther] so the outer
    // loop is oblivious to the clause representation.
    fn analyze(self: *Solver, conflict: Conflict) !u32 {
        self.analyze_learned.clearRetainingCapacity();
        self.analyze_levels.clearRetainingCapacity();
        try self.analyze_learned.append(self.allocator, undefined);

        var counter: u32 = 0;
        var resolved: Literal = undefined;
        var has_resolved = false;
        var trail_idx: isize = @as(isize, @intCast(self.assignment.trail.items.len)) - 1;

        // Scratch for binary-conflict / binary-reason views. Stable for
        // the lifetime of one analyze call.
        var binary_scratch: [2]Literal = undefined;

        // Seed the lits slice from the initial conflict.
        var lits: []const Literal = switch (conflict) {
            .clause => |cref| self.clauseLits(cref),
            .binary => |two| blk: {
                binary_scratch = two;
                break :blk binary_scratch[0..2];
            },
        };

        while (true) {
            const start: usize = if (has_resolved) 1 else 0;
            for (lits[start..]) |q| {
                const v = q.variable();
                if (self.analyze_seen[v]) continue;
                const q_level = self.assignment.vars[v].level;
                if (q_level == 0) continue;

                self.analyze_seen[v] = true;
                self.bumpVarActivity(v);
                if (q_level >= self.assignment.level) {
                    counter += 1;
                } else {
                    try self.analyze_learned.append(self.allocator, q);
                }
            }

            while (trail_idx >= 0) {
                const tl = self.assignment.trail.items[@intCast(trail_idx)];
                if (self.analyze_seen[tl.variable()]) break;
                trail_idx -= 1;
            }
            std.debug.assert(trail_idx >= 0);
            resolved = self.assignment.trail.items[@intCast(trail_idx)];
            has_resolved = true;
            const rv = resolved.variable();
            self.analyze_seen[rv] = false;
            counter -= 1;
            trail_idx -= 1;

            if (counter == 0) break;

            // Refresh lits from the next reason on the chain. For a
            // binary reason, the clause is (resolved ∨ binaryOther)
            // and we only iterate lits[1..] next time anyway, so the
            // lits[0] slot just needs to parse as a Literal.
            const reason = self.assignment.vars[rv].reason;
            std.debug.assert(!reason.isNone());
            if (reason.isBinary()) {
                binary_scratch[0] = resolved;
                binary_scratch[1] = reason.binaryOther();
                lits = binary_scratch[0..2];
            } else {
                lits = self.clauseLits(reason.clauseRef());
            }
        }

        self.analyze_learned.items[0] = resolved.negate();

        // --- recursive clause minimization (MiniSat 2.2 litRedundant) ---
        // A literal p in the learned clause is redundant if it is implied
        // by the other literals — checked via iterative self-subsuming
        // resolution over reason chains. Typically removes 15–30% of
        // literals on uniform random 3-SAT, compounding into smaller
        // watcher lists and cheaper future propagate passes.
        {
            self.analyze_seen[self.analyze_learned.items[0].variable()] = true;

            var abstract_levels: u64 = 0;
            for (self.analyze_learned.items) |lit| {
                const lv = self.assignment.vars[lit.variable()].level;
                abstract_levels |= @as(u64, 1) << @intCast(lv & 63);
            }

            self.analyze_to_clear.clearRetainingCapacity();

            const original_len = self.analyze_learned.items.len;
            var wj: usize = 1;
            var wk: usize = 1;
            while (wk < original_len) : (wk += 1) {
                const lit = self.analyze_learned.items[wk];
                const lv = lit.variable();
                if (self.assignment.vars[lv].reason.isNone() or
                    !self.litRedundant(lv, abstract_levels))
                {
                    self.analyze_learned.items[wj] = lit;
                    wj += 1;
                } else {
                    // Removed — queue its seen flag for cleanup at the
                    // end alongside transitively-marked vars.
                    self.analyze_to_clear.appendAssumeCapacity(lv);
                }
            }
            self.analyze_learned.shrinkRetainingCapacity(wj);

            for (self.analyze_learned.items) |lit| {
                self.analyze_seen[lit.variable()] = false;
            }
            for (self.analyze_to_clear.items) |cv| {
                self.analyze_seen[cv] = false;
            }
        }

        var backjump: u32 = 0;
        if (self.analyze_learned.items.len > 1) {
            var max_i: usize = 1;
            var max_level = self.assignment.vars[self.analyze_learned.items[1].variable()].level;
            var k: usize = 2;
            while (k < self.analyze_learned.items.len) : (k += 1) {
                const lv = self.assignment.vars[self.analyze_learned.items[k].variable()].level;
                if (lv > max_level) {
                    max_level = lv;
                    max_i = k;
                }
            }
            const tmp = self.analyze_learned.items[1];
            self.analyze_learned.items[1] = self.analyze_learned.items[max_i];
            self.analyze_learned.items[max_i] = tmp;
            backjump = max_level;
        }

        return backjump;
    }

    fn computeLbd(self: *Solver, lits: []const Literal) u32 {
        self.analyze_levels.clearRetainingCapacity();
        outer: for (lits) |lit| {
            const lv = self.assignment.vars[lit.variable()].level;
            if (lv == 0) continue;
            for (self.analyze_levels.items) |existing| {
                if (existing == lv) continue :outer;
            }
            self.analyze_levels.append(self.allocator, lv) catch return @intCast(lits.len);
        }
        return @intCast(self.analyze_levels.items.len);
    }

    // --- VSIDS + branching -------------------------------------------------

    fn bumpVarActivity(self: *Solver, var_idx: u32) void {
        self.activities[var_idx] += self.var_inc;
        if (self.activities[var_idx] > rescale_threshold) {
            for (self.activities) |*a| a.* *= 1.0 / rescale_threshold;
            self.var_inc *= 1.0 / rescale_threshold;
        }
        self.order_heap.update(var_idx);
    }

    fn decayVarActivity(self: *Solver) void {
        self.var_inc *= 1.0 / var_decay;
    }

    fn pickBranching(self: *Solver) ?Literal {
        while (!self.order_heap.isEmpty()) {
            const v = self.order_heap.popMax();
            if (self.assignment.vars[v].value == .unassigned) {
                const neg = !self.assignment.saved_phases[v];
                return Literal.init(v, neg);
            }
        }
        return null;
    }

    fn backtrack(self: *Solver, target_level: u32) void {
        const a = &self.assignment;
        if (a.level <= target_level) return;
        const trail_start = a.trail_lim.items[target_level];
        var i: usize = a.trail.items.len;
        while (i > trail_start) {
            i -= 1;
            const lit = a.trail.items[i];
            const v = lit.variable();
            a.saved_phases[v] = (a.vars[v].value == .@"true");
            a.vars[v] = .{};
            const pos_slot = v << 1;
            a.lit_values[pos_slot] = .unassigned;
            a.lit_values[pos_slot | 1] = .unassigned;
            self.order_heap.insert(v);
        }
        a.trail.shrinkRetainingCapacity(trail_start);
        a.trail_lim.shrinkRetainingCapacity(target_level);
        a.level = target_level;
        if (a.propagation_head > trail_start) a.propagation_head = trail_start;
    }

    // --- main loop ---------------------------------------------------------

    pub fn solve(self: *Solver) !Result {
        if (self.unsat_at_init) {
            try self.proofEmpty();
            return .unsat;
        }
        if ((try self.propagate()) != null) {
            try self.proofEmpty();
            return .unsat;
        }

        while (true) {
            if (interrupted.load(.monotonic)) return .unknown;

            if (try self.propagate()) |conflict| {
                self.stats.conflicts += 1;
                self.conflicts_since_restart += 1;
                if (self.assignment.level == 0) {
                    try self.proofEmpty();
                    return .unsat;
                }

                const backjump_level = try self.analyze(conflict);

                // Snapshot trail length at the conflict point — used as
                // the blocker sample below. Must be taken before backtrack.
                const conflict_trail_f: f64 = @floatFromInt(self.assignment.trail.items.len);

                self.backtrack(backjump_level);

                const learned_len = self.analyze_learned.items.len;
                const lbd: u32 = if (learned_len == 1)
                    1
                else
                    self.computeLbd(self.analyze_learned.items);
                const lbd_f: f64 = @floatFromInt(lbd);

                // Bias-corrected EMA update: value += alpha*(x - value),
                // bc += alpha*(1 - bc). The corrected estimate is value/bc.
                self.lbd_fast += lbd_fast_alpha * (lbd_f - self.lbd_fast);
                self.lbd_fast_bc += lbd_fast_alpha * (1 - self.lbd_fast_bc);
                self.lbd_slow += lbd_slow_alpha * (lbd_f - self.lbd_slow);
                self.lbd_slow_bc += lbd_slow_alpha * (1 - self.lbd_slow_bc);

                if (learned_len == 1) {
                    try self.proofAdd(self.analyze_learned.items);
                    try self.assignment.assign(self.analyze_learned.items[0], Reason.none);
                } else if (learned_len == 2) {
                    // Learned binary — skips the arena. Register both
                    // watch directions and assert the UIP with an inline
                    // binary reason. ReduceDB never touches bin_watchers,
                    // so the clause is implicitly permanent.
                    try self.proofAdd(self.analyze_learned.items);
                    const uip = self.analyze_learned.items[0];
                    const other = self.analyze_learned.items[1];
                    try self.bin_watchers[uip.negate().raw].append(
                        self.allocator,
                        .{ .other = other },
                    );
                    try self.bin_watchers[other.negate().raw].append(
                        self.allocator,
                        .{ .other = uip },
                    );
                    try self.assignment.assign(uip, Reason.fromBinary(other));
                    self.stats.learned += 1;
                } else {
                    try self.proofAdd(self.analyze_learned.items);
                    const cref = try self.addClauseToArena(
                        self.analyze_learned.items,
                        true,
                        lbd,
                    );
                    try self.learned_clauses.append(self.allocator, cref);
                    try self.attachWatches(cref);
                    // The UIP at index 0 is asserted under the new level.
                    // We read the literal *after* the append because the
                    // arena may have been reallocated; analyze_learned
                    // survives the append (it's a separate ArrayList).
                    try self.assignment.assign(
                        self.analyze_learned.items[0],
                        Reason.fromClause(cref),
                    );
                    self.stats.learned += 1;
                }

                self.decayVarActivity();

                // --- Glucose restart decision -------------------------
                // Bias-corrected ratio test: if recent LBD quality is
                // worse than the long-run baseline by `restart_ratio`,
                // pop back to root. Blocker vetoes when the CURRENT
                // conflict's stack is significantly deeper than the
                // recent average (search is making progress, keep it).
                const ready = self.conflicts_since_restart >= restart_min_conflicts;
                var should_restart = false;
                if (ready and self.lbd_fast_bc > 0 and self.lbd_slow_bc > 0) {
                    const fast_corrected = self.lbd_fast / self.lbd_fast_bc;
                    const slow_corrected = self.lbd_slow / self.lbd_slow_bc;
                    const trending_bad = fast_corrected > slow_corrected * restart_ratio;

                    var trail_blocks = false;
                    if (self.trail_fast_bc > 0) {
                        const trail_corrected = self.trail_fast / self.trail_fast_bc;
                        trail_blocks = conflict_trail_f > trail_corrected * trail_block_ratio;
                    }
                    should_restart = trending_bad and !trail_blocks;
                }

                // Update the trail EMA *after* the blocker check so we
                // compare this conflict against past history, not itself.
                self.trail_fast += lbd_fast_alpha * (conflict_trail_f - self.trail_fast);
                self.trail_fast_bc += lbd_fast_alpha * (1 - self.trail_fast_bc);

                // ReduceDB runs on its own conflict-count budget, and
                // only at level 0 — piggyback on a restart when the
                // budget and the max_learned threshold both agree.
                const should_reduce = self.stats.conflicts >= self.next_reduce and
                    self.learned_clauses.items.len > self.max_learned;

                if (should_restart or should_reduce) {
                    if (should_restart) {
                        self.stats.restarts += 1;
                        self.conflicts_since_restart = 0;
                    }
                    self.backtrack(0);
                    if (should_reduce) {
                        try self.reduceDB();
                        self.max_learned = (self.max_learned * 11) / 10;
                        self.reduce_interval += reduce_grow;
                        self.next_reduce = self.stats.conflicts + self.reduce_interval;
                    }
                }
            } else {
                const lit = self.pickBranching() orelse return .sat;
                self.stats.decisions += 1;
                try self.assignment.pushDecisionLevel();
                try self.assignment.assign(lit, Reason.none);
            }
        }
    }

    pub fn verifyModel(self: *Solver) bool {
        // Walk only the original, non-deleted clauses. (Learned clauses
        // are implied by the originals, and deleted clauses are holes in
        // the arena that no longer participate in the problem.)
        var cref: ClauseRef = 0;
        while (cref < self.arena.items.len) {
            const header = self.arena.items[cref].raw;
            const len = header & len_mask;
            const is_learned = (header & learned_bit) != 0;
            const is_deleted = (header & deleted_bit) != 0;
            if (!is_learned and !is_deleted) {
                var satisfied = false;
                var k: usize = 0;
                while (k < len) : (k += 1) {
                    const lit = self.arena.items[cref + header_slots + k];
                    if (self.assignment.valueOfLiteral(lit) == .@"true") {
                        satisfied = true;
                        break;
                    }
                }
                if (!satisfied) return false;
            }
            cref += header_slots + len;
        }
        // Original binaries don't live in the arena — check them separately.
        for (self.original_binaries.items) |pair| {
            if (self.assignment.valueOfLiteral(pair[0]) != .@"true" and
                self.assignment.valueOfLiteral(pair[1]) != .@"true")
            {
                return false;
            }
        }
        return true;
    }

    // ---- Clause DB reduction --------------------------------------------
    //
    // Called at level 0 after a restart, when the learned clause count has
    // outgrown `max_learned`. Keeps the better half (by LBD — lower is
    // better). Clauses that are currently reasons for trail literals are
    // "locked" and must never be deleted, since `analyze` follows reasons.
    // Glue clauses (LBD <= 2) are also kept unconditionally — they are
    // empirically the most useful learned clauses.
    //
    // Dead clauses stay in the arena as holes; this avoids rewriting
    // ClauseRefs. BCP never visits them because we also strip their
    // watchers from every watcher list. Proper arena compaction can come
    // later if the holes become a memory problem.
    fn reduceDB(self: *Solver) !void {
        std.debug.assert(self.assignment.level == 0);

        // Collect the set of arena-backed clauses currently serving as
        // reasons on the trail. These are locked. Binary reasons inline
        // their partner literal and don't reference the arena, so they
        // don't participate in locking.
        var locked: std.AutoHashMap(ClauseRef, void) = .init(self.allocator);
        defer locked.deinit();
        for (self.assignment.trail.items) |lit| {
            const r = self.assignment.vars[lit.variable()].reason;
            if (r.isNone() or r.isBinary()) continue;
            try locked.put(r.clauseRef(), {});
        }

        // Build the deletion candidate list: learned, non-deleted,
        // non-locked, non-glue.
        const Candidate = struct { cref: ClauseRef, lbd: u32 };
        var candidates: std.ArrayList(Candidate) = .empty;
        defer candidates.deinit(self.allocator);
        try candidates.ensureTotalCapacity(
            self.allocator,
            self.learned_clauses.items.len,
        );
        for (self.learned_clauses.items) |cref| {
            if (self.clauseIsDeleted(cref)) continue;
            if (locked.contains(cref)) continue;
            const lbd = self.clauseLbd(cref);
            if (lbd <= 2) continue;
            candidates.appendAssumeCapacity(.{ .cref = cref, .lbd = lbd });
        }

        // Worst first (highest LBD first) so we can slice off the front.
        std.mem.sort(Candidate, candidates.items, {}, struct {
            fn lessThan(_: void, a: Candidate, b: Candidate) bool {
                return a.lbd > b.lbd;
            }
        }.lessThan);

        const to_delete = candidates.items.len / 2;
        for (candidates.items[0..to_delete]) |c| {
            try self.proofDelete(c.cref);
            self.arena.items[c.cref].raw |= deleted_bit;
        }
        self.stats.reductions += 1;
        self.stats.deleted += to_delete;

        // Sweep watcher lists: drop any watcher that points at a deleted
        // clause. One pass per list, O(total watchers).
        for (self.watchers) |*wlist| {
            var j: usize = 0;
            for (wlist.items) |w| {
                if (!self.clauseIsDeleted(w.clause)) {
                    wlist.items[j] = w;
                    j += 1;
                }
            }
            wlist.shrinkRetainingCapacity(j);
        }

        // Compact the learned_clauses index so the next reduceDB doesn't
        // waste time re-scanning dead entries.
        var j: usize = 0;
        for (self.learned_clauses.items) |cref| {
            if (!self.clauseIsDeleted(cref)) {
                self.learned_clauses.items[j] = cref;
                j += 1;
            }
        }
        self.learned_clauses.shrinkRetainingCapacity(j);
    }
};

// ---------------------------------------------------------------------------
// VSIDS order heap (binary max-heap keyed by activity).
// ---------------------------------------------------------------------------

const OrderHeap = struct {
    heap: std.ArrayList(u32),
    pos: []i32,
    activities: []const f64,

    fn init(allocator: Allocator, num_vars: u32, activities: []const f64) !OrderHeap {
        const pos = try allocator.alloc(i32, num_vars);
        @memset(pos, -1);
        return .{
            .heap = try std.ArrayList(u32).initCapacity(allocator, num_vars),
            .pos = pos,
            .activities = activities,
        };
    }

    fn deinit(self: *OrderHeap, allocator: Allocator) void {
        self.heap.deinit(allocator);
        allocator.free(self.pos);
    }

    fn isEmpty(self: *const OrderHeap) bool {
        return self.heap.items.len == 0;
    }

    fn gt(self: *const OrderHeap, a: u32, b: u32) bool {
        return self.activities[a] > self.activities[b];
    }

    fn siftUp(self: *OrderHeap, start: usize) void {
        var i = start;
        const x = self.heap.items[i];
        while (i > 0) {
            const parent_i = (i - 1) / 2;
            const parent = self.heap.items[parent_i];
            if (!self.gt(x, parent)) break;
            self.heap.items[i] = parent;
            self.pos[parent] = @intCast(i);
            i = parent_i;
        }
        self.heap.items[i] = x;
        self.pos[x] = @intCast(i);
    }

    fn siftDown(self: *OrderHeap, start: usize) void {
        var i = start;
        const x = self.heap.items[i];
        const n = self.heap.items.len;
        while (true) {
            const left = 2 * i + 1;
            if (left >= n) break;
            var child = left;
            const right = left + 1;
            if (right < n and self.gt(self.heap.items[right], self.heap.items[left])) {
                child = right;
            }
            if (!self.gt(self.heap.items[child], x)) break;
            self.heap.items[i] = self.heap.items[child];
            self.pos[self.heap.items[i]] = @intCast(i);
            i = child;
        }
        self.heap.items[i] = x;
        self.pos[x] = @intCast(i);
    }

    fn insert(self: *OrderHeap, v: u32) void {
        if (self.pos[v] != -1) return;
        self.heap.appendAssumeCapacity(v);
        self.pos[v] = @intCast(self.heap.items.len - 1);
        self.siftUp(self.heap.items.len - 1);
    }

    fn update(self: *OrderHeap, v: u32) void {
        if (self.pos[v] == -1) return;
        self.siftUp(@intCast(self.pos[v]));
    }

    fn popMax(self: *OrderHeap) u32 {
        const top = self.heap.items[0];
        self.pos[top] = -1;
        if (self.heap.items.len == 1) {
            self.heap.shrinkRetainingCapacity(0);
            return top;
        }
        const last = self.heap.items[self.heap.items.len - 1];
        self.heap.items[0] = last;
        self.pos[last] = 0;
        self.heap.shrinkRetainingCapacity(self.heap.items.len - 1);
        self.siftDown(0);
        return top;
    }
};

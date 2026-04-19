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

// Rephase cadence. Every `rephase_next` conflicts, the solver backs to
// level 0 and rotates `saved_phases` through a small family of
// polarities (best / original / inverse / random) so phase saving can
// escape local minima. The interval grows geometrically so late search
// doesn't thrash the branching heuristic.
const rephase_initial: u64 = 1000;
const rephase_grow_num: u64 = 3;
const rephase_grow_den: u64 = 2;

// Failed literal probing (FLP) — cheapest inprocessing technique that
// actually derives new facts. At level 0, for a top-K slice of active
// unassigned variables, we try both polarities at a throw-away
// decision level 1 and propagate. A conflict in that probe means the
// opposite polarity is implied by the formula, so we assert it as a
// root-level unit and DRAT-log the addition. Only runs at level 0 and
// only touches the level-1 scratch trail, so it slots cleanly between
// a restart and the next decision without disturbing the search state.
//
// probe_budget_num/_den controls how much work each probe call may do
// relative to the propagations accumulated since the last probe; the
// outer interval grows geometrically so inprocessing doesn't dominate
// on long searches.
const probe_initial_interval: u64 = 10_000;
const probe_grow_num: u64 = 3;
const probe_grow_den: u64 = 2;
const probe_budget_num: u64 = 1;
const probe_budget_den: u64 = 10;
const probe_max_vars: usize = 1024;

// Vivification — at level 0, walk low-LBD learned clauses and assume
// the negation of each literal in turn at a throwaway decision level.
// If BCP derives a conflict at position i, then the prefix C[0..i+1]
// is already implied by the formula, so the clause is replaced by
// that shorter version; if BCP derives a later literal of C to
// *true*, the same prefix shrink applies for a different reason
// (¬C[0..i] ⊢ C[j>i]). Lits already falsified at level 0 are just
// dropped in place. Targets LBD ≤ 6 because glue-adjacent clauses
// are the ones whose BCP cost compounds through long searches, and
// shrink success rate on high-LBD noise is too low to pay the probe.
const vivify_initial_interval: u64 = 15_000;
const vivify_grow_num: u64 = 3;
const vivify_grow_den: u64 = 2;
const vivify_budget_num: u64 = 2;
const vivify_budget_den: u64 = 10;
const vivify_lbd_cap: u32 = 6;

// Chronological backtracking gate (Möhle/Biere 2018, Kissat default).
// When a learned clause would jump more than this many levels down from
// the conflict point, we backtrack by exactly one decision level instead
// — the intuition is that long jumps destroy useful assignments and the
// chronological path re-derives the same learned clause on the way down.
// The UIP is still asserted at its natural (resolution) level via
// assignAtLevel, so the trail goes out-of-order; analyze and backtrack
// are level-aware rather than position-aware to accommodate this.
const chrono_level_gap: u32 = 100;

// Which polarity strategy the next rephase will apply. We cycle
// through the four in order; `.best` copies the trail-peak snapshot,
// `.original` resets to the solver's default (all-false), `.inverse`
// flips every current saved phase, and `.random` seeds a fresh set
// from a deterministic PRNG so reruns are reproducible.
const RephaseMode = enum { best, original, inverse, random };

pub const Stats = struct {
    decisions: u64 = 0,
    propagations: u64 = 0,
    conflicts: u64 = 0,
    restarts: u64 = 0,
    learned: u64 = 0,
    reductions: u64 = 0,
    deleted: u64 = 0,
    rephases: u64 = 0,
    chronos: u64 = 0,
    probings: u64 = 0,
    flp_units: u64 = 0,
    vivifies: u64 = 0,
    vivified: u64 = 0,
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

    // Rephase state. `best_trail_len` tracks the longest partial
    // assignment we've ever seen at a conflict point — each new peak
    // writes its polarities into assignment.best_phases. The trigger
    // cadence is independent of restart/reduce, and the mode cycles
    // round-robin every time rephase() runs.
    best_trail_len: usize,
    rephase_next: u64,
    rephase_interval: u64,
    rephase_mode: RephaseMode,

    // Failed literal probing cadence. `next_probe` is the conflict
    // count that triggers the next run; `probe_interval` grows
    // geometrically. `props_at_last_probe` is a propagation-count
    // checkpoint used to size the per-call budget: we spend at most
    // `(current - last) × num/den` propagations inside a probe call.
    next_probe: u64,
    probe_interval: u64,
    props_at_last_probe: u64,

    // Vivification cadence. Same propagation-budget pattern as FLP,
    // independent conflict-count gate so inprocessing passes don't
    // collide with reduceDB on the same level-0 backtrack.
    next_vivify: u64,
    vivify_interval: u64,
    props_at_last_vivify: u64,

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
            .best_trail_len = 0,
            .rephase_next = rephase_initial,
            .rephase_interval = rephase_initial,
            .rephase_mode = .best,
            .next_probe = probe_initial_interval,
            .probe_interval = probe_initial_interval,
            .props_at_last_probe = 0,
            .next_vivify = vivify_initial_interval,
            .vivify_interval = vivify_initial_interval,
            .props_at_last_vivify = 0,
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

            // Under chronological backtracking the trail is not
            // monotonic in level, so the level at which a forced literal
            // "naturally" holds is max over the falsified clause lits
            // rather than the current decision level. For a binary (¬p ∨ b)
            // the only falsified lit is ¬p, so the force level is simply
            // p's level. For long clauses we compute the max when we hit
            // the unit case (see below).
            const p_level = self.assignment.vars[p.variable()].level;

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
                // Unit: force b.other at p's level (natural level for a
                // binary under chrono).
                try self.assignment.assignAtLevel(
                    b.other,
                    Reason.fromBinary(p.negate()),
                    p_level,
                );
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
                    // Natural force level = max level of the other lits
                    // in the clause (all of which are currently false).
                    // Classical trail ⇒ this collapses to self.level, so
                    // the expense only shows up on genuine chrono paths.
                    var force_level: u32 = p_level;
                    var m: usize = 2;
                    while (m < lits.len) : (m += 1) {
                        const lv = self.assignment.vars[lits[m].variable()].level;
                        if (lv > force_level) force_level = lv;
                    }
                    try self.assignment.assignAtLevel(
                        other,
                        Reason.fromClause(w.clause),
                        force_level,
                    );
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
    //
    // `conflict_level` is the maximum level of any literal in the
    // initial conflict. Under classical backtracking it equals the
    // current decision level; under chronological backtracking the
    // trail may be out-of-order and the conflict can fire at a level
    // below self.level, so the caller computes it from the conflict
    // lits and passes it in. All UIP-counter and trail-walk checks use
    // conflict_level in place of self.level.
    fn analyze(self: *Solver, conflict: Conflict, conflict_level: u32) !u32 {
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
                if (q_level >= conflict_level) {
                    counter += 1;
                } else {
                    try self.analyze_learned.append(self.allocator, q);
                }
            }

            // Walk the trail backwards. Under chrono the trail is not
            // monotonic in level, so a seen var at a lower level could
            // be interleaved with conflict-level entries — those belong
            // in the learned clause (they went through the .else branch
            // above), not as resolution candidates, so skip them.
            while (trail_idx >= 0) {
                const tl = self.assignment.trail.items[@intCast(trail_idx)];
                const tv = tl.variable();
                if (self.analyze_seen[tv] and
                    self.assignment.vars[tv].level == conflict_level)
                {
                    break;
                }
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

    // Rotate `saved_phases` through the rephase family. Called only at
    // level 0 — the search tree has already been torn down and we're
    // rebiasing the *next* descent, not perturbing an active trail.
    //
    // best    → copy the deepest-trail snapshot (best_phases) in.
    // original → reset to the solver default (all-false == "try
    //            negative first" under pickBranching's neg = !saved rule).
    // inverse → flip every saved phase; lets us probe the complementary
    //           neighborhood of wherever saving had drifted to.
    // random  → deterministic PRNG seeded by conflict count. Reruns are
    //           reproducible and bench diffs stay meaningful.
    fn rephase(self: *Solver) void {
        std.debug.assert(self.assignment.level == 0);
        const saved = self.assignment.saved_phases;
        switch (self.rephase_mode) {
            .best => @memcpy(saved, self.assignment.best_phases),
            .original => @memset(saved, false),
            .inverse => {
                for (saved) |*b| b.* = !b.*;
            },
            .random => {
                var rng = std.Random.DefaultPrng.init(self.stats.conflicts);
                const r = rng.random();
                for (saved) |*b| b.* = r.boolean();
            },
        }
        self.rephase_mode = switch (self.rephase_mode) {
            .best => .original,
            .original => .inverse,
            .inverse => .random,
            .random => .best,
        };
        self.stats.rephases += 1;
    }

    // Failed literal probing pass. Returns .unsat if the probe (or its
    // follow-up propagation) derives an empty clause at level 0,
    // otherwise null — the solver continues its normal search. Expects
    // self.level == 0 and propagation to have reached fixed point; both
    // are guaranteed by the caller gating this on the post-restart
    // path in solve().
    //
    // For each top-K active unassigned variable, try its saved polarity
    // at a throw-away level 1 and propagate. A conflict means the
    // opposite polarity is entailed by the formula plus level-0 facts,
    // so we pop the probe, assert the opposite as a real level-0 unit,
    // emit the DRAT addition, and re-propagate. If that re-propagation
    // itself conflicts, the whole formula is UNSAT. Otherwise retry the
    // other polarity (unless the variable has meanwhile been assigned
    // by a cascade from a different unit derivation).
    fn probe(self: *Solver) !?Result {
        std.debug.assert(self.assignment.level == 0);
        self.stats.probings += 1;

        const props_start = self.stats.propagations;
        const delta = if (props_start > self.props_at_last_probe)
            props_start - self.props_at_last_probe
        else
            0;
        const budget: u64 = (delta * probe_budget_num) / probe_budget_den;
        self.props_at_last_probe = props_start;

        var candidates: std.ArrayList(u32) = .empty;
        defer candidates.deinit(self.allocator);
        try candidates.ensureTotalCapacity(self.allocator, self.num_vars);
        for (self.assignment.vars, 0..) |vi, idx| {
            if (vi.value == .unassigned) {
                candidates.appendAssumeCapacity(@intCast(idx));
            }
        }
        std.mem.sort(u32, candidates.items, self.activities, struct {
            fn lessThan(acts: []f64, a: u32, b: u32) bool {
                return acts[a] > acts[b];
            }
        }.lessThan);

        const k = @min(candidates.items.len, probe_max_vars);

        var probed: usize = 0;
        while (probed < k) : (probed += 1) {
            if (budget > 0 and self.stats.propagations - props_start > budget) break;

            const v = candidates.items[probed];

            // Try up to two polarities per variable. After the first
            // succeeds or fails, the second is attempted only if v is
            // still unassigned (a cascade from an earlier probe can
            // have fixed it).
            var iter: u32 = 0;
            while (iter < 2) : (iter += 1) {
                if (self.assignment.vars[v].value != .unassigned) break;

                const first_neg = !self.assignment.saved_phases[v];
                const neg = if (iter == 0) first_neg else !first_neg;
                const probe_lit = Literal.init(v, neg);

                try self.assignment.pushDecisionLevel();
                try self.assignment.assign(probe_lit, Reason.none);
                const conflict = try self.propagate();
                self.backtrack(0);

                if (conflict != null) {
                    const unit = probe_lit.negate();
                    try self.proofAdd(&.{unit});
                    try self.assignment.assign(unit, Reason.none);
                    self.stats.flp_units += 1;
                    if ((try self.propagate()) != null) {
                        try self.proofEmpty();
                        return .unsat;
                    }
                }
            }
        }

        return null;
    }

    // Vivification pass. Attempts to shrink low-LBD learned clauses by
    // assuming the negation of each literal in turn at a fresh decision
    // level and running BCP. Three outcomes per literal l at position i:
    //
    //   * l is already level-0 true   → clause is subsumed by a unit;
    //                                   delete it (emit DRAT del).
    //   * l is already level-0 false  → drop l from the scratch clause;
    //                                   no decision pushed.
    //   * l is unassigned             → push decision level, assign ¬l,
    //                                   propagate.
    //     - conflict              → scratch[0..i+1] is RUP-implied;
    //                               replace the clause with that shorter
    //                               disjunction.
    //     - propagates scratch[k] true (for some k > i):
    //                               same implication, same shrink to
    //                               scratch[0..i+1] (with scratch[i] = l
    //                               already the current position).
    //     - propagates scratch[k] false: l is redundant given the
    //                               earlier decisions; drop without
    //                               pushing.
    //
    // Returns .unsat if any shrink lands on an empty clause or derives
    // a conflicting level-0 unit; otherwise null. Preconditions: level 0,
    // BCP is at fixed point.
    //
    // Memory safety: addClauseToArena may reallocate the arena and
    // invalidate outstanding `clauseLits` slices. We copy each candidate
    // into `scratch` up-front and hold no arena slice across the decision
    // loop. The `candidates` list is snapshotted before any mutations.
    //
    // Deleted-clause watcher sweep: shrunk/subsumed clauses leave their
    // watchers dangling in `watchers[...]` pointing at deleted_bit-set
    // arena slots. Propagate does not check `clauseIsDeleted`, so we must
    // sweep watcher lists before returning — same invariant reduceDB
    // maintains after its own deletion pass.
    fn vivify(self: *Solver) !?Result {
        std.debug.assert(self.assignment.level == 0);
        self.stats.vivifies += 1;

        const props_start = self.stats.propagations;
        const delta = if (props_start > self.props_at_last_vivify)
            props_start - self.props_at_last_vivify
        else
            0;
        const budget: u64 = (delta * vivify_budget_num) / vivify_budget_den;
        self.props_at_last_vivify = props_start;

        // Snapshot candidates now — addClauseToArena below may reallocate
        // and mutate learned_clauses during the loop, and we want stable
        // targets.
        var candidates: std.ArrayList(ClauseRef) = .empty;
        defer candidates.deinit(self.allocator);
        for (self.learned_clauses.items) |cref| {
            if (self.clauseIsDeleted(cref)) continue;
            if (self.clauseLbd(cref) > vivify_lbd_cap) continue;
            try candidates.append(self.allocator, cref);
        }

        var scratch: std.ArrayList(Literal) = .empty;
        defer scratch.deinit(self.allocator);

        var any_deleted = false;

        outer: for (candidates.items) |cref| {
            if (budget > 0 and self.stats.propagations - props_start > budget) break;
            if (self.clauseIsDeleted(cref)) continue;

            // Copy lits before any decision-level push. Arena slices are
            // only safe between allocations; we intentionally don't hold
            // one across propagate().
            const lits_now = self.clauseLits(cref);
            scratch.clearRetainingCapacity();
            try scratch.ensureTotalCapacity(self.allocator, lits_now.len);
            scratch.appendSliceAssumeCapacity(lits_now);

            // Locked-clause check: if this clause is currently a reason
            // for a level-0 literal, mutating it would break reason
            // chains. Skip — those are rare and analyze's level-0 path
            // tolerates their survival.
            var locked = false;
            for (scratch.items) |lit| {
                const vi = self.assignment.vars[lit.variable()];
                if (vi.level == 0 and !vi.reason.isNone() and
                    !vi.reason.isBinary() and vi.reason.clauseRef() == cref)
                {
                    locked = true;
                    break;
                }
            }
            if (locked) continue;

            var shrink_len: ?usize = null;
            var subsumed = false;

            var i: usize = 0;
            while (i < scratch.items.len) {
                const lit = scratch.items[i];
                const vi = self.assignment.vars[lit.variable()];

                if (vi.level == 0 and vi.value != .unassigned) {
                    if (self.assignment.valueOfLiteral(lit) == .@"true") {
                        subsumed = true;
                        break;
                    }
                    // level-0 false → redundant, drop without pushing.
                    _ = scratch.swapRemove(i);
                    continue;
                }

                const cur = self.assignment.valueOfLiteral(lit);
                if (cur == .@"true") {
                    // Propagated true by earlier ¬-decisions → prefix is
                    // implied. Keep this lit as the tail of the shrunken
                    // clause.
                    shrink_len = i + 1;
                    break;
                }
                if (cur == .@"false") {
                    // Propagated false → redundant given earlier lits;
                    // drop without pushing.
                    _ = scratch.swapRemove(i);
                    continue;
                }

                try self.assignment.pushDecisionLevel();
                try self.assignment.assign(lit.negate(), Reason.none);
                const conflict = try self.propagate();
                if (conflict != null) {
                    shrink_len = i + 1;
                    break;
                }
                i += 1;
            }

            self.backtrack(0);

            if (subsumed) {
                try self.proofDelete(cref);
                self.arena.items[cref].raw |= deleted_bit;
                self.stats.vivified += 1;
                any_deleted = true;
                continue :outer;
            }

            // Did anything actually shrink? Only count/apply if the
            // effective new length is strictly smaller than the original
            // stored length.
            const original_len = self.clauseLen(cref);
            const new_len: usize = shrink_len orelse scratch.items.len;
            if (new_len >= original_len) continue;

            const new_lits = scratch.items[0..new_len];

            if (new_len == 0) {
                try self.proofEmpty();
                return .unsat;
            }

            try self.proofAdd(new_lits);
            try self.proofDelete(cref);
            self.arena.items[cref].raw |= deleted_bit;
            any_deleted = true;
            self.stats.vivified += 1;

            if (new_len == 1) {
                const unit = new_lits[0];
                const val = self.assignment.valueOfLiteral(unit);
                if (val == .@"false") {
                    try self.proofEmpty();
                    return .unsat;
                }
                if (val == .unassigned) {
                    try self.assignment.assign(unit, Reason.none);
                }
            } else if (new_len == 2) {
                try self.bin_watchers[new_lits[0].negate().raw].append(
                    self.allocator,
                    .{ .other = new_lits[1] },
                );
                try self.bin_watchers[new_lits[1].negate().raw].append(
                    self.allocator,
                    .{ .other = new_lits[0] },
                );
            } else {
                const new_lbd = self.computeLbd(new_lits);
                const new_cref = try self.addClauseToArena(new_lits, true, new_lbd);
                try self.learned_clauses.append(self.allocator, new_cref);
                try self.attachWatches(new_cref);
            }
        }

        // Watcher sweep — drop entries pointing at any clause we marked
        // deleted this pass. Mirrors reduceDB's post-delete sweep so
        // propagate never dereferences a tombstoned arena slot.
        if (any_deleted) {
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

            var j: usize = 0;
            for (self.learned_clauses.items) |cref| {
                if (!self.clauseIsDeleted(cref)) {
                    self.learned_clauses.items[j] = cref;
                    j += 1;
                }
            }
            self.learned_clauses.shrinkRetainingCapacity(j);
        }

        // Any new level-0 unit we derived (from a 1-lit shrink) needs
        // propagating before we return to search. If that itself
        // conflicts, the formula is UNSAT.
        if ((try self.propagate()) != null) {
            try self.proofEmpty();
            return .unsat;
        }

        return null;
    }

    // Compacting backtrack. Starts at trail_lim[target_level] — a valid
    // lower bound because every entry below that index was assigned
    // before level target+1 was first entered — and walks forward. Each
    // entry at vars[v].level > target is popped (its value cleared,
    // phase saved, heap re-inserted); each entry ≤ target is kept and
    // shifted left into the compacted region.
    //
    // Under classical CDCL the trail is monotonic in level, so this
    // collapses to the old "slice off the tail" behaviour. Under
    // chronological backtracking, where earlier chrono-asserted literals
    // can live at lower levels than their trail neighbours, the compact
    // pass is required for correctness.
    fn backtrack(self: *Solver, target_level: u32) void {
        const a = &self.assignment;
        if (a.level <= target_level) return;
        const scan_start = a.trail_lim.items[target_level];
        var j: usize = scan_start;
        var i: usize = scan_start;
        const trail_items = a.trail.items;
        while (i < trail_items.len) : (i += 1) {
            const lit = trail_items[i];
            const v = lit.variable();
            if (a.vars[v].level > target_level) {
                a.saved_phases[v] = (a.vars[v].value == .@"true");
                a.vars[v] = .{};
                const pos_slot = v << 1;
                a.lit_values[pos_slot] = .unassigned;
                a.lit_values[pos_slot | 1] = .unassigned;
                self.order_heap.insert(v);
            } else {
                trail_items[j] = lit;
                j += 1;
            }
        }
        a.trail.shrinkRetainingCapacity(j);
        a.trail_lim.shrinkRetainingCapacity(target_level);
        a.level = target_level;
        // Re-propagate everything from the compact boundary on. Kept
        // literals at the current level may still have watcher work to
        // do against the new trail shape, and the UIP we're about to
        // chrono-assert will land at exactly this index.
        if (a.propagation_head > scan_start) a.propagation_head = scan_start;
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

                // Conflict level = max level of any lit in the falsified
                // clause. Under classical CDCL this is always self.level;
                // under chrono it can be lower (an asserted lit at a low
                // level conflicts with an existing assignment). A
                // conflict_level of 0 means the empty clause is implied
                // at the root — UNSAT.
                const conflict_level: u32 = switch (conflict) {
                    .clause => |cref| blk: {
                        var m: u32 = 0;
                        for (self.clauseLits(cref)) |lit| {
                            const lv = self.assignment.vars[lit.variable()].level;
                            if (lv > m) m = lv;
                        }
                        break :blk m;
                    },
                    .binary => |two| @max(
                        self.assignment.vars[two[0].variable()].level,
                        self.assignment.vars[two[1].variable()].level,
                    ),
                };
                if (conflict_level == 0) {
                    try self.proofEmpty();
                    return .unsat;
                }

                const backjump_level = try self.analyze(conflict, conflict_level);

                // Snapshot trail length at the conflict point — used as
                // the blocker sample below. Must be taken before backtrack.
                const conflict_trail_len = self.assignment.trail.items.len;
                const conflict_trail_f: f64 = @floatFromInt(conflict_trail_len);

                // Record a new trail-peak snapshot for rephase. We only
                // overwrite variables that are actually on the current
                // trail so peak-specific polarities persist across
                // shallower future conflicts. Doing this before backtrack
                // is essential — backtrack erases vars[v].value.
                if (conflict_trail_len > self.best_trail_len) {
                    for (self.assignment.trail.items) |tl| {
                        const v = tl.variable();
                        self.assignment.best_phases[v] =
                            (self.assignment.vars[v].value == .@"true");
                    }
                    self.best_trail_len = conflict_trail_len;
                }

                // Chronological gate: if the non-chrono backjump would
                // skip many levels, pop exactly one level instead and
                // re-assert the UIP at its resolution level so the
                // intervening work survives.
                const chrono = conflict_level > backjump_level + chrono_level_gap;
                const target_level: u32 = if (chrono)
                    conflict_level - 1
                else
                    backjump_level;
                if (chrono) self.stats.chronos += 1;
                self.backtrack(target_level);

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
                    // Top-level unit: always level 0, even when a chrono
                    // target left self.level > 0. assignAtLevel pins it
                    // to level 0 regardless of the current stack.
                    try self.assignment.assignAtLevel(
                        self.analyze_learned.items[0],
                        Reason.none,
                        0,
                    );
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
                    try self.assignment.assignAtLevel(
                        uip,
                        Reason.fromBinary(other),
                        backjump_level,
                    );
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
                    // UIP goes in at its resolution (backjump) level,
                    // not self.level — they diverge when chronological
                    // backtracking skipped the big jump.
                    try self.assignment.assignAtLevel(
                        self.analyze_learned.items[0],
                        Reason.fromClause(cref),
                        backjump_level,
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

                // Rephase also only fires at level 0. It's independent of
                // restart/reduce; when its budget is up we force a
                // level-0 backtrack so we can rewrite saved_phases.
                const should_rephase = self.stats.conflicts >= self.rephase_next;

                // FLP also only fires at level 0. Same pattern: gate on
                // the conflict budget, piggyback on a level-0 backtrack.
                const should_probe = self.stats.conflicts >= self.next_probe;

                // Vivification: independent cadence from reduceDB so
                // inprocessing passes don't starve on the max_learned
                // gate that reduceDB needs.
                const should_vivify = self.stats.conflicts >= self.next_vivify;

                if (should_restart or should_reduce or should_rephase or
                    should_probe or should_vivify)
                {
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
                    if (should_rephase) {
                        self.rephase();
                        self.rephase_interval =
                            (self.rephase_interval * rephase_grow_num) / rephase_grow_den;
                        self.rephase_next = self.stats.conflicts + self.rephase_interval;
                    }
                    if (should_probe) {
                        if (try self.probe()) |r| return r;
                        self.probe_interval =
                            (self.probe_interval * probe_grow_num) / probe_grow_den;
                        self.next_probe = self.stats.conflicts + self.probe_interval;
                    }
                    if (should_vivify) {
                        if (try self.vivify()) |r| return r;
                        self.vivify_interval =
                            (self.vivify_interval * vivify_grow_num) / vivify_grow_den;
                        self.next_vivify = self.stats.conflicts + self.vivify_interval;
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

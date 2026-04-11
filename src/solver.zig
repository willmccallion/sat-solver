const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const Formula = cnf.Formula;
const ClauseRef = cnf.ClauseRef;
const null_clause = cnf.null_clause;
const assignment_mod = @import("assignment.zig");
const Assignment = assignment_mod.Assignment;
const Value = assignment_mod.Value;

pub const Result = enum { sat, unsat, unknown };

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

const var_decay: f64 = 0.95;
const restart_base: u64 = 100;
const rescale_threshold: f64 = 1e100;

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
    assignment: Assignment,

    activities: []f64,
    var_inc: f64,
    order_heap: OrderHeap,

    analyze_seen: []bool,
    analyze_learned: std.ArrayList(Literal),
    analyze_levels: std.ArrayList(u32),

    learned_clauses: std.ArrayList(ClauseRef),
    max_learned: usize,

    luby_index: u64,
    next_restart: u64,
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
            .assignment = try Assignment.init(allocator, formula.num_vars),
            .activities = &.{},
            .var_inc = 1.0,
            .order_heap = undefined,
            .analyze_seen = &.{},
            .analyze_learned = .empty,
            .analyze_levels = .empty,
            .learned_clauses = .empty,
            .max_learned = @max(formula.clauses.items.len, 1000),
            .luby_index = 0,
            .next_restart = restart_base,
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

        self.activities = try allocator.alloc(f64, formula.num_vars);
        @memset(self.activities, 0);
        errdefer allocator.free(self.activities);

        self.analyze_seen = try allocator.alloc(bool, formula.num_vars);
        @memset(self.analyze_seen, false);
        errdefer allocator.free(self.analyze_seen);

        self.order_heap = try OrderHeap.init(allocator, formula.num_vars, self.activities);
        errdefer self.order_heap.deinit(allocator);
        {
            var v: u32 = 0;
            while (v < formula.num_vars) : (v += 1) {
                self.order_heap.insert(v);
            }
        }

        // Reserve a tight upper bound for the arena: every original clause
        // contributes (len + 2) slots. Learned clauses will extend it later.
        var total_slots: usize = 0;
        for (formula.clauses.items) |lits| total_slots += lits.len + header_slots;
        try self.arena.ensureTotalCapacity(allocator, total_slots);
        errdefer self.arena.deinit(allocator);

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
                    try self.assignment.assign(lit, null_clause);
                }
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
        self.allocator.free(self.activities);
        self.allocator.free(self.analyze_seen);
        self.analyze_learned.deinit(self.allocator);
        self.analyze_levels.deinit(self.allocator);
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
        std.debug.assert(lits.len >= 2);
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

    // Two-watched-literal propagation. Processes trail from propagation_head
    // to the end, firing unit clauses as they appear. Returns the conflict
    // clause on conflict, or null_clause on clean completion.
    fn propagate(self: *Solver) !ClauseRef {
        while (self.assignment.propagation_head < self.assignment.trail.items.len) {
            const p = self.assignment.trail.items[self.assignment.propagation_head];
            self.assignment.propagation_head += 1;
            self.stats.propagations += 1;

            const ws = &self.watchers[p.raw];
            var i: usize = 0;
            var j: usize = 0;
            const end = ws.items.len;

            outer: while (i < end) {
                const w = ws.items[i];
                i += 1;

                if (self.assignment.valueOfLiteral(w.blocker) == .@"true") {
                    ws.items[j] = w;
                    j += 1;
                    continue;
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

                if (!other.eql(w.blocker) and
                    self.assignment.valueOfLiteral(other) == .@"true")
                {
                    ws.items[j] = new_w;
                    j += 1;
                    continue;
                }

                var k: usize = 2;
                while (k < lits.len) : (k += 1) {
                    if (self.assignment.valueOfLiteral(lits[k]) != .@"false") {
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

                if (self.assignment.valueOfLiteral(other) == .@"false") {
                    while (i < end) : ({
                        i += 1;
                        j += 1;
                    }) {
                        ws.items[j] = ws.items[i];
                    }
                    ws.shrinkRetainingCapacity(j);
                    self.assignment.propagation_head = self.assignment.trail.items.len;
                    return w.clause;
                } else {
                    try self.assignment.assign(other, w.clause);
                }
            }

            ws.shrinkRetainingCapacity(j);
        }

        return null_clause;
    }

    // --- conflict analysis -------------------------------------------------

    // 1-UIP conflict analysis. Builds the learned clause into
    // analyze_learned, asserting literal at index 0, next-highest-level
    // literal at index 1 (ready to be the second watch). Returns the
    // backjump level.
    fn analyze(self: *Solver, conflict_ref: ClauseRef) !u32 {
        self.analyze_learned.clearRetainingCapacity();
        self.analyze_levels.clearRetainingCapacity();
        try self.analyze_learned.append(self.allocator, undefined);

        var counter: u32 = 0;
        var resolved: Literal = undefined;
        var has_resolved = false;
        var cref = conflict_ref;
        var trail_idx: isize = @as(isize, @intCast(self.assignment.trail.items.len)) - 1;

        while (true) {
            std.debug.assert(cref != null_clause);
            const lits = self.clauseLits(cref);

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
            cref = self.assignment.vars[rv].reason;
        }

        self.analyze_learned.items[0] = resolved.negate();

        for (self.analyze_learned.items[1..]) |lit| {
            self.analyze_seen[lit.variable()] = false;
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
            self.order_heap.insert(v);
        }
        a.trail.shrinkRetainingCapacity(trail_start);
        a.trail_lim.shrinkRetainingCapacity(target_level);
        a.level = target_level;
        if (a.propagation_head > trail_start) a.propagation_head = trail_start;
    }

    // --- main loop ---------------------------------------------------------

    pub fn solve(self: *Solver) !Result {
        if (self.unsat_at_init) return .unsat;
        if ((try self.propagate()) != null_clause) return .unsat;

        while (true) {
            const conflict = try self.propagate();
            if (conflict != null_clause) {
                self.stats.conflicts += 1;
                if (self.assignment.level == 0) return .unsat;

                const backjump_level = try self.analyze(conflict);
                self.backtrack(backjump_level);

                const learned_len = self.analyze_learned.items.len;
                if (learned_len == 1) {
                    try self.assignment.assign(self.analyze_learned.items[0], null_clause);
                } else {
                    const lbd = self.computeLbd(self.analyze_learned.items);
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
                    try self.assignment.assign(self.analyze_learned.items[0], cref);
                    self.stats.learned += 1;
                }

                self.decayVarActivity();

                if (self.stats.conflicts >= self.next_restart) {
                    self.luby_index += 1;
                    self.next_restart = self.stats.conflicts +
                        restart_base * luby(2, self.luby_index);
                    self.stats.restarts += 1;
                    self.backtrack(0);

                    // While we're at level 0, reduce the clause DB if
                    // learned clauses have piled up. Keeps BCP from
                    // dragging through garbage and bounds memory use on
                    // hard instances.
                    if (self.learned_clauses.items.len > self.max_learned) {
                        try self.reduceDB();
                        self.max_learned = (self.max_learned * 11) / 10;
                    }
                }
            } else {
                const lit = self.pickBranching() orelse return .sat;
                self.stats.decisions += 1;
                try self.assignment.pushDecisionLevel();
                try self.assignment.assign(lit, null_clause);
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

        // Collect the set of clauses currently serving as reasons on the
        // trail. These are locked.
        var locked: std.AutoHashMap(ClauseRef, void) = .init(self.allocator);
        defer locked.deinit();
        for (self.assignment.trail.items) |lit| {
            const r = self.assignment.vars[lit.variable()].reason;
            if (r != null_clause) try locked.put(r, {});
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
// Luby sequence — restart schedule.
// ---------------------------------------------------------------------------

fn luby(y: u64, x_in: u64) u64 {
    var size: u64 = 1;
    var seq: u32 = 0;
    var x = x_in;
    while (size < x + 1) {
        seq += 1;
        size = 2 * size + 1;
    }
    while (size != x + 1) {
        size = (size - 1) / 2;
        seq -= 1;
        x = x % size;
    }
    var result: u64 = 1;
    var i: u32 = 0;
    while (i < seq) : (i += 1) result *= y;
    return result;
}

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

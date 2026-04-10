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

const StoredClause = struct {
    lits: []Literal,
    learned: bool,
    lbd: u32,
};

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
};

pub const Solver = struct {
    allocator: Allocator,
    num_vars: u32,

    clauses: std.ArrayList(StoredClause),
    watchers: []std.ArrayList(Watcher),
    assignment: Assignment,

    activities: []f64,
    var_inc: f64,
    order_heap: OrderHeap,

    analyze_seen: []bool,
    analyze_learned: std.ArrayList(Literal),
    analyze_levels: std.ArrayList(u32),

    luby_index: u64,
    next_restart: u64,
    unsat_at_init: bool,

    stats: Stats,

    pub fn init(allocator: Allocator, formula: Formula) !Solver {
        var self: Solver = .{
            .allocator = allocator,
            .num_vars = formula.num_vars,
            .clauses = .empty,
            .watchers = &.{},
            .assignment = try Assignment.init(allocator, formula.num_vars),
            .activities = &.{},
            .var_inc = 1.0,
            .order_heap = undefined,
            .analyze_seen = &.{},
            .analyze_learned = .empty,
            .analyze_levels = .empty,
            .luby_index = 0,
            .next_restart = restart_base,
            .unsat_at_init = false,
            .stats = .{},
        };
        errdefer {
            self.assignment.deinit();
        }

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
        var v: u32 = 0;
        while (v < formula.num_vars) : (v += 1) {
            try self.order_heap.insert(allocator, v);
        }

        // Transfer the input formula's clauses. We take ownership of the literal
        // slices where possible to avoid an extra dup; unit clauses become
        // level-0 assignments and their slices are freed immediately.
        for (formula.clauses.items) |lits| {
            if (self.unsat_at_init) {
                allocator.free(lits);
                continue;
            }
            if (lits.len == 0) {
                allocator.free(lits);
                self.unsat_at_init = true;
                continue;
            }
            if (lits.len == 1) {
                const lit = lits[0];
                allocator.free(lits);
                const val = self.assignment.valueOfLiteral(lit);
                if (val == .@"false") {
                    self.unsat_at_init = true;
                } else if (val == .unassigned) {
                    try self.assignment.assign(lit, null_clause);
                }
                continue;
            }
            const cref: ClauseRef = @intCast(self.clauses.items.len);
            try self.clauses.append(allocator, .{
                .lits = lits,
                .learned = false,
                .lbd = 0,
            });
            try self.attachWatches(cref);
        }

        // The solver now owns all the literal slices; drop the input formula's
        // bookkeeping without freeing its contents.
        var owned = formula;
        owned.clauses.deinit(allocator);

        return self;
    }

    pub fn deinit(self: *Solver) void {
        for (self.clauses.items) |c| self.allocator.free(c.lits);
        self.clauses.deinit(self.allocator);
        for (self.watchers) |*w| w.deinit(self.allocator);
        self.allocator.free(self.watchers);
        self.allocator.free(self.activities);
        self.allocator.free(self.analyze_seen);
        self.analyze_learned.deinit(self.allocator);
        self.analyze_levels.deinit(self.allocator);
        self.order_heap.deinit(self.allocator);
        self.assignment.deinit();
        self.* = undefined;
    }

    fn attachWatches(self: *Solver, cref: ClauseRef) !void {
        const c = &self.clauses.items[cref];
        std.debug.assert(c.lits.len >= 2);
        try self.watchers[c.lits[0].negate().raw].append(self.allocator, .{
            .clause = cref,
            .blocker = c.lits[1],
        });
        try self.watchers[c.lits[1].negate().raw].append(self.allocator, .{
            .clause = cref,
            .blocker = c.lits[0],
        });
    }

    // Two-watched-literal BCP. Processes trail from propagation_head to the
    // end, firing unit clauses as they appear. Returns a conflict clause
    // reference on conflict, or null_clause if propagation completes cleanly.
    fn propagate(self: *Solver) !ClauseRef {
        var conflict: ClauseRef = null_clause;

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

                const clause = &self.clauses.items[w.clause];
                const false_lit = p.negate();

                if (clause.lits[0].eql(false_lit)) {
                    clause.lits[0] = clause.lits[1];
                    clause.lits[1] = false_lit;
                }
                std.debug.assert(clause.lits[1].eql(false_lit));

                const other = clause.lits[0];
                const new_w: Watcher = .{ .clause = w.clause, .blocker = other };

                if (!other.eql(w.blocker) and
                    self.assignment.valueOfLiteral(other) == .@"true")
                {
                    ws.items[j] = new_w;
                    j += 1;
                    continue;
                }

                // Scan for a replacement watch.
                var k: usize = 2;
                while (k < clause.lits.len) : (k += 1) {
                    if (self.assignment.valueOfLiteral(clause.lits[k]) != .@"false") {
                        clause.lits[1] = clause.lits[k];
                        clause.lits[k] = false_lit;
                        try self.watchers[clause.lits[1].negate().raw].append(
                            self.allocator,
                            .{ .clause = w.clause, .blocker = other },
                        );
                        continue :outer;
                    }
                }

                // No replacement; the clause is unit or conflicting.
                ws.items[j] = new_w;
                j += 1;

                if (self.assignment.valueOfLiteral(other) == .@"false") {
                    // Conflict — copy the remaining watchers verbatim so the
                    // list stays consistent, then bail out.
                    while (i < end) : ({
                        i += 1;
                        j += 1;
                    }) {
                        ws.items[j] = ws.items[i];
                    }
                    ws.shrinkRetainingCapacity(j);
                    self.assignment.propagation_head = self.assignment.trail.items.len;
                    conflict = w.clause;
                    return conflict;
                } else {
                    try self.assignment.assign(other, w.clause);
                }
            }

            ws.shrinkRetainingCapacity(j);
        }

        return conflict;
    }

    // 1-UIP conflict analysis. Builds a learned clause into analyze_learned,
    // with the asserting literal at index 0 and the second-highest level
    // literal at index 1 (so it can be watched immediately). Returns the
    // backjump level.
    fn analyze(self: *Solver, conflict_ref: ClauseRef) !u32 {
        self.analyze_learned.clearRetainingCapacity();
        self.analyze_levels.clearRetainingCapacity();
        try self.analyze_learned.append(self.allocator, undefined); // slot for UIP

        var counter: u32 = 0;
        var resolved: Literal = undefined;
        var has_resolved = false;
        var cref = conflict_ref;
        var trail_idx: isize = @as(isize, @intCast(self.assignment.trail.items.len)) - 1;

        while (true) {
            std.debug.assert(cref != null_clause);
            const clause = &self.clauses.items[cref];

            const start: usize = if (has_resolved) 1 else 0;
            for (clause.lits[start..]) |q| {
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

            // Walk back to the next seen literal at the current level.
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

        // Clear any remaining seen flags.
        for (self.analyze_learned.items[1..]) |lit| {
            self.analyze_seen[lit.variable()] = false;
        }

        // Determine backjump level and move the highest-level literal to
        // index 1 (the second watched slot).
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
        // LBD = number of distinct decision levels represented in the clause.
        // Uses analyze_levels as a scratch set; levels at 0 are skipped.
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

    pub fn solve(self: *Solver) !Result {
        if (self.unsat_at_init) return .unsat;
        if ((try self.propagate()) != null_clause) return .unsat;

        while (true) {
            const conflict = try self.propagate();
            if (conflict != null_clause) {
                self.stats.conflicts += 1;
                if (self.assignment.level == 0) return .unsat;

                const backjump_level = try self.analyze(conflict);
                self.assignment.popToLevel(backjump_level);

                const learned_len = self.analyze_learned.items.len;
                if (learned_len == 1) {
                    try self.assignment.assign(self.analyze_learned.items[0], null_clause);
                } else {
                    const owned = try self.allocator.dupe(Literal, self.analyze_learned.items);
                    const lbd = self.computeLbd(owned);
                    const cref: ClauseRef = @intCast(self.clauses.items.len);
                    try self.clauses.append(self.allocator, .{
                        .lits = owned,
                        .learned = true,
                        .lbd = lbd,
                    });
                    try self.attachWatches(cref);
                    try self.assignment.assign(owned[0], cref);
                    self.stats.learned += 1;
                }

                self.decayVarActivity();

                if (self.stats.conflicts >= self.next_restart) {
                    self.luby_index += 1;
                    self.next_restart = self.stats.conflicts + restart_base * luby(2, self.luby_index);
                    self.stats.restarts += 1;
                    self.assignment.popToLevel(0);
                }
            } else {
                const lit = self.pickBranching() orelse return .sat;
                self.stats.decisions += 1;
                try self.assignment.pushDecisionLevel();
                try self.assignment.assign(lit, null_clause);
            }
        }
    }

    pub fn verifyModel(self: *const Solver) bool {
        for (self.clauses.items) |c| {
            if (c.learned) continue;
            var satisfied = false;
            for (c.lits) |lit| {
                if (self.assignment.valueOfLiteral(lit) == .@"true") {
                    satisfied = true;
                    break;
                }
            }
            if (!satisfied) return false;
        }
        return true;
    }
};

// Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
// Returns y^(k) where k is the sequence index (0-based, starting at the
// first 1). Used to schedule restarts.
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

    fn insert(self: *OrderHeap, allocator: Allocator, v: u32) !void {
        if (self.pos[v] != -1) return;
        try self.heap.append(allocator, v);
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

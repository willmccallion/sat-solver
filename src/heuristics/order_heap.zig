const std = @import("std");
const Allocator = std.mem.Allocator;

// Activity decay per conflict, applied by growing the bump instead, and
// the activity at which every activity is rescaled to stay finite.
pub const var_decay: f64 = 0.95;
pub const rescale_threshold: f64 = 1e100;

// VSIDS order heap — binary max-heap keyed by per-variable activity.
// Standalone type: holds a slice view onto the solver's activity array
// and compares by dereferencing it. Insert / update / popMax are O(log n).
pub const OrderHeap = struct {
    heap: std.ArrayList(u32),
    // Each variable's index in `heap`, or `absent`.
    pos: []u32,
    activities: []const f64,

    const absent = std.math.maxInt(u32);

    pub fn init(allocator: Allocator, num_vars: u32, activities: []const f64) !OrderHeap {
        const pos = try allocator.alloc(u32, num_vars);
        errdefer allocator.free(pos);
        @memset(pos, absent);
        return .{
            .heap = try std.ArrayList(u32).initCapacity(allocator, num_vars),
            .pos = pos,
            .activities = activities,
        };
    }

    pub fn deinit(self: *OrderHeap, allocator: Allocator) void {
        self.heap.deinit(allocator);
        allocator.free(self.pos);
    }

    pub fn isEmpty(self: *const OrderHeap) bool {
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

    pub fn insert(self: *OrderHeap, v: u32) void {
        if (self.pos[v] != absent) return;
        self.heap.appendAssumeCapacity(v);
        self.pos[v] = @intCast(self.heap.items.len - 1);
        self.siftUp(self.heap.items.len - 1);
    }

    pub fn update(self: *OrderHeap, v: u32) void {
        if (self.pos[v] == absent) return;
        self.siftUp(self.pos[v]);
    }

    pub fn popMax(self: *OrderHeap) u32 {
        const top = self.heap.items[0];
        self.pos[top] = absent;
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

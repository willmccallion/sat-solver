const std = @import("std");
const Allocator = std.mem.Allocator;

// The `.cnf` files of a benchmark directory, sorted so that runs over it
// are reproducible.
pub const CnfNames = struct {
    items: [][]u8,

    pub fn list(gpa: Allocator, io: std.Io, dir: std.Io.Dir) !CnfNames {
        var names: std.ArrayList([]u8) = .empty;
        errdefer {
            for (names.items) |name| gpa.free(name);
            names.deinit(gpa);
        }
        var it = dir.iterate();
        while (try it.next(io)) |entry| {
            if (entry.kind != .file or !std.mem.endsWith(u8, entry.name, ".cnf")) continue;
            const name = try gpa.dupe(u8, entry.name);
            errdefer gpa.free(name);
            try names.append(gpa, name);
        }
        std.mem.sort([]u8, names.items, {}, lessThan);
        return .{ .items = try names.toOwnedSlice(gpa) };
    }

    pub fn deinit(self: CnfNames, gpa: Allocator) void {
        for (self.items) |name| gpa.free(name);
        gpa.free(self.items);
    }

    fn lessThan(_: void, a: []u8, b: []u8) bool {
        return std.mem.lessThan(u8, a, b);
    }
};

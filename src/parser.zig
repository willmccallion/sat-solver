const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("cnf.zig");
const Literal = cnf.Literal;
const Formula = cnf.Formula;

pub const ParseError = error{
    MissingHeader,
    DuplicateHeader,
    InvalidHeader,
    InvalidToken,
    VariableOutOfRange,
    UnterminatedClause,
    ClauseCountMismatch,
    OutOfMemory,
};

fn isSpace(b: u8) bool {
    return b == ' ' or b == '\t' or b == '\r' or b == '\n';
}

pub fn parse(allocator: Allocator, source: []const u8) ParseError!Formula {
    var formula = Formula.init(allocator);
    errdefer formula.deinit();

    var current: std.ArrayList(Literal) = .empty;
    defer current.deinit(allocator);

    var header_seen = false;
    var declared_clauses: u32 = 0;
    var i: usize = 0;

    while (i < source.len) {
        if (isSpace(source[i])) {
            i += 1;
            continue;
        }

        if (source[i] == 'c') {
            while (i < source.len and source[i] != '\n') i += 1;
            continue;
        }

        // SATLIB/DIMACS challenge format: a lone `%` marks the end of the
        // problem content. Anything after it (typically `0\n`) is ignored.
        if (source[i] == '%') break;

        if (source[i] == 'p') {
            if (header_seen) return error.DuplicateHeader;
            var line_end = i;
            while (line_end < source.len and source[line_end] != '\n') line_end += 1;
            const line = source[i..line_end];
            i = line_end;

            var it = std.mem.tokenizeAny(u8, line, " \t\r");
            const p_tok = it.next() orelse return error.InvalidHeader;
            if (!std.mem.eql(u8, p_tok, "p")) return error.InvalidHeader;
            const fmt_tok = it.next() orelse return error.InvalidHeader;
            if (!std.mem.eql(u8, fmt_tok, "cnf")) return error.InvalidHeader;
            const nv_tok = it.next() orelse return error.InvalidHeader;
            const nc_tok = it.next() orelse return error.InvalidHeader;
            if (it.next() != null) return error.InvalidHeader;

            formula.num_vars = std.fmt.parseInt(u32, nv_tok, 10) catch return error.InvalidHeader;
            declared_clauses = std.fmt.parseInt(u32, nc_tok, 10) catch return error.InvalidHeader;
            header_seen = true;
            continue;
        }

        if (!header_seen) return error.MissingHeader;

        var tok_end = i;
        while (tok_end < source.len and !isSpace(source[tok_end])) tok_end += 1;
        const token = source[i..tok_end];
        i = tok_end;

        const n = std.fmt.parseInt(i32, token, 10) catch return error.InvalidToken;
        if (n == 0) {
            try formula.addClause(current.items);
            current.clearRetainingCapacity();
        } else {
            const magnitude: u32 = @intCast(if (n < 0) -n else n);
            if (magnitude == 0 or magnitude > formula.num_vars) return error.VariableOutOfRange;
            try current.append(allocator, Literal.fromDimacs(n));
        }
    }

    if (!header_seen) return error.MissingHeader;
    if (current.items.len > 0) return error.UnterminatedClause;

    // Sanity check against the `p cnf N M` header. A large delta is
    // almost always a malformed file (missing `0` terminators or stray
    // lines that got silently joined into giant clauses), as seen in
    // SATLIB's dubois100.cnf. We accept a 5 % slack because some real
    // files have off-by-one header errors but are otherwise fine.
    const parsed: u32 = @intCast(formula.clauses.items.len);
    if (declared_clauses > 0) {
        const delta = if (parsed >= declared_clauses)
            parsed - declared_clauses
        else
            declared_clauses - parsed;
        const slack = (declared_clauses + 19) / 20; // 5 %
        if (delta > slack) return error.ClauseCountMismatch;
    }

    return formula;
}

const std = @import("std");
const Allocator = std.mem.Allocator;
const cnf = @import("core").cnf;
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
    FormulaTooLarge,
    ReadFailed,
    OutOfMemory,
};

// Caps the clause slots reserved from the header's declared count, so a
// bogus `p cnf` line cannot force a huge up-front allocation.
const max_reserved_clauses: usize = 1 << 26;

const Header = struct {
    num_vars: u32,
    num_clauses: u32,
};

// Streams a DIMACS CNF formula from `reader`; the input is never held in
// memory as a whole.
pub fn parse(allocator: Allocator, reader: *std.Io.Reader) ParseError!Formula {
    const header = try parseHeader(reader);
    var formula = Formula.init(allocator, header.num_vars);
    errdefer formula.deinit();
    try formula.clauses.ends.ensureTotalCapacity(
        allocator,
        @min(header.num_clauses, max_reserved_clauses),
    );

    var current: std.ArrayList(Literal) = .empty;
    defer current.deinit(allocator);
    var parsed_clauses: u64 = 0;

    while (try peekTokenStart(reader)) |first| {
        if (first == 'p') return error.DuplicateHeader;
        if (try takeLiteral(reader, header.num_vars)) |lit| {
            try current.append(allocator, lit);
        } else {
            try formula.addClause(current.items);
            current.clearRetainingCapacity();
            parsed_clauses += 1;
        }
    }
    if (current.items.len > 0) return error.UnterminatedClause;
    if (!clauseCountMatches(header.num_clauses, parsed_clauses)) return error.ClauseCountMismatch;
    return formula;
}

fn parseHeader(reader: *std.Io.Reader) ParseError!Header {
    const first = try peekTokenStart(reader) orelse return error.MissingHeader;
    if (first != 'p') return error.MissingHeader;
    const maybe_line = reader.takeDelimiter('\n') catch |err| switch (err) {
        error.ReadFailed => return error.ReadFailed,
        error.StreamTooLong => return error.InvalidHeader,
    };
    const line = maybe_line orelse return error.InvalidHeader;

    var it = std.mem.tokenizeAny(u8, line, " \t\r");
    const p_tok = it.next() orelse return error.InvalidHeader;
    if (!std.mem.eql(u8, p_tok, "p")) return error.InvalidHeader;
    const fmt_tok = it.next() orelse return error.InvalidHeader;
    if (!std.mem.eql(u8, fmt_tok, "cnf")) return error.InvalidHeader;
    const nv_tok = it.next() orelse return error.InvalidHeader;
    const nc_tok = it.next() orelse return error.InvalidHeader;
    if (it.next() != null) return error.InvalidHeader;

    const num_vars = std.fmt.parseInt(u32, nv_tok, 10) catch return error.InvalidHeader;
    if (num_vars > cnf.max_vars) return error.FormulaTooLarge;
    return .{
        .num_vars = num_vars,
        .num_clauses = std.fmt.parseInt(u32, nc_tok, 10) catch return error.InvalidHeader,
    };
}

// A large mismatch against the `p cnf N M` header is almost always a
// malformed file (missing `0` terminators joining clauses together, as in
// SATLIB's dubois100.cnf). 5% slack tolerates off-by-one headers.
const clause_count_slack_divisor: u64 = 20;

fn clauseCountMatches(declared: u32, parsed: u64) bool {
    if (declared == 0) return true;
    const delta = if (parsed >= declared) parsed - declared else declared - parsed;
    const slack = (declared + clause_count_slack_divisor - 1) / clause_count_slack_divisor;
    return delta <= slack;
}

fn isSpace(b: u8) bool {
    return b == ' ' or b == '\t' or b == '\r' or b == '\n';
}

// Skips whitespace and `c` comment lines and returns the first byte of
// the next token without consuming it. Returns null at end of input or
// at a SATLIB `%` end-of-content marker (anything after it is ignored).
fn peekTokenStart(reader: *std.Io.Reader) ParseError!?u8 {
    while (true) {
        const b = (peekByteOrNull(reader) catch return error.ReadFailed) orelse return null;
        if (isSpace(b)) {
            reader.toss(1);
        } else if (b == 'c') {
            _ = reader.discardDelimiterInclusive('\n') catch |err| switch (err) {
                error.EndOfStream => return null,
                error.ReadFailed => return error.ReadFailed,
            };
        } else if (b == '%') {
            return null;
        } else {
            return b;
        }
    }
}

// Consumes one integer token. Returns null for the `0` clause terminator;
// `-0` is no literal, so it is an invalid token, not a terminator.
fn takeLiteral(reader: *std.Io.Reader, num_vars: u32) ParseError!?Literal {
    const negative = (peekByteOrNull(reader) catch return error.ReadFailed) == '-';
    if (negative) reader.toss(1);

    var magnitude: u64 = 0;
    var digits: usize = 0;
    while (peekByteOrNull(reader) catch return error.ReadFailed) |b| {
        if (isSpace(b)) break;
        if (b < '0' or b > '9') return error.InvalidToken;
        magnitude = magnitude * 10 + (b - '0');
        if (magnitude > num_vars) return error.VariableOutOfRange;
        digits += 1;
        reader.toss(1);
    }
    if (digits == 0) return error.InvalidToken;
    if (magnitude == 0) return if (negative) error.InvalidToken else null;
    return Literal.init(.fromIndex(magnitude - 1), negative);
}

fn peekByteOrNull(reader: *std.Io.Reader) error{ReadFailed}!?u8 {
    return reader.peekByte() catch |err| switch (err) {
        error.EndOfStream => null,
        error.ReadFailed => error.ReadFailed,
    };
}

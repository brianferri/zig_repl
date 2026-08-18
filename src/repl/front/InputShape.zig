const std = @import("std");
const assert = std.debug.assert;

pub const Shape = enum { expression, declaration };

pub const Wrapped = struct {
    text: [:0]u8,
    shape: Shape,
    /// Byte offset in `text` where the original user input begins.
    /// For `.expression` shape, equals `expression_prefix.len`.
    /// For `.declaration` shape, zero.
    user_offset: u32,
    /// Byte length of the original user input region inside `text`.
    user_len: u32,

    pub fn deinit(wrapped: *Wrapped, gpa: std.mem.Allocator) void {
        gpa.free(wrapped.text);
        wrapped.* = undefined;
    }

    /// Slice of `text` corresponding to what the user actually typed.
    /// Diagnostic renderers anchor line/column math against this so
    /// the wrap is invisible to the user.
    pub fn userText(wrapped: *const Wrapped) []const u8 {
        assert(wrapped.user_offset + wrapped.user_len <= wrapped.text.len);
        return wrapped.text[wrapped.user_offset..][0..wrapped.user_len];
    }
};

/// Names the expression wrap exposes. Sema imports these so it can find the produced function and its
/// result local in the analysed Zir without re-stating the names independently -- a typo in one place
/// would otherwise silently desynchronise the producer from the consumer.
///
/// The wrap is a runtime function body rather than a container `const`: a container const initializer
/// is a comptime scope in AstGen, which elides the `block_comptime` markers around comptime-required
/// operands (`@Int` bit width, array length, ...). A function body is a runtime scope, so those markers
/// are emitted, and the expression evaluates with the same comptime/runtime boundary as real code.
pub const expression_decl_name: []const u8 = "__repl_input";
pub const expression_value_name: []const u8 = "__repl_value";

const expression_prefix: []const u8 = "fn " ++ expression_decl_name ++ "() void {\n    const " ++ expression_value_name ++ " = (";
const expression_suffix: []const u8 = ");\n    _ = " ++ expression_value_name ++ ";\n}\n";

pub const max_input_bytes: u32 = 16 * 1024;

/// Max bracket-nesting depth accepted. Parser, AstGen, and the Sema eval over
/// the same bodies each recurse per nesting level -- several call frames per
/// level for the heaviest construct (a labeled block). Past this the call stack
/// overflows mid-parse (a hard trap on wasm, whose ceiling the stack size
/// cannot raise) before any diagnostic runs, so the front end rejects it.
/// Sized well under the observed wasm trap point with margin for browser
/// engines; still ample for real code.
pub const max_nesting_depth: u32 = 32;

/// Classifies an input line by its first non-trivia token using
/// std.zig.Tokenizer, so the grammar's own list of declaration-introducing
/// keywords stays the source of truth.
///
/// `keyword_fn` is overloaded: `fn name(...) ...` is a declaration,
/// but `fn (...) R` (no name, parens immediately after) is an
/// anonymous fn TYPE expression. Two-token lookahead disambiguates --
/// an l_paren right after `fn` means expression; an identifier means
/// declaration.
fn classify(input: [:0]const u8) Shape {
    assert(input.len > 0);
    assert(input.len <= max_input_bytes);

    var tokenizer = std.zig.Tokenizer.init(input);
    const first = tokenizer.next();
    return switch (first.tag) {
        .keyword_fn => switch (tokenizer.next().tag) {
            .l_paren => .expression,
            else => .declaration,
        },
        .keyword_const,
        .keyword_var,
        .keyword_pub,
        .keyword_comptime,
        .keyword_test,
        .keyword_extern,
        .keyword_inline,
        .keyword_noinline,
        .keyword_export,
        .keyword_threadlocal,
        => .declaration,
        else => .expression,
    };
}

pub const Split = struct {
    decls: []const u8,
    expr: []const u8,
};

/// When `input` is a run of declarations followed by a single trailing
/// expression (`const x = 1; x + 1`), return it split into the
/// declaration prefix and the trailing expression. The REPL runs them
/// as two passes -- the decls persist to the session, then the
/// expression is evaluated with them in scope -- so each pass keeps a
/// single contiguous user region and the existing wrap and diagnostic
/// mapping apply unchanged.
///
/// "Declarations then one trailing expression" is the only shape with a
/// split: at container scope Zig accepts declarations and rejects a bare
/// expression except in trailing (result) position, so an expression can
/// legally appear only last. Newlines are whitespace to the tokenizer,
/// so a Shift-Enter multi-line buffer is handled by the same `;` scan.
///
/// Returns null when a single wrap already suffices -- a lone expression
/// or pure declarations -- and for inputs with no trailing expression
/// (the tail is itself a declaration); those fall through to
/// `wrapWithInjection`. The returned slices borrow from `input`.
pub fn splitTrailingExpr(gpa: std.mem.Allocator, input: []const u8) std.mem.Allocator.Error!?Split {
    assert(input.len > 0);
    assert(input.len <= max_input_bytes);

    const sentinel = try gpa.allocSentinel(u8, input.len, 0);
    defer gpa.free(sentinel);
    @memcpy(sentinel, input);

    // Byte just past the last top-level `;` -- the boundary between the
    // declaration prefix and a trailing statement. Depth tracks
    // bracketing so a `;` inside a `struct {...}` body (or any nested
    // braces/parens/brackets) is not read as a statement separator;
    // literals and comments are single (or skipped) tokens, so their
    // contents never reach the scan.
    var tokenizer = std.zig.Tokenizer.init(sentinel);
    var depth: u32 = 0;
    var boundary: ?usize = null;
    while (true) {
        const token = tokenizer.next();
        switch (token.tag) {
            .eof => break,
            .l_brace, .l_paren, .l_bracket => depth += 1,
            .r_brace, .r_paren, .r_bracket => if (depth > 0) {
                depth -= 1;
            },
            .semicolon => if (depth == 0) {
                boundary = token.loc.end;
            },
            else => {},
        }
    }

    const split_at = boundary orelse return null; // a single statement
    // `sentinel[split_at..]` keeps the trailing sentinel, so `classify`
    // can read its first token. An empty tail means the input ended in
    // `;` (pure declarations); a declaration tail means no trailing
    // expression. Either way there is nothing to evaluate separately.
    const tail = sentinel[split_at..];
    if (std.mem.trim(u8, tail, " \t\r\n").len == 0) return null;
    if (classify(tail) == .declaration) return null;

    const decls = std.mem.trim(u8, input[0..split_at], " \t\r\n");
    const expr = std.mem.trim(u8, input[split_at..], " \t\r\n");
    if (decls.len == 0) return null;
    return .{ .decls = decls, .expr = expr };
}

pub fn wrap(gpa: std.mem.Allocator, input: []const u8) std.mem.Allocator.Error!Wrapped {
    return wrapWithInjection(gpa, "", input);
}

/// Like `wrap`, but prepends `injection_prefix` to the produced
/// text. The prefix is emitted verbatim at file scope so AstGen
/// sees the named decls in scope -- the REPL uses this to project
/// session-namespace bindings into every input's scope via
/// `const <name>: <type> = undefined;` lines. `user_offset` shifts
/// past the prefix so diagnostics still land in the user's frame.
pub fn wrapWithInjection(
    gpa: std.mem.Allocator,
    injection_prefix: []const u8,
    input: []const u8,
) std.mem.Allocator.Error!Wrapped {
    assert(input.len > 0);
    assert(input.len <= max_input_bytes);

    const sentinel_input = try gpa.allocSentinel(u8, input.len, 0);
    defer gpa.free(sentinel_input);
    @memcpy(sentinel_input, input);
    const shape = classify(sentinel_input);

    return switch (shape) {
        .declaration => .{
            .text = try wrapDeclaration(gpa, injection_prefix, input),
            .shape = shape,
            .user_offset = @intCast(injection_prefix.len),
            .user_len = @intCast(input.len),
        },
        .expression => .{
            .text = try wrapExpression(gpa, injection_prefix, input),
            .shape = shape,
            .user_offset = @intCast(injection_prefix.len + expression_prefix.len),
            .user_len = @intCast(input.len),
        },
    };
}

fn wrapExpression(
    gpa: std.mem.Allocator,
    injection_prefix: []const u8,
    input: []const u8,
) std.mem.Allocator.Error![:0]u8 {
    return std.fmt.allocPrintSentinel(
        gpa,
        "{s}{s}{s}{s}",
        .{ injection_prefix, expression_prefix, input, expression_suffix },
        0,
    );
}

fn wrapDeclaration(
    gpa: std.mem.Allocator,
    injection_prefix: []const u8,
    input: []const u8,
) std.mem.Allocator.Error![:0]u8 {
    return std.fmt.allocPrintSentinel(
        gpa,
        "{s}{s}",
        .{ injection_prefix, input },
        0,
    );
}

test "splitTrailingExpr: declarations then a trailing expression" {
    const split = (try splitTrailingExpr(std.testing.allocator, "const x = 1; x + 1")).?;
    try std.testing.expectEqualStrings("const x = 1;", split.decls);
    try std.testing.expectEqualStrings("x + 1", split.expr);
}

test "splitTrailingExpr: multiple declarations precede the expression" {
    const split = (try splitTrailingExpr(std.testing.allocator, "const a = 1; const b = 2; a + b")).?;
    try std.testing.expectEqualStrings("const a = 1; const b = 2;", split.decls);
    try std.testing.expectEqualStrings("a + b", split.expr);
}

test "splitTrailingExpr: a `;` nested in a container body is not a split point" {
    const split = (try splitTrailingExpr(std.testing.allocator, "const S = struct { const k = 1; }; S.k")).?;
    try std.testing.expectEqualStrings("const S = struct { const k = 1; };", split.decls);
    try std.testing.expectEqualStrings("S.k", split.expr);
}

test "splitTrailingExpr: shapes a single wrap handles return null" {
    const gpa = std.testing.allocator;
    try std.testing.expect(try splitTrailingExpr(gpa, "const x = 1;") == null); // pure declaration
    try std.testing.expect(try splitTrailingExpr(gpa, "1 + 2") == null); // pure expression
    try std.testing.expect(try splitTrailingExpr(gpa, "const a = 1; const b = 2;") == null); // trailing decl
}

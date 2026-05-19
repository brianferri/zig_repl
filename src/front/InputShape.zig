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

/// Decl name the expression wrap exposes. Sema imports this so it
/// can find the produced decl in the analysed Zir without
/// re-stating the name independently -- a typo in one place would
/// otherwise silently desynchronise the producer from the consumer.
pub const expression_decl_name: []const u8 = "__repl_input";

const expression_prefix: []const u8 = "const " ++ expression_decl_name ++ " = (";
const expression_suffix: []const u8 = ");\n";

pub const max_input_bytes: u32 = 16 * 1024;

/// Classifies an input line by its first non-trivia token using
/// std.zig.Tokenizer, so the grammar's own list of declaration-introducing
/// keywords stays the source of truth.
pub fn classify(input: [:0]const u8) Shape {
    assert(input.len > 0);
    assert(input.len <= max_input_bytes);

    var tokenizer = std.zig.Tokenizer.init(input);
    const first = tokenizer.next();
    return switch (first.tag) {
        .keyword_fn,
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

pub fn wrap(gpa: std.mem.Allocator, input: []const u8) std.mem.Allocator.Error!Wrapped {
    assert(input.len > 0);
    assert(input.len <= max_input_bytes);

    const sentinel_input = try gpa.dupeZ(u8, input);
    const shape = classify(sentinel_input);
    if (shape == .declaration) return .{
        .text = sentinel_input,
        .shape = shape,
        .user_offset = 0,
        .user_len = @intCast(input.len),
    };
    defer gpa.free(sentinel_input);
    return .{
        .text = try wrapExpression(gpa, input),
        .shape = shape,
        .user_offset = @intCast(expression_prefix.len),
        .user_len = @intCast(input.len),
    };
}

fn wrapExpression(gpa: std.mem.Allocator, input: []const u8) std.mem.Allocator.Error![:0]u8 {
    assert(input.len > 0);
    assert(input.len <= max_input_bytes);

    return std.fmt.allocPrintSentinel(
        gpa,
        "{s}{s}{s}",
        .{ expression_prefix, input, expression_suffix },
        0,
    );
}

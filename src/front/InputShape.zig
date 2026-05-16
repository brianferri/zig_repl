const std = @import("std");
const assert = std.debug.assert;

pub const Shape = enum { expression, declaration };

pub const Wrapped = struct {
    text: [:0]u8,
    shape: Shape,

    pub fn deinit(wrapped: *Wrapped, gpa: std.mem.Allocator) void {
        gpa.free(wrapped.text);
        wrapped.* = undefined;
    }
};

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
    if (shape == .declaration) {
        return .{ .text = sentinel_input, .shape = shape };
    }
    defer gpa.free(sentinel_input);
    return .{ .text = try wrapExpression(gpa, input), .shape = shape };
}

fn wrapExpression(gpa: std.mem.Allocator, input: []const u8) std.mem.Allocator.Error![:0]u8 {
    assert(input.len > 0);
    assert(input.len <= max_input_bytes);

    return std.fmt.allocPrintSentinel(
        gpa,
        "const __repl_input = ({s});\n",
        .{input},
        0,
    );
}

const std = @import("std");
const assert = std.debug.assert;

const InputShape = @import("InputShape.zig");
const ZirErrors = @import("ZirErrors.zig");
const InternPool = @import("../sema/InternPool.zig");

pub const Result = struct {
    wrapped: InputShape.Wrapped,
    tree: std.zig.Ast,
    zir: std.zig.Zir,

    pub fn deinit(result: *Result, gpa: std.mem.Allocator) void {
        result.zir.deinit(gpa);
        result.tree.deinit(gpa);
        result.wrapped.deinit(gpa);
        result.* = undefined;
    }

    /// Hand the analysed `zir` to the caller and free the rest. Consumes the result.
    pub fn takeZir(result: *Result, gpa: std.mem.Allocator) std.zig.Zir {
        const zir = result.zir;
        result.tree.deinit(gpa);
        result.wrapped.deinit(gpa);
        result.* = undefined;
        return zir;
    }

    pub fn hasParseErrors(result: *const Result) bool {
        return result.tree.errors.len != 0;
    }

    pub fn hasZirErrors(result: *const Result) bool {
        if (!result.zir.hasCompileErrors()) return false;
        return ZirErrors.countActionable(result.zir, result.tree) > 0;
    }

    pub fn source(result: *const Result) [:0]const u8 {
        return result.wrapped.text;
    }

    /// View of the user-visible coordinate space inside `source()`, past the wrap prefix/suffix.
    pub fn userView(result: *const Result) UserView {
        return .{
            .text = result.wrapped.userText(),
            .offset_in_source = result.wrapped.user_offset,
        };
    }
};

/// Translates wrapped-source positions back into the user's frame, keeping all wrap-shape knowledge here.
pub const UserView = struct {
    text: []const u8,
    offset_in_source: u32,

    /// Null when the span anchors entirely in the wrap-injection prefix; a span straddling the boundary
    /// clips to `[0, user_len]`.
    pub fn translate(view: UserView, wrapped: std.zig.Ast.Span) ?std.zig.Ast.Span {
        if (anchorsInInjection(view, wrapped)) return null;
        const len: u32 = @intCast(view.text.len);
        return .{
            .start = mapPos(wrapped.start, view.offset_in_source, len),
            .main = mapPos(wrapped.main, view.offset_in_source, len),
            .end = mapPos(wrapped.end, view.offset_in_source, len),
        };
    }

    pub fn findLoc(view: UserView, user_byte_offset: u32) std.zig.Loc {
        return std.zig.findLineColumn(view.text, user_byte_offset);
    }

    fn anchorsInInjection(view: UserView, span: std.zig.Ast.Span) bool {
        return span.end <= view.offset_in_source;
    }

    fn mapPos(wrapped_pos: u32, user_offset: u32, user_len: u32) u32 {
        if (wrapped_pos < user_offset) return 0;
        const rel = wrapped_pos - user_offset;
        return @min(rel, user_len);
    }
};

pub fn run(gpa: std.mem.Allocator, input: []const u8) !Result {
    return runWithInjection(gpa, input, null, .none);
}

/// Like `run`, but builds an injection prefix from `namespace`'s decls so AstGen's scope chain resolves
/// session bindings (including rebind rejection).
pub fn runWithInjection(
    gpa: std.mem.Allocator,
    input: []const u8,
    pool: ?*const InternPool,
    namespace: InternPool.OptionalNamespaceIndex,
) !Result {
    assert(input.len > 0);
    assert(input.len <= InputShape.max_input_bytes);

    const injection_prefix = try buildInjectionPrefix(gpa, pool, namespace);
    defer gpa.free(injection_prefix);

    var wrapped = try InputShape.wrapWithInjection(gpa, injection_prefix, input);
    errdefer wrapped.deinit(gpa);

    // Reject pathologically nested input before the recursive parse overflows the stack -- a parse-level
    // rejection routes through the existing diagnostic paths.
    if (exceedsNestingDepth(wrapped.text)) return error.ParseError;

    var tree = try std.zig.Ast.parse(gpa, wrapped.text, .{ .mode = .zig });
    errdefer tree.deinit(gpa);

    var zir = try std.zig.AstGen.generate(gpa, tree);
    errdefer zir.deinit(gpa);

    return .{ .wrapped = wrapped, .tree = tree, .zir = zir };
}

/// Whether `source`'s bracket nesting exceeds `InputShape.max_nesting_depth`. Tokenizing keeps
/// brackets inside strings and comments from counting.
fn exceedsNestingDepth(source: [:0]const u8) bool {
    var tokenizer = std.zig.Tokenizer.init(source);
    var depth: u32 = 0;
    while (true) {
        switch (tokenizer.next().tag) {
            .eof => return false,
            .l_paren, .l_brace, .l_bracket => {
                depth += 1;
                if (depth > InputShape.max_nesting_depth) return true;
            },
            .r_paren, .r_brace, .r_bracket => depth -|= 1,
            else => {},
        }
    }
}

/// Renders `const <name> = undefined;` per session-bound decl. The `= undefined` only adds the name to
/// AstGen's scope chain; `Sema.evalDeclVal` substitutes the real value at lookup.
fn buildInjectionPrefix(
    gpa: std.mem.Allocator,
    pool: ?*const InternPool,
    namespace: InternPool.OptionalNamespaceIndex,
) ![]u8 {
    const p = pool orelse return gpa.alloc(u8, 0);
    const ns_idx = namespace.unwrap() orelse return gpa.alloc(u8, 0);
    const ns = p.namespaces.items[@backingInt(ns_idx)];
    if (ns.pub_decls.count() == 0 and ns.priv_decls.count() == 0) {
        return gpa.alloc(u8, 0);
    }

    var alloc_writer: std.Io.Writer.Allocating = .init(gpa);
    defer alloc_writer.deinit();
    const writer = &alloc_writer.writer;

    for (ns.pub_decls.keys()) |nav_idx| try appendDeclLine(p, nav_idx, writer);
    for (ns.priv_decls.keys()) |nav_idx| try appendDeclLine(p, nav_idx, writer);

    return alloc_writer.toOwnedSlice();
}

fn appendDeclLine(
    pool: *const InternPool,
    nav_idx: InternPool.Nav.Index,
    writer: *std.Io.Writer,
) !void {
    const nav = pool.getNav(nav_idx);
    _ = nav.resolved orelse return; // test / comptime / unresolved extern
    const name = pool.stringSlice(nav.name);
    try writer.print("const {s} = undefined;\n", .{name});
}

test "UserView.translate: span entirely in user frame translates to user-relative" {
    const view: UserView = .{ .text = "1 + 2", .offset_in_source = 22 };
    // Wrapped position 24..27 = "+ 2" inside user input.
    const translated = view.translate(.{ .start = 24, .main = 24, .end = 27 }).?;
    try std.testing.expectEqual(@as(u32, 2), translated.start);
    try std.testing.expectEqual(@as(u32, 2), translated.main);
    try std.testing.expectEqual(@as(u32, 5), translated.end);
}

test "UserView.translate: span entirely in injection prefix returns null" {
    const view: UserView = .{ .text = "1 + 2", .offset_in_source = 22 };
    // Wrapped position 5..10 is entirely before user_offset=22.
    try std.testing.expect(view.translate(.{ .start = 5, .main = 7, .end = 10 }) == null);
}

test "UserView.translate: span straddling injection boundary clips to user range" {
    const view: UserView = .{ .text = "1 + 2", .offset_in_source = 22 };
    // Wrapped position 20..25 straddles user_offset=22; clips start to 0.
    const translated = view.translate(.{ .start = 20, .main = 22, .end = 25 }).?;
    try std.testing.expectEqual(@as(u32, 0), translated.start);
    try std.testing.expectEqual(@as(u32, 0), translated.main);
    try std.testing.expectEqual(@as(u32, 3), translated.end);
}

test "UserView.translate: span entirely in suffix clamps to user_len" {
    const view: UserView = .{ .text = "1 + 2", .offset_in_source = 22 };
    // Wrapped 30..33 is past user_end=27. span.end > user_offset, so it's
    // not "anchored in injection"; clipping caps every coord at user_len=5.
    const translated = view.translate(.{ .start = 30, .main = 31, .end = 33 }).?;
    try std.testing.expectEqual(@as(u32, 5), translated.start);
    try std.testing.expectEqual(@as(u32, 5), translated.main);
    try std.testing.expectEqual(@as(u32, 5), translated.end);
}

test "UserView.translate: boundary case (span.end == user_offset) is injection" {
    const view: UserView = .{ .text = "x", .offset_in_source = 22 };
    // A span ending exactly at user_offset is "all before user input" --
    // anchoring on the byte BEFORE user input is still injection-side.
    try std.testing.expect(view.translate(.{ .start = 0, .main = 10, .end = 22 }) == null);
}

test "UserView.findLoc: byte offset maps to user-frame line/column" {
    const view: UserView = .{ .text = "first\nsecond\nthird", .offset_in_source = 0 };

    const at_first = view.findLoc(0);
    try std.testing.expectEqual(@as(usize, 0), at_first.line);
    try std.testing.expectEqual(@as(usize, 0), at_first.column);

    const at_second = view.findLoc(8); // "first\nse|cond..."
    try std.testing.expectEqual(@as(usize, 1), at_second.line);
    try std.testing.expectEqual(@as(usize, 2), at_second.column);
}

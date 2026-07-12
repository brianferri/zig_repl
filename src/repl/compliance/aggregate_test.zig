const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

// Non-power-of-two widths reach the int_type handler rather than a well-known Inst.Ref.
const awkward = .{ 1, 3, 7, 33, 69, 420 };

fn U(comptime bits: u16) type {
    return @Int(.unsigned, bits);
}

test "compliance: array literals, indexing, and rendering" {
    try compliance.check(a, .{
        .{
            .src = &.{ "const a = [_]i32{1, 2, 3};", "a[1]" },
            .want = blk: {
                const arr = [_]i32{ 1, 2, 3 };
                break :blk arr[1];
            },
        },
        .{
            .src = &.{ "const a = [_]u32{7, 7, 7};", "a[2]" },
            .want = blk: {
                const arr = [_]u32{ 7, 7, 7 };
                break :blk arr[2];
            },
        },
        .{ .src = &.{"[_]i32{1, 2, 3}"}, .want = [_]i32{ 1, 2, 3 } },
        .{ .src = &.{"[3]i32"}, .want = [3]i32 },
    });
}

test "compliance: tuple literals, indexing, and rendering" {
    try compliance.check(a, .{
        .{ .src = &.{".{1, 2, 3}"}, .want = .{ 1, 2, 3 } },
        .{ .src = &.{".{1, 2.5, 3}"}, .want = .{ 1, 2.5, 3 } },
        .{ .src = &.{".{1, 2.5}[1]"}, .want = .{ 1, 2.5 }[1] },
        .{
            .src = &.{ "const t = .{ 1, 2.5, 3 };", "t[0]" },
            .want = blk: {
                const t = .{ 1, 2.5, 3 };
                break :blk t[0];
            },
        },
    });
}

test "compliance: array index across awkward integer widths" {
    inline for (awkward) |bits| {
        try compliance.check(a, .{
            .{
                .src = &.{ std.fmt.comptimePrint("const a = [_]u{d}{{1, 0, 1}};", .{bits}), "a[0]" },
                .want = @as(U(bits), 1),
            },
        });
    }
}

test "compliance: array type renders across awkward integer widths" {
    inline for (awkward) |bits| {
        try compliance.check(a, .{
            .{
                .src = &.{std.fmt.comptimePrint("[3]u{d}", .{bits})},
                .want = [3]U(bits),
            },
        });
    }
}

test "compliance: wide-width values round-trip (u69 large, i420 negative)" {
    try compliance.check(a, .{
        .{
            .src = &.{ "const a = [_]u69{100, 200, 300};", "a[2]" },
            .want = blk: {
                const arr = [_]u69{ 100, 200, 300 };
                break :blk arr[2];
            },
        },
        .{
            .src = &.{ "const a = [_]i420{-123456789, 0, 1};", "a[0]" },
            .want = blk: {
                const arr = [_]i420{ -123456789, 0, 1 };
                break :blk arr[0];
            },
        },
    });
}

test "compliance: vector, pointer-to-aggregate, and optional types render" {
    try compliance.check(a, .{
        .{ .src = &.{"@Vector(4, i32)"}, .want = @Vector(4, i32) },
        .{ .src = &.{"@Vector(2, f32)"}, .want = @Vector(2, f32) },
        .{ .src = &.{"@Vector(8, bool)"}, .want = @Vector(8, bool) },
        .{ .src = &.{"@Vector(3, *const u8)"}, .want = @Vector(3, *const u8) },
        .{ .src = &.{"*@Vector(4, i32)"}, .want = *@Vector(4, i32) },
        .{ .src = &.{"*[3]i32"}, .want = *[3]i32 },
        .{ .src = &.{"?i32"}, .want = ?i32 },
        .{ .src = &.{"?*const u8"}, .want = ?*const u8 },
        .{ .src = &.{"?@Vector(4, i32)"}, .want = ?@Vector(4, i32) },
    });
}

test "compliance: vector type renders across awkward element widths" {
    inline for (awkward) |bits| {
        try compliance.check(a, .{
            .{
                .src = &.{std.fmt.comptimePrint("@Vector(7, u{d})", .{bits})},
                .want = @Vector(7, U(bits)),
            },
        });
    }
}

test "compliance: void and explicit tuple types" {
    try compliance.check(a, .{
        .{ .src = &.{"{}"}, .want = {} },
        .{ .src = &.{".{ 1, {} }"}, .want = .{ 1, {} } },
        .{ .src = &.{"@as(i32, {})"}, .reject = {} },
        .{ .src = &.{"@as(void, 5)"}, .reject = {} },
        .{
            .src = &.{ "const T = struct { i32, f128 };", "T" },
            .want = blk: {
                const T = struct { i32, f128 };
                break :blk T;
            },
        },
        .{ .src = &.{"struct { i32, void }"}, .want = struct { i32, void } },
        .{
            .src = &.{ "const x: struct { i32, f128, void } = .{ 420, 2.5, {} };", "x" },
            .want = blk: {
                const x: struct { i32, f128, void } = .{ 420, 2.5, {} };
                break :blk x;
            },
        },
        .{ .src = &.{"const x: struct { i32 } = .{ {} };"}, .reject = {} },
        .{ .src = &.{"const x: struct { void } = .{ 420 };"}, .reject = {} },
        .{ .src = &.{"const x: struct { i32, f128 } = .{ 1 };"}, .reject = {} },
        .{ .src = &.{"const x: struct { i32 } = .{ 1, 2 };"}, .reject = {} },
    });
}

test "compliance: prior decl used as a tuple element" {
    try compliance.check(a, .{
        .{ .src = &.{ "const x = 7;", ".{ x, 2.5 }" }, .want = .{ 7, 2.5 } },
        .{ .src = &.{ "const y = 9;", "const t = .{ y, 2.5 };", "t[0]" }, .want = blk: {
            const y = 9;
            const t = .{ y, 2.5 };
            break :blk t[0];
        } },
    });
}

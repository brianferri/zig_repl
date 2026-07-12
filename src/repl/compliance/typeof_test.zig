const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @TypeOf reports the resolved type" {
    try compliance.check(a, .{
        .{ .src = &.{"@TypeOf(@as(u32, 1))"}, .want = @TypeOf(@as(u32, 1)) },
        .{ .src = &.{"@TypeOf(true)"}, .want = @TypeOf(true) },
        .{ .src = &.{"@TypeOf(1)"}, .want = @TypeOf(1) },
        .{ .src = &.{"@TypeOf(@as(i32, -5))"}, .want = @TypeOf(@as(i32, -5)) },
        .{ .src = &.{"@TypeOf(1 + 2)"}, .want = @TypeOf(1 + 2) },
        .{ .src = &.{"@TypeOf(@as(u8, 1) + @as(u16, 2))"}, .want = @TypeOf(@as(u8, 1) + @as(u16, 2)) },
        .{ .src = &.{"@TypeOf(1.5)"}, .want = @TypeOf(1.5) },
        .{ .src = &.{"@TypeOf(@as(f32, 1.5))"}, .want = @TypeOf(@as(f32, 1.5)) },
        .{ .src = &.{"@TypeOf(true and false)"}, .want = @TypeOf(true and false) },
        .{ .src = &.{"@TypeOf(if (true) @as(u32, 1) else @as(u32, 0))"}, .want = @TypeOf(if (true) @as(u32, 1) else @as(u32, 0)) },
        .{ .src = &.{"@TypeOf({})"}, .want = @TypeOf({}) },
        .{ .src = &.{"@TypeOf(switch (1) { 0 => @as(u8, 10), else => @as(u8, 20) })"}, .want = @TypeOf(switch (1) {
            0 => @as(u8, 10),
            else => @as(u8, 20),
        }) },
        .{
            .src = &.{ "fn foo() void {}", "@TypeOf(foo)" },
            .want = fn () void,
        },
        .{
            .src = &.{ "fn add(a2: u32, b: u32) u32 { return a2 + b; }", "@TypeOf(add)" },
            .want = fn (u32, u32) u32,
        },
        .{
            .src = &.{ "const E = error{Bad, Worse};", "@TypeOf(@as(E!u32, 0))" },
            .want = blk: {
                const E = error{ Bad, Worse };
                break :blk @TypeOf(@as(E!u32, 0));
            },
        },
    });
}

test "compliance: type and bool equality compare by identity" {
    try compliance.check(a, .{
        .{ .src = &.{"u8 == u8"}, .want = u8 == u8 },
        .{ .src = &.{"u8 == u16"}, .want = u8 == u16 },
        .{ .src = &.{"u8 != u16"}, .want = u8 != u16 },
        .{
            .src = &.{"blk: { const x: u8 = 1; const y: u8 = 2; break :blk @TypeOf(x) == @TypeOf(y); }"},
            .want = blk: {
                const x: u8 = 1;
                const y: u8 = 2;
                break :blk @TypeOf(x) == @TypeOf(y);
            },
        },
        .{
            .src = &.{"blk: { const x: u8 = 1; const y: u16 = 2; break :blk @TypeOf(x) == @TypeOf(y); }"},
            .want = blk: {
                const x: u8 = 1;
                const y: u16 = 2;
                break :blk @TypeOf(x) == @TypeOf(y);
            },
        },
        .{ .src = &.{"true == false"}, .want = true == false },
        .{
            .src = &.{"blk: { const b = true; break :blk b != false; }"},
            .want = blk: {
                const b = true;
                break :blk b != false;
            },
        },
        .{ .src = &.{"blk: { break :blk u8 < u16; }"}, .reject = {} },
    });
}

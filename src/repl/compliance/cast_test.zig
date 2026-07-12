const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: overflow-arithmetic builtins return .{ wrapped, overflow }" {
    try compliance.check(a, .{
        .{
            .src = &.{"@addWithOverflow(@as(u8, 200), @as(u8, 100))[0]"},
            .want = @addWithOverflow(@as(u8, 200), @as(u8, 100))[0],
        },
        .{
            .src = &.{"@addWithOverflow(@as(u8, 200), @as(u8, 100))[1]"},
            .want = @addWithOverflow(@as(u8, 200), @as(u8, 100))[1],
        },
        .{
            .src = &.{"@addWithOverflow(@as(u8, 5), @as(u8, 3))[1]"},
            .want = @addWithOverflow(@as(u8, 5), @as(u8, 3))[1],
        },
        .{
            .src = &.{"@subWithOverflow(@as(u8, 5), @as(u8, 10))[0]"},
            .want = @subWithOverflow(@as(u8, 5), @as(u8, 10))[0],
        },
        .{
            .src = &.{"@mulWithOverflow(@as(u8, 20), @as(u8, 20))[0]"},
            .want = @mulWithOverflow(@as(u8, 20), @as(u8, 20))[0],
        },
        .{
            .src = &.{"@mulWithOverflow(@as(u8, 20), @as(u8, 20))[1]"},
            .want = @mulWithOverflow(@as(u8, 20), @as(u8, 20))[1],
        },
        .{
            .src = &.{"@shlWithOverflow(@as(u8, 64), 2)[0]"},
            .want = @shlWithOverflow(@as(u8, 64), 2)[0],
        },
        .{
            .src = &.{"@shlWithOverflow(@as(u8, 64), 2)[1]"},
            .want = @shlWithOverflow(@as(u8, 64), 2)[1],
        },
        .{
            .src = &.{"@addWithOverflow(@as(@Vector(2, u8), .{ 200, 5 }), @as(@Vector(2, u8), .{ 100, 3 }))[0]"},
            .want = @addWithOverflow(@as(@Vector(2, u8), .{ 200, 5 }), @as(@Vector(2, u8), .{ 100, 3 }))[0],
        },
        .{
            .src = &.{"@addWithOverflow(@as(u8, 0), @as(u8, 7))[0]"},
            .want = @addWithOverflow(@as(u8, 0), @as(u8, 7))[0],
        },
    });
}

test "compliance: int/float casts and coercions" {
    try compliance.check(a, .{
        .{ .src = &.{"@as(u32, @intCast(@as(u8, 200)))"}, .want = @as(u32, @intCast(@as(u8, 200))) },
        .{ .src = &.{"@as(u8, @truncate(@as(u32, 0x1234)))"}, .want = @as(u8, @truncate(@as(u32, 0x1234))) },
        .{ .src = &.{"@as(u32, @bitCast(@as(f32, 1.5)))"}, .want = @as(u32, @bitCast(@as(f32, 1.5))) },
        .{ .src = &.{"@as(u8, @bitCast(@as(i8, -1)))"}, .want = @as(u8, @bitCast(@as(i8, -1))) },
        .{ .src = &.{"@as(usize, 100) + 1"}, .want = @as(usize, 100) + 1 },
        .{ .src = &.{"@as(c_int, 5) * 2"}, .want = @as(c_int, 5) * 2 },
        .{ .src = &.{"@as(u16, 1000) > @as(u8, 200)"}, .want = @as(u16, 1000) > @as(u8, 200) },
        .{ .src = &.{"@as(f32, 1.5)"}, .want = @as(f32, 1.5) },
        .{ .src = &.{"@as(f64, @as(i32, 1000000))"}, .want = @as(f64, @as(i32, 1000000)) },
    });
}

test "compliance: @intFromFloat and @floatFromInt" {
    try compliance.check(a, .{
        .{ .src = &.{"@as(i32, @intFromFloat(@as(f64, 3.7)))"}, .want = @as(i32, @intFromFloat(@as(f64, 3.7))) },
        .{ .src = &.{"@as(usize, @intFromFloat(@as(f64, 5.9)))"}, .want = @as(usize, @intFromFloat(@as(f64, 5.9))) },
        .{ .src = &.{"@as(isize, @intFromFloat(@as(f64, -3.8)))"}, .want = @as(isize, @intFromFloat(@as(f64, -3.8))) },
        .{ .src = &.{"@as(c_int, @intFromFloat(@as(f64, 7.2)))"}, .want = @as(c_int, @intFromFloat(@as(f64, 7.2))) },
        .{ .src = &.{"@as(f32, @floatFromInt(16777217))"}, .want = @as(f32, @floatFromInt(16777217)) },
    });
}

test "compliance: unary float builtins fold at comptime" {
    try compliance.check(a, .{
        .{ .src = &.{"@sqrt(@as(f64, 16.0))"}, .want = @sqrt(@as(f64, 16.0)) },
        .{ .src = &.{"@floor(@as(f64, 3.7))"}, .want = @floor(@as(f64, 3.7)) },
        .{ .src = &.{"@ceil(@as(f32, 3.2))"}, .want = @ceil(@as(f32, 3.2)) },
        .{ .src = &.{"@trunc(@as(f64, -3.7))"}, .want = @trunc(@as(f64, -3.7)) },
        .{ .src = &.{"@round(@as(f64, 2.5))"}, .want = @round(@as(f64, 2.5)) },
        .{ .src = &.{"@log2(@as(f64, 8.0))"}, .want = @log2(@as(f64, 8.0)) },
        .{ .src = &.{"@exp2(@as(f64, 3.0))"}, .want = @exp2(@as(f64, 3.0)) },
        .{ .src = &.{"@sqrt(@as(@Vector(2, f32), .{ 4.0, 9.0 }))[1] == 3.0"}, .want = @sqrt(@as(@Vector(2, f32), .{ 4.0, 9.0 }))[1] == 3.0 },
        .{ .src = &.{"@floor(3.7)"}, .want = @floor(3.7) },
        .{ .src = &.{"@sqrt(@as(u8, 4))"}, .reject = {} },
        .{ .src = &.{"@TypeOf(@sqrt(@as(f64, undefined))) == f64"}, .want = @TypeOf(@sqrt(@as(f64, undefined))) == f64 },
    });
}

test "compliance: @abs narrows a signed int to unsigned" {
    try compliance.check(a, .{
        .{ .src = &.{"@abs(@as(i8, -5))"}, .want = @abs(@as(i8, -5)) },
        .{ .src = &.{"@abs(@as(i8, -128))"}, .want = @abs(@as(i8, -128)) },
        .{ .src = &.{"@TypeOf(@abs(@as(i8, -5))) == u8"}, .want = @TypeOf(@abs(@as(i8, -5))) == u8 },
        .{ .src = &.{"@abs(@as(u8, 5))"}, .want = @abs(@as(u8, 5)) },
        .{ .src = &.{"@abs(@as(f64, -3.5))"}, .want = @abs(@as(f64, -3.5)) },
        .{ .src = &.{"@abs(-7)"}, .want = @abs(-7) },
        .{ .src = &.{"@abs(@as(@Vector(2, i8), .{ -3, 4 }))[0]"}, .want = @abs(@as(@Vector(2, i8), .{ -3, 4 }))[0] },
        .{ .src = &.{"@abs(true)"}, .reject = {} },
    });
}

test "compliance: integer bit-count and bit/byte reversal builtins" {
    try compliance.check(a, .{
        .{ .src = &.{"@clz(@as(u8, 1))"}, .want = @clz(@as(u8, 1)) },
        .{ .src = &.{"@ctz(@as(u8, 8))"}, .want = @ctz(@as(u8, 8)) },
        .{ .src = &.{"@ctz(@as(u8, 0))"}, .want = @ctz(@as(u8, 0)) },
        .{ .src = &.{"@popCount(@as(u8, 0xff))"}, .want = @popCount(@as(u8, 0xff)) },
        .{ .src = &.{"@popCount(@as(i16, -1))"}, .want = @popCount(@as(i16, -1)) },
        .{ .src = &.{"@byteSwap(@as(u16, 0x1234))"}, .want = @byteSwap(@as(u16, 0x1234)) },
        .{ .src = &.{"@byteSwap(@as(u32, 0x11223344))"}, .want = @byteSwap(@as(u32, 0x11223344)) },
        .{ .src = &.{"@bitReverse(@as(u8, 0b10000000))"}, .want = @bitReverse(@as(u8, 0b10000000)) },
        .{ .src = &.{"@bitReverse(@as(i8, 1))"}, .want = @bitReverse(@as(i8, 1)) },
        .{ .src = &.{"@clz(@as(@Vector(2, u8), .{ 1, 255 }))[0]"}, .want = @clz(@as(@Vector(2, u8), .{ 1, 255 }))[0] },
        .{ .src = &.{"@TypeOf(@clz(@as(@Vector(0, u8), .{}))) == @Vector(0, u4)"}, .want = @TypeOf(@clz(@as(@Vector(0, u8), .{}))) == @Vector(0, u4) },
        .{ .src = &.{"@byteSwap(@as(u12, 1))"}, .reject = {} },
    });
}

test "compliance: intInfo unwraps vectors without misclassifying non-ints" {
    try compliance.check(a, .{
        .{ .src = &.{"(@as(@Vector(2, u8), .{ 1, 2 }) << @as(@Vector(2, u3), .{ 1, 2 }))[1]"}, .want = (@as(@Vector(2, u8), .{ 1, 2 }) << @as(@Vector(2, u3), .{ 1, 2 }))[1] },
        .{ .src = &.{"@typeInfo(@Vector(4, u8)) == .vector"}, .want = @typeInfo(@Vector(4, u8)) == .vector },
        .{ .src = &.{"@typeInfo([4]u8) == .array"}, .want = @typeInfo([4]u8) == .array },
        .{ .src = &.{"@typeInfo(*u8) == .pointer"}, .want = @typeInfo(*u8) == .pointer },
    });
}

test "compliance: bit_not and negate" {
    try compliance.check(a, .{
        .{ .src = &.{"~@as(u8, 5)"}, .want = ~@as(u8, 5) },
        .{ .src = &.{"~@as(i32, 100)"}, .want = ~@as(i32, 100) },
        .{ .src = &.{"-%@as(i8, -128)"}, .want = -%@as(i8, -128) },
        .{ .src = &.{"-@as(i32, 100)"}, .want = -@as(i32, 100) },
    });
}

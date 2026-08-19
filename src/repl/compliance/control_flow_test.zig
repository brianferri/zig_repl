const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: type-inferred locals (var y = expr)" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { var x: u8 = 5; x += 1; var y = x; y += 1; break :blk y; }"}, .want = compliance.want(blk: {
            var x: u8 = 5;
            x += 1;
            var y = x;
            y += 1;
            break :blk y;
        }) },
        .{ .src = &.{"blk: { var x: u8 = 5; x += 1; const y = x; break :blk y; }"}, .want = compliance.want(blk: {
            var x: u8 = 5;
            x += 1;
            const y = x;
            break :blk y;
        }) },
        .{ .src = &.{"blk: { const S = struct { a: u8, b: u8 }; var s = S{ .a = 1, .b = 2 }; s.a = 10; break :blk s.a + s.b; }"}, .want = compliance.want(blk: {
            const S = struct { a: u8, b: u8 };
            var s = S{ .a = 1, .b = 2 };
            s.a = 10;
            break :blk s.a + s.b;
        }) },
        .{ .src = &.{"blk: { const Q = struct { a: u8 }; const q = Q{ .a = 1 }; q.a = 2; break :blk q.a; }"}, .reject = true },
    });
}

test "compliance: for loops (range and array)" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { var s: u32 = 0; for (0..4) |i| { s += @intCast(i); } break :blk s; }"}, .want = compliance.want(blk: {
            var s: u32 = 0;
            for (0..4) |i| {
                s += @intCast(i);
            }
            break :blk s;
        }) },
        .{ .src = &.{"blk: { var s: u32 = 0; for (2..5) |i| { s += @intCast(i); } break :blk s; }"}, .want = compliance.want(blk: {
            var s: u32 = 0;
            for (2..5) |i| {
                s += @intCast(i);
            }
            break :blk s;
        }) },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30 }; var s: u32 = 0; for (arr) |x| { s += x; } break :blk s; }"}, .want = compliance.want(blk: {
            const arr = [_]u8{ 10, 20, 30 };
            var s: u32 = 0;
            for (arr) |x| {
                s += x;
            }
            break :blk s;
        }) },
        .{ .src = &.{"blk: { var s: u32 = 0; for (0..3) |i| { for (0..3) |j| { s += @intCast(i * j); } } break :blk s; }"}, .want = compliance.want(blk: {
            var s: u32 = 0;
            for (0..3) |i| {
                for (0..3) |j| {
                    s += @intCast(i * j);
                }
            }
            break :blk s;
        }) },
        .{ .src = &.{"blk: { var arr = [_]u8{ 1, 2, 3 }; for (&arr) |*e| { e.* += 10; } break :blk arr[0] + arr[1] + arr[2]; }"}, .want = compliance.want(blk: {
            var arr = [_]u8{ 1, 2, 3 };
            for (&arr) |*e| {
                e.* += 10;
            }
            break :blk arr[0] + arr[1] + arr[2];
        }) },
        .{ .src = &.{"blk: { var arr = [_]u8{ 5, 6, 7, 8 }; for (&arr) |*e| { e.* = e.* * 2; } break :blk arr[3]; }"}, .want = compliance.want(blk: {
            var arr = [_]u8{ 5, 6, 7, 8 };
            for (&arr) |*e| {
                e.* = e.* * 2;
            }
            break :blk arr[3];
        }) },
        .{ .src = &.{"blk: { var arr = [_]u32{ 0, 0, 0 }; for (&arr, 0..) |*e, i| { e.* = @intCast(i); } break :blk arr[2]; }"}, .want = compliance.want(blk: {
            var arr = [_]u32{ 0, 0, 0 };
            for (&arr, 0..) |*e, i| {
                e.* = @intCast(i);
            }
            break :blk arr[2];
        }) },
        // A `&array` operand's length comes from the array type, so an undefined destination is a valid loop operand.
        .{ .src = &.{"blk: { var result: [3]u8 = undefined; const src = [_]u8{ 4, 5, 6 }; for (&result, src) |*r, v| { r.* = v; } break :blk result[0] + result[2]; }"}, .want = compliance.want(blk: {
            var result: [3]u8 = undefined;
            const src = [_]u8{ 4, 5, 6 };
            for (&result, src) |*r, v| {
                r.* = v;
            }
            break :blk result[0] + result[2];
        }) },
    });
}

test "compliance: nested aggregate init and element store" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const arr: [2][3]u8 = .{ .{ 1, 2, 3 }, .{ 4, 5, 6 } }; break :blk arr[1][0] + arr[0][2]; }"}, .want = compliance.want(blk: {
            const arr: [2][3]u8 = .{ .{ 1, 2, 3 }, .{ 4, 5, 6 } };
            break :blk arr[1][0] + arr[0][2];
        }) },
        .{ .src = &.{"blk: { var m: [2][2]u8 = .{ .{ 1, 2 }, .{ 3, 4 } }; m[0][1] = 9; break :blk m[0][1] + m[1][0]; }"}, .want = compliance.want(blk: {
            var m: [2][2]u8 = .{ .{ 1, 2 }, .{ 3, 4 } };
            m[0][1] = 9;
            break :blk m[0][1] + m[1][0];
        }) },
        .{ .src = &.{"blk: { const S = struct { p: struct { x: u8 } }; var s: S = .{ .p = .{ .x = 1 } }; s.p.x = 7; break :blk s.p.x; }"}, .want = compliance.want(blk: {
            const S = struct { p: struct { x: u8 } };
            var s: S = .{ .p = .{ .x = 1 } };
            s.p.x = 7;
            break :blk s.p.x;
        }) },
    });
}

test "compliance: unreachable errors only when reached" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const x: u8 = 3; break :blk switch (x) { 3 => @as(i32, 7), else => unreachable }; }"}, .want = compliance.want(blk: {
            const x: u8 = 3;
            break :blk switch (x) {
                3 => @as(i32, 7),
                else => unreachable,
            };
        }) },
        // Reaching it is a compile error, matching a comptime `unreachable` in the compiler.
        .{ .src = &.{"blk: { const x: u8 = 9; break :blk switch (x) { 3 => @as(i32, 7), else => unreachable }; }"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { const x: u8 = 9; break :blk switch (x) { 3 => @as(i32, 7), else => unreachable }; }"}, "reached unreachable code");
}

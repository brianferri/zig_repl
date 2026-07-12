const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @Vector element indexing" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const v: @Vector(4, i32) = .{ 10, 20, 30, 40 }; break :blk v[2]; }"},
            .want = blk: {
                const v: @Vector(4, i32) = .{ 10, 20, 30, 40 };
                break :blk v[2];
            },
        },
        .{
            .src = &.{"blk: { const v: @Vector(4, i32) = .{ 10, 20, 30, 40 }; break :blk v[0] + v[3]; }"},
            .want = blk: {
                const v: @Vector(4, i32) = .{ 10, 20, 30, 40 };
                break :blk v[0] + v[3];
            },
        },
        .{
            .src = &.{"blk: { const v: @Vector(3, u8) = .{ 5, 6, 7 }; break :blk v[1]; }"},
            .want = blk: {
                const v: @Vector(3, u8) = .{ 5, 6, 7 };
                break :blk v[1];
            },
        },
        .{
            .src = &.{"blk: { const v: @Vector(3, u8) = .{ 5, 6, 7 }; break :blk v[5]; }"},
            .reject = {},
        },
    });
}

test "compliance: @Vector lane-wise arithmetic" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 8, 9, 20, 21 }; const y: @Vector(4, i32) = .{ 2, 3, 4, 5 }; const z = x + y; break :blk z[0] + z[3]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 8, 9, 20, 21 };
            const y: @Vector(4, i32) = .{ 2, 3, 4, 5 };
            const z = x + y;
            break :blk z[0] + z[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 8, 9, 20, 21 }; const y: @Vector(4, i32) = .{ 2, 3, 4, 5 }; const z = x - y; break :blk z[2]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 8, 9, 20, 21 };
            const y: @Vector(4, i32) = .{ 2, 3, 4, 5 };
            const z = x - y;
            break :blk z[2];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 8, 9, 20, 21 }; const y: @Vector(4, i32) = .{ 2, 3, 4, 5 }; const z = x * y; break :blk z[1]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 8, 9, 20, 21 };
            const y: @Vector(4, i32) = .{ 2, 3, 4, 5 };
            const z = x * y;
            break :blk z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 8, 9, 20, 21 }; const y: @Vector(4, i32) = .{ 2, 3, 4, 5 }; const z = @divFloor(x, y); break :blk z[2] + z[3]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 8, 9, 20, 21 };
            const y: @Vector(4, i32) = .{ 2, 3, 4, 5 };
            const z = @divFloor(x, y);
            break :blk z[2] + z[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 8, 9, 20, 21 }; const y: @Vector(4, i32) = .{ 2, 3, 4, 5 }; const z = @divTrunc(x, y); break :blk z[2]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 8, 9, 20, 21 };
            const y: @Vector(4, i32) = .{ 2, 3, 4, 5 };
            const z = @divTrunc(x, y);
            break :blk z[2];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 8, 9, 20, 21 }; const y: @Vector(4, i32) = .{ 2, 3, 4, 5 }; const z = @mod(x, y); break :blk z[1]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 8, 9, 20, 21 };
            const y: @Vector(4, i32) = .{ 2, 3, 4, 5 };
            const z = @mod(x, y);
            break :blk z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 8, 9, 20, 21 }; const y: @Vector(4, i32) = .{ 2, 3, 4, 5 }; const z = @rem(x, y); break :blk z[3]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 8, 9, 20, 21 };
            const y: @Vector(4, i32) = .{ 2, 3, 4, 5 };
            const z = @rem(x, y);
            break :blk z[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, i32) = .{ 20, 30 }; const y: @Vector(2, i32) = .{ 4, 5 }; const z = @divExact(x, y); break :blk z[0] + z[1]; }"}, .want = blk: {
            const x: @Vector(2, i32) = .{ 20, 30 };
            const y: @Vector(2, i32) = .{ 4, 5 };
            const z = @divExact(x, y);
            break :blk z[0] + z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 200, 10 }; const y: @Vector(2, u8) = .{ 100, 5 }; const z = x +% y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 200, 10 };
            const y: @Vector(2, u8) = .{ 100, 5 };
            const z = x +% y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 10, 10 }; const y: @Vector(2, u8) = .{ 200, 5 }; const z = x -% y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 10, 10 };
            const y: @Vector(2, u8) = .{ 200, 5 };
            const z = x -% y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 100, 10 }; const y: @Vector(2, u8) = .{ 200, 5 }; const z = x +| y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 100, 10 };
            const y: @Vector(2, u8) = .{ 200, 5 };
            const z = x +| y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 10, 10 }; const y: @Vector(2, u8) = .{ 200, 5 }; const z = x -| y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 10, 10 };
            const y: @Vector(2, u8) = .{ 200, 5 };
            const z = x -| y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, f32) = .{ 1.5, 2.5 }; const y: @Vector(2, f32) = .{ 0.5, 0.5 }; const z = x + y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, f32) = .{ 1.5, 2.5 };
            const y: @Vector(2, f32) = .{ 0.5, 0.5 };
            const z = x + y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, f64) = .{ 7.0, 9.0 }; const y: @Vector(2, f64) = .{ 2.0, 3.0 }; const z = x / y; break :blk z[1]; }"}, .want = blk: {
            const x: @Vector(2, f64) = .{ 7.0, 9.0 };
            const y: @Vector(2, f64) = .{ 2.0, 3.0 };
            const z = x / y;
            break :blk z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(3, i64) = .{ 1000000, 2, 3 }; const y: @Vector(3, i64) = .{ 1, 2, 3 }; const z = x + y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(3, i64) = .{ 1000000, 2, 3 };
            const y: @Vector(3, i64) = .{ 1, 2, 3 };
            const z = x + y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(3, i32) = .{ 1, 2, 3 }; const y: @Vector(3, i32) = .{ 4, 5, 6 }; const z = (x + y) * x; break :blk z[2]; }"}, .want = blk: {
            const x: @Vector(3, i32) = .{ 1, 2, 3 };
            const y: @Vector(3, i32) = .{ 4, 5, 6 };
            const z = (x + y) * x;
            break :blk z[2];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i16) = .{ 1, 2, 3, 4 }; const y: @Vector(4, i16) = .{ 5, 6, 7, 8 }; const z = x + y; const arr: [4]i16 = z; break :blk arr[3]; }"}, .want = blk: {
            const x: @Vector(4, i16) = .{ 1, 2, 3, 4 };
            const y: @Vector(4, i16) = .{ 5, 6, 7, 8 };
            const z = x + y;
            const arr: [4]i16 = z;
            break :blk arr[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 200, 1 }; const y: @Vector(2, u8) = .{ 100, 1 }; const z = x + y; break :blk z[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const x: @Vector(2, i32) = .{ 1, 2 }; const z = x * 2; break :blk z[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const x: @Vector(2, i32) = .{ 1, 2 }; const y: @Vector(3, i32) = .{ 1, 2, 3 }; const z = x + y; break :blk z[0]; }"}, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { const x: @Vector(2, i32) = .{ 1, 2 }; const z = x * 2; break :blk z[0]; }"}, "mixed scalar and vector operands");
    try compliance.expectDiagnostic(a, &.{"blk: { const x: @Vector(2, i32) = .{ 1, 2 }; const y: @Vector(3, i32) = .{ 1, 2, 3 }; const z = x + y; break :blk z[0]; }"}, "vector length mismatch");
}

test "compliance: @Vector lane-wise comparison" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const m = x == y; break :blk m[0]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const m = x == y;
            break :blk m[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const m = x == y; break :blk m[1]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const m = x == y;
            break :blk m[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const m = x != y; break :blk m[1]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const m = x != y;
            break :blk m[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const m = x < y; break :blk m[3]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const m = x < y;
            break :blk m[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const m = x > y; break :blk m[1]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const m = x > y;
            break :blk m[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const m = x <= y; break :blk m[0]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const m = x <= y;
            break :blk m[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const m = x >= y; break :blk m[2]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const m = x >= y;
            break :blk m[2];
        } },
        .{ .src = &.{"blk: { const p: @Vector(2, f32) = .{ 1.5, 2.5 }; const q: @Vector(2, f32) = .{ 1.5, 1.0 }; const m = p >= q; break :blk m[1]; }"}, .want = blk: {
            const p: @Vector(2, f32) = .{ 1.5, 2.5 };
            const q: @Vector(2, f32) = .{ 1.5, 1.0 };
            const m = p >= q;
            break :blk m[1];
        } },
        .{ .src = &.{"blk: { const p: @Vector(2, i32) = .{ 1, 2 }; const q: @Vector(2, i32) = .{ 1, 3 }; const m = p == q; break :blk @as(type, @TypeOf(m)) == @as(type, @Vector(2, bool)); }"}, .want = blk: {
            const p: @Vector(2, i32) = .{ 1, 2 };
            const q: @Vector(2, i32) = .{ 1, 3 };
            const m = p == q;
            break :blk @as(type, @TypeOf(m)) == @as(type, @Vector(2, bool));
        } },
        .{ .src = &.{"blk: { const p: @Vector(2, i32) = .{ 1, 2 }; const m = p == 1; break :blk m[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const p: @Vector(2, i32) = .{ 1, 2 }; const q: @Vector(3, i32) = .{ 1, 2, 3 }; const m = p == q; break :blk m[0]; }"}, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { const p: @Vector(2, i32) = .{ 1, 2 }; const m = p == 1; break :blk m[0]; }"}, "mixed scalar and vector operands");
}

test "compliance: @splat broadcasts a scalar to a vector or array" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const v: @Vector(4, i32) = @splat(7); break :blk v[0] + v[3]; }"}, .want = blk: {
            const v: @Vector(4, i32) = @splat(7);
            break :blk v[0] + v[3];
        } },
        .{ .src = &.{"blk: { const v: @Vector(2, f32) = @splat(1.5); break :blk v[1]; }"}, .want = blk: {
            const v: @Vector(2, f32) = @splat(1.5);
            break :blk v[1];
        } },
        .{ .src = &.{"blk: { const a2: [3]u8 = @splat(9); break :blk a2[0] + a2[2]; }"}, .want = blk: {
            const a2: [3]u8 = @splat(9);
            break :blk a2[0] + a2[2];
        } },
        .{ .src = &.{"blk: { const v: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const z = v + @as(@Vector(4, i32), @splat(10)); break :blk z[2]; }"}, .want = blk: {
            const v: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const z = v + @as(@Vector(4, i32), @splat(10));
            break :blk z[2];
        } },
        .{ .src = &.{"blk: { const v: @Vector(4, i32) = .{ 1, 9, 3, 9 }; const m = v == @as(@Vector(4, i32), @splat(9)); break :blk m[1]; }"}, .want = blk: {
            const v: @Vector(4, i32) = .{ 1, 9, 3, 9 };
            const m = v == @as(@Vector(4, i32), @splat(9));
            break :blk m[1];
        } },
        .{ .src = &.{"blk: { const s: [3:0]u8 = @splat(9); break :blk s[0] + s[2] + s.len; }"}, .want = blk: {
            const s: [3:0]u8 = @splat(9);
            break :blk s[0] + s[2] + s.len;
        } },
        .{ .src = &.{"blk: { const S = struct { x: u8, y: u8 }; const arr: [3]S = @splat(.{ .x = 1, .y = 2 }); break :blk arr[2].x + arr[0].y; }"}, .want = blk: {
            const S = struct { x: u8, y: u8 };
            const arr: [3]S = @splat(.{ .x = 1, .y = 2 });
            break :blk arr[2].x + arr[0].y;
        } },
        .{ .src = &.{"blk: { const arr: [2][3]u8 = @splat(.{ 7, 8, 9 }); break :blk arr[1][2]; }"}, .want = blk: {
            const arr: [2][3]u8 = @splat(.{ 7, 8, 9 });
            break :blk arr[1][2];
        } },
        .{ .src = &.{"blk: { const E = enum { red, green }; const arr: [3]E = @splat(.green); break :blk @intFromEnum(arr[1]); }"}, .want = blk: {
            const E = enum { red, green };
            const arr: [3]E = @splat(.green);
            break :blk @intFromEnum(arr[1]);
        } },
        .{ .src = &.{"blk: { const v: @Vector(4, bool) = @splat(true); break :blk v[2]; }"}, .want = blk: {
            const v: @Vector(4, bool) = @splat(true);
            break :blk v[2];
        } },
        .{ .src = &.{"blk: { const x: u8 = 3; const v: @Vector(4, u8) = @splat(x); break :blk v[0] + x; }"}, .want = blk: {
            const x: u8 = 3;
            const v: @Vector(4, u8) = @splat(x);
            break :blk v[0] + x;
        } },
        .{ .src = &.{"blk: { const x: i32 = @splat(5); break :blk x; }"}, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { const x: i32 = @splat(5); break :blk x; }"}, "expected array or vector type, found 'i32'");
}

test "compliance: @Vector lane-wise bitwise, shift, and negation" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 12, 10 }; const y: @Vector(2, u8) = .{ 10, 6 }; const z = x & y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 12, 10 };
            const y: @Vector(2, u8) = .{ 10, 6 };
            const z = x & y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 12, 10 }; const y: @Vector(2, u8) = .{ 10, 6 }; const z = x | y; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 12, 10 };
            const y: @Vector(2, u8) = .{ 10, 6 };
            const z = x | y;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 12, 10 }; const y: @Vector(2, u8) = .{ 10, 6 }; const z = x ^ y; break :blk z[1]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 12, 10 };
            const y: @Vector(2, u8) = .{ 10, 6 };
            const z = x ^ y;
            break :blk z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 1, 2 }; const y: @Vector(2, u3) = .{ 3, 2 }; const z = x << y; break :blk z[0] + z[1]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 1, 2 };
            const y: @Vector(2, u3) = .{ 3, 2 };
            const z = x << y;
            break :blk z[0] + z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 16, 32 }; const y: @Vector(2, u3) = .{ 2, 1 }; const z = x >> y; break :blk z[0] + z[1]; }"}, .want = blk: {
            const x: @Vector(2, u8) = .{ 16, 32 };
            const y: @Vector(2, u3) = .{ 2, 1 };
            const z = x >> y;
            break :blk z[0] + z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(3, i32) = .{ 5, -6, 7 }; const z = -x; break :blk z[0] + z[1] + z[2]; }"}, .want = blk: {
            const x: @Vector(3, i32) = .{ 5, -6, 7 };
            const z = -x;
            break :blk z[0] + z[1] + z[2];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, f32) = .{ 1.5, -2.5 }; const z = -x; break :blk z[1]; }"}, .want = blk: {
            const x: @Vector(2, f32) = .{ 1.5, -2.5 };
            const z = -x;
            break :blk z[1];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, i8) = .{ -128, 1 }; const z = -%x; break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(2, i8) = .{ -128, 1 };
            const z = -%x;
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, u8) = .{ 1, 2 }; const z = x & 3; break :blk z[0]; }"}, .reject = {} },
    });
}

test "compliance: @select blends two vectors by a bool mask" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const p: @Vector(4, bool) = .{ true, false, true, false }; const x: @Vector(4, i32) = .{ 1, 2, 3, 4 }; const y: @Vector(4, i32) = .{ 10, 20, 30, 40 }; const z = @select(i32, p, x, y); break :blk z[0] + z[1] + z[2] + z[3]; }"}, .want = blk: {
            const p: @Vector(4, bool) = .{ true, false, true, false };
            const x: @Vector(4, i32) = .{ 1, 2, 3, 4 };
            const y: @Vector(4, i32) = .{ 10, 20, 30, 40 };
            const z = @select(i32, p, x, y);
            break :blk z[0] + z[1] + z[2] + z[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 1, 5, 3, 9 }; const y: @Vector(4, i32) = .{ 4, 2, 6, 1 }; const z = @select(i32, x < y, x, y); break :blk z[0] + z[1] + z[2] + z[3]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 1, 5, 3, 9 };
            const y: @Vector(4, i32) = .{ 4, 2, 6, 1 };
            const z = @select(i32, x < y, x, y);
            break :blk z[0] + z[1] + z[2] + z[3];
        } },
        .{ .src = &.{"blk: { const p: @Vector(2, bool) = .{ true, false }; const x: @Vector(2, f32) = .{ 1.5, 2.5 }; const y: @Vector(2, f32) = .{ 9.0, 8.0 }; const z = @select(f32, p, x, y); break :blk z[1]; }"}, .want = blk: {
            const p: @Vector(2, bool) = .{ true, false };
            const x: @Vector(2, f32) = .{ 1.5, 2.5 };
            const y: @Vector(2, f32) = .{ 9.0, 8.0 };
            const z = @select(f32, p, x, y);
            break :blk z[1];
        } },
    });
}

test "compliance: @shuffle picks lanes from two vectors by an i32 mask" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 10, 20, 30, 40 }; const y: @Vector(4, i32) = .{ 100, 200, 300, 400 }; const m: @Vector(4, i32) = .{ 0, -1, 2, -4 }; const z = @shuffle(i32, x, y, m); break :blk z[0] + z[1] + z[2] + z[3]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 10, 20, 30, 40 };
            const y: @Vector(4, i32) = .{ 100, 200, 300, 400 };
            const m: @Vector(4, i32) = .{ 0, -1, 2, -4 };
            const z = @shuffle(i32, x, y, m);
            break :blk z[0] + z[1] + z[2] + z[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, i32) = .{ 1, 2 }; const y: @Vector(2, i32) = .{ 3, 4 }; const m: @Vector(4, i32) = .{ 1, 0, -1, -2 }; const z = @shuffle(i32, x, y, m); break :blk z[0] + z[3]; }"}, .want = blk: {
            const x: @Vector(2, i32) = .{ 1, 2 };
            const y: @Vector(2, i32) = .{ 3, 4 };
            const m: @Vector(4, i32) = .{ 1, 0, -1, -2 };
            const z = @shuffle(i32, x, y, m);
            break :blk z[0] + z[3];
        } },
        .{ .src = &.{"blk: { const x: @Vector(4, i32) = .{ 10, 20, 30, 40 }; const y: @Vector(4, i32) = .{ 100, 200, 300, 400 }; const m: @Vector(4, i32) = .{ 3, 2, 1, 0 }; const z = @shuffle(i32, x, y, m); break :blk z[0]; }"}, .want = blk: {
            const x: @Vector(4, i32) = .{ 10, 20, 30, 40 };
            const y: @Vector(4, i32) = .{ 100, 200, 300, 400 };
            const m: @Vector(4, i32) = .{ 3, 2, 1, 0 };
            const z = @shuffle(i32, x, y, m);
            break :blk z[0];
        } },
        .{ .src = &.{"blk: { const x: @Vector(2, i32) = .{ 1, 2 }; const y: @Vector(2, i32) = .{ 3, 4 }; const m: @Vector(2, i32) = .{ 5, 0 }; const z = @shuffle(i32, x, y, m); break :blk z[0]; }"}, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { const x: @Vector(2, i32) = .{ 1, 2 }; const y: @Vector(2, i32) = .{ 3, 4 }; const m: @Vector(2, i32) = .{ 5, 0 }; const z = @shuffle(i32, x, y, m); break :blk z[0]; }"}, "selects out-of-bounds index");
}

test "compliance: @Vector and arrays are distinct but interconvertible" {
    try compliance.check(a, .{
        .{ .src = &.{"@as(type, [4]i32) == @as(type, @Vector(4, i32))"}, .want = @as(type, [4]i32) == @as(type, @Vector(4, i32)) },
        .{ .src = &.{"blk: { const arr = [4]i32{ 1, 2, 3, 4 }; const v: @Vector(4, i32) = arr; break :blk v[2]; }"}, .want = blk: {
            const arr = [4]i32{ 1, 2, 3, 4 };
            const v: @Vector(4, i32) = arr;
            break :blk v[2];
        } },
        .{ .src = &.{"blk: { const v: @Vector(4, i32) = .{ 10, 20, 30, 40 }; const arr: [4]i32 = v; break :blk arr[3]; }"}, .want = blk: {
            const v: @Vector(4, i32) = .{ 10, 20, 30, 40 };
            const arr: [4]i32 = v;
            break :blk arr[3];
        } },
        .{ .src = &.{"blk: { const arr = [3]u8{ 1, 2, 3 }; const v: @Vector(4, u8) = arr; break :blk v[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const T = @Vector(3, [2]u8); break :blk @sizeOf(T); }"}, .reject = {} },
        .{ .src = &.{"blk: { const T = @Vector(2, struct { x: u8 }); break :blk @sizeOf(T); }"}, .reject = {} },
        .{ .src = &.{"blk: { const S = struct { x: u8 }; const arr = [2]S{ .{ .x = 1 }, .{ .x = 2 } }; break :blk arr[1].x; }"}, .want = blk: {
            const S = struct { x: u8 };
            const arr = [2]S{ .{ .x = 1 }, .{ .x = 2 } };
            break :blk arr[1].x;
        } },
        .{ .src = &.{"blk: { const arr = [2]u8{ 1, 2, 3 }; break :blk arr[0]; }"}, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { const arr = [2]u8{ 1, 2, 3 }; break :blk arr[0]; }"}, "expected 2 array elements; found 3");
}

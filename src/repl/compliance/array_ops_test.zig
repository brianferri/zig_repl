const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @memcpy copies a slice range" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, .{
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(dst[0..3], src[0..3]); break :blk dst[0] + dst[2]; }"}, .want = blk: {
            var dst = [_]u8{ 0, 0, 0 };
            const src = [_]u8{ 7, 8, 9 };
            @memcpy(dst[0..3], src[0..3]);
            break :blk dst[0] + dst[2];
        } },
        .{ .src = &.{"blk: { var dst = [_]u8{ 1, 2, 3, 4 }; const src = [_]u8{ 8, 9 }; @memcpy(dst[1..3], src[0..2]); break :blk dst[0] + dst[1] + dst[2] + dst[3]; }"}, .want = blk: {
            var dst = [_]u8{ 1, 2, 3, 4 };
            const src = [_]u8{ 8, 9 };
            @memcpy(dst[1..3], src[0..2]);
            break :blk dst[0] + dst[1] + dst[2] + dst[3];
        } },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 4, 5, 6 }; @memcpy(&dst, &src); break :blk dst[0] + dst[2]; }"}, .want = blk: {
            var dst = [_]u8{ 0, 0, 0 };
            const src = [_]u8{ 4, 5, 6 };
            @memcpy(&dst, &src);
            break :blk dst[0] + dst[2];
        } },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(&dst, src[0..3]); break :blk dst[0] + dst[2]; }"}, .want = blk: {
            var dst = [_]u8{ 0, 0, 0 };
            const src = [_]u8{ 7, 8, 9 };
            @memcpy(&dst, src[0..3]);
            break :blk dst[0] + dst[2];
        } },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0, 0 }; const src = [_]u8{ 1, 2 }; @memcpy(dst[1..3], &src); break :blk dst[1] + dst[2]; }"}, .want = blk: {
            var dst = [_]u8{ 0, 0, 0, 0 };
            const src = [_]u8{ 1, 2 };
            @memcpy(dst[1..3], &src);
            break :blk dst[1] + dst[2];
        } },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(dst[1..3], src[0..3]); break :blk dst[1]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(dst[0..3], src[0..3]); break :blk dst[1]; }"}, .reject = {} },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0 }; const src = [_]u16{ 1, 2 }; @memcpy(dst[0..2], src[0..2]); break :blk dst[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { var arr = [_]u8{ 1, 2, 3, 4 }; @memcpy(arr[0..3], arr[1..4]); break :blk arr[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { var arr = [_]u8{ 1, 2, 3, 4 }; @memcpy(arr[1..4], arr[0..3]); break :blk arr[1]; }"}, .reject = {} },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 1, 2 }; @memcpy(&dst, &src); break :blk dst[0]; }"}, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { var dst = [_]u8{ 0, 0 }; const src = [_]u16{ 1, 2 }; @memcpy(dst[0..2], src[0..2]); break :blk dst[0]; }"}, "cannot represent all possible");
}

test "compliance: @memcpy ported behavior cases" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { var foo = [_]u8{ 65, 66, 67 }; var bar: [3]u8 = undefined; @memcpy(&bar, &foo); break :blk bar[2]; }"}, .want = blk: {
            var foo = [_]u8{ 65, 66, 67 };
            var bar: [3]u8 = undefined;
            @memcpy(&bar, &foo);
            break :blk bar[2];
        } },
        .{ .src = &.{"blk: { var buf: [5]u8 = undefined; const dst: []u8 = &buf; const src: []const u8 = \"hello\"; @memcpy(dst, src); break :blk @as(u16, buf[0]) + buf[4]; }"}, .want = blk: {
            var buf: [5]u8 = undefined;
            const dst: []u8 = &buf;
            const src: []const u8 = "hello";
            @memcpy(dst, src);
            break :blk @as(u16, buf[0]) + buf[4];
        } },
        .{ .src = &.{"blk: { var buf: [3]void = undefined; const s: []void = &buf; @memcpy(s, s); break :blk @as(u8, 42); }"}, .want = blk: {
            var buf: [3]void = undefined;
            const s: []void = &buf;
            @memcpy(s, s);
            break :blk @as(u8, 42);
        } },
        // Comptime-only element type ([N]type): `zig run` can't be an oracle, but the
        // reference is comptime-folded here just the same.
        .{ .src = &.{"blk: { const in: [2]type = .{ u8, u16 }; var out: [2]type = undefined; @memcpy(&out, &in); break :blk out[0] == u8 and out[1] == u16; }"}, .want = blk: {
            const in: [2]type = .{ u8, u16 };
            var out: [2]type = undefined;
            @memcpy(&out, &in);
            break :blk out[0] == u8 and out[1] == u16;
        } },
    });
}

test "compliance: typed array initialization ([N]T = .{ ... })" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const arr: [3]u8 = .{ 7, 8, 9 }; break :blk arr[2]; }"}, .want = blk: {
            const arr: [3]u8 = .{ 7, 8, 9 };
            break :blk arr[2];
        } },
        .{ .src = &.{"blk: { const arr: [3]u8 = .{ 7, 8, 9 }; break :blk arr[0] + arr[1] + arr[2]; }"}, .want = blk: {
            const arr: [3]u8 = .{ 7, 8, 9 };
            break :blk arr[0] + arr[1] + arr[2];
        } },
        .{ .src = &.{"blk: { const arr: [3]u8 = .{ 1, 2 }; break :blk arr[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const arr: [2]u8 = .{ 1, 2, 3 }; break :blk arr[0]; }"}, .reject = {} },
    });
}

test "compliance: sentinel array types ([N:S]T)" {
    try compliance.check(a, .{
        .{ .src = &.{"[3:0]u8"}, .want = [3:0]u8 },
        .{ .src = &.{"blk: { const arr: [3:0]u8 = .{ 1, 2, 3 }; break :blk arr.len; }"}, .want = blk: {
            const arr: [3:0]u8 = .{ 1, 2, 3 };
            break :blk arr.len;
        } },
        .{ .src = &.{"blk: { const arr: [3:0]u8 = .{ 1, 2, 3 }; break :blk arr[1]; }"}, .want = blk: {
            const arr: [3:0]u8 = .{ 1, 2, 3 };
            break :blk arr[1];
        } },
        .{ .src = &.{"blk: { const arr = [_:9]u8{ 4, 5 }; break :blk arr.len; }"}, .want = blk: {
            const arr = [_:9]u8{ 4, 5 };
            break :blk arr.len;
        } },
        .{ .src = &.{"blk: { const arr = [_:9]u8{ 4, 5 }; break :blk arr[0]; }"}, .want = blk: {
            const arr = [_:9]u8{ 4, 5 };
            break :blk arr[0];
        } },
        .{ .src = &.{"@as(type, [3:0]u8) == @as(type, [3:0]u8)"}, .want = @as(type, [3:0]u8) == @as(type, [3:0]u8) },
        .{ .src = &.{"@as(type, [3:0]u8) == @as(type, [3:1]u8)"}, .want = @as(type, [3:0]u8) == @as(type, [3:1]u8) },
        .{ .src = &.{"@as(type, [3:0]u8) == @as(type, [3]u8)"}, .want = @as(type, [3:0]u8) == @as(type, [3]u8) },
        .{ .src = &.{"blk: { const arr: [2:256]u8 = .{ 1, 2 }; break :blk arr[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const a: [2:1.5]u8 = .{ 1, 2 }; break :blk a[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const a: [2:\"hi\"]u8 = .{ 1, 2 }; break :blk a[0]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const T = [3:undefined]u8; break :blk @sizeOf(T); }"}, .reject = {} },
        .{ .src = &.{"blk: { const S = struct { x: u8 }; const T = [2:S{ .x = 0 }]S; break :blk @sizeOf(T); }"}, .reject = {} },
        .{ .src = &.{"blk: { const T = [2:\"x\"][]const u8; break :blk @sizeOf(T); }"}, .reject = {} },
    });
}

test "compliance: slices nested in structs and arrays of slices" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const S = struct { name: []const u8 }; const s = S{ .name = \"hello\" }; break :blk s.name.len; }"}, .want = blk: {
            const S = struct { name: []const u8 };
            const s = S{ .name = "hello" };
            break :blk s.name.len;
        } },
        .{ .src = &.{"blk: { const S = struct { name: []const u8 }; const s = S{ .name = \"abc\" }; break :blk s.name[1]; }"}, .want = blk: {
            const S = struct { name: []const u8 };
            const s = S{ .name = "abc" };
            break :blk s.name[1];
        } },
        .{ .src = &.{"blk: { const arr = [_][]const u8{ \"a\", \"bb\", \"ccc\" }; break :blk arr[2].len; }"}, .want = blk: {
            const arr = [_][]const u8{ "a", "bb", "ccc" };
            break :blk arr[2].len;
        } },
        .{ .src = &.{"blk: { const arr = [_][]const u8{ \"a\", \"bb\", \"ccc\" }; break :blk arr[0][0]; }"}, .want = blk: {
            const arr = [_][]const u8{ "a", "bb", "ccc" };
            break :blk arr[0][0];
        } },
        .{ .src = &.{"blk: { const W = struct { rows: [2][]const u8 }; const w = W{ .rows = .{ \"xy\", \"z\" } }; break :blk w.rows[0][1]; }"}, .want = blk: {
            const W = struct { rows: [2][]const u8 };
            const w = W{ .rows = .{ "xy", "z" } };
            break :blk w.rows[0][1];
        } },
    });
}

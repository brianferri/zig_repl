const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @memcpy copies a slice range" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(dst[0..3], src[0..3]); break :blk dst[0] + dst[2]; }"}, .want = compliance.want(blk: {
            var dst = [_]u8{ 0, 0, 0 };
            const src = [_]u8{ 7, 8, 9 };
            @memcpy(dst[0..3], src[0..3]);
            break :blk dst[0] + dst[2];
        }) },
        .{ .src = &.{"blk: { var dst = [_]u8{ 1, 2, 3, 4 }; const src = [_]u8{ 8, 9 }; @memcpy(dst[1..3], src[0..2]); break :blk dst[0] + dst[1] + dst[2] + dst[3]; }"}, .want = compliance.want(blk: {
            var dst = [_]u8{ 1, 2, 3, 4 };
            const src = [_]u8{ 8, 9 };
            @memcpy(dst[1..3], src[0..2]);
            break :blk dst[0] + dst[1] + dst[2] + dst[3];
        }) },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 4, 5, 6 }; @memcpy(&dst, &src); break :blk dst[0] + dst[2]; }"}, .want = compliance.want(blk: {
            var dst = [_]u8{ 0, 0, 0 };
            const src = [_]u8{ 4, 5, 6 };
            @memcpy(&dst, &src);
            break :blk dst[0] + dst[2];
        }) },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(&dst, src[0..3]); break :blk dst[0] + dst[2]; }"}, .want = compliance.want(blk: {
            var dst = [_]u8{ 0, 0, 0 };
            const src = [_]u8{ 7, 8, 9 };
            @memcpy(&dst, src[0..3]);
            break :blk dst[0] + dst[2];
        }) },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0, 0 }; const src = [_]u8{ 1, 2 }; @memcpy(dst[1..3], &src); break :blk dst[1] + dst[2]; }"}, .want = compliance.want(blk: {
            var dst = [_]u8{ 0, 0, 0, 0 };
            const src = [_]u8{ 1, 2 };
            @memcpy(dst[1..3], &src);
            break :blk dst[1] + dst[2];
        }) },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(dst[1..3], src[0..3]); break :blk dst[1]; }"}, .reject = true },
        .{ .src = &.{"blk: { const dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 7, 8, 9 }; @memcpy(dst[0..3], src[0..3]); break :blk dst[1]; }"}, .reject = true },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0 }; const src = [_]u16{ 1, 2 }; @memcpy(dst[0..2], src[0..2]); break :blk dst[0]; }"}, .reject = true },
        .{ .src = &.{"blk: { var arr = [_]u8{ 1, 2, 3, 4 }; @memcpy(arr[0..3], arr[1..4]); break :blk arr[0]; }"}, .reject = true },
        .{ .src = &.{"blk: { var arr = [_]u8{ 1, 2, 3, 4 }; @memcpy(arr[1..4], arr[0..3]); break :blk arr[1]; }"}, .reject = true },
        .{ .src = &.{"blk: { var dst = [_]u8{ 0, 0, 0 }; const src = [_]u8{ 1, 2 }; @memcpy(&dst, &src); break :blk dst[0]; }"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { var dst = [_]u8{ 0, 0 }; const src = [_]u16{ 1, 2 }; @memcpy(dst[0..2], src[0..2]); break :blk dst[0]; }"}, "cannot represent all possible");
}

test "compliance: @memset writes a value to every element" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { var buf: [4]u8 = undefined; @memset(&buf, 7); break :blk buf[0] + buf[3]; }"}, .want = compliance.want(blk: {
            var buf: [4]u8 = undefined;
            @memset(&buf, 7);
            break :blk buf[0] + buf[3];
        }) },
        .{ .src = &.{"blk: { var buf = [_]u8{ 1, 2, 3 }; @memset(buf[0..2], 0); break :blk buf[0] + buf[2]; }"}, .want = compliance.want(blk: {
            var buf = [_]u8{ 1, 2, 3 };
            @memset(buf[0..2], 0);
            break :blk buf[0] + buf[2];
        }) },
        // A const destination cannot be written.
        .{ .src = &.{"blk: { const buf = [_]u8{ 1, 2, 3 }; @memset(&buf, 0); break :blk buf[0]; }"}, .reject = true },
    });
}

test "compliance: @memcpy ported behavior cases" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { var foo = [_]u8{ 65, 66, 67 }; var bar: [3]u8 = undefined; @memcpy(&bar, &foo); break :blk bar[2]; }"}, .want = compliance.want(blk: {
            var foo = [_]u8{ 65, 66, 67 };
            var bar: [3]u8 = undefined;
            @memcpy(&bar, &foo);
            break :blk bar[2];
        }) },
        .{ .src = &.{"blk: { var buf: [5]u8 = undefined; const dst: []u8 = &buf; const src: []const u8 = \"hello\"; @memcpy(dst, src); break :blk @as(u16, buf[0]) + buf[4]; }"}, .want = compliance.want(blk: {
            var buf: [5]u8 = undefined;
            const dst: []u8 = &buf;
            const src: []const u8 = "hello";
            @memcpy(dst, src);
            break :blk @as(u16, buf[0]) + buf[4];
        }) },
        .{ .src = &.{"blk: { var buf: [3]void = undefined; const s: []void = &buf; @memcpy(s, s); break :blk @as(u8, 42); }"}, .want = compliance.want(blk: {
            var buf: [3]void = undefined;
            const s: []void = &buf;
            @memcpy(s, s);
            break :blk @as(u8, 42);
        }) },
        // Comptime-only element type ([N]type): `zig run` can't be an oracle, but the
        // reference is comptime-folded here just the same.
        .{ .src = &.{"blk: { const in: [2]type = .{ u8, u16 }; var out: [2]type = undefined; @memcpy(&out, &in); break :blk out[0] == u8 and out[1] == u16; }"}, .want = compliance.want(blk: {
            const in: [2]type = .{ u8, u16 };
            var out: [2]type = undefined;
            @memcpy(&out, &in);
            break :blk out[0] == u8 and out[1] == u16;
        }) },
    });
}

test "compliance: typed array initialization ([N]T = .{ ... })" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const arr: [3]u8 = .{ 7, 8, 9 }; break :blk arr[2]; }"}, .want = compliance.want(blk: {
            const arr: [3]u8 = .{ 7, 8, 9 };
            break :blk arr[2];
        }) },
        .{ .src = &.{"blk: { const arr: [3]u8 = .{ 7, 8, 9 }; break :blk arr[0] + arr[1] + arr[2]; }"}, .want = compliance.want(blk: {
            const arr: [3]u8 = .{ 7, 8, 9 };
            break :blk arr[0] + arr[1] + arr[2];
        }) },
        .{ .src = &.{"blk: { const arr: [3]u8 = .{ 1, 2 }; break :blk arr[0]; }"}, .reject = true },
        .{ .src = &.{"blk: { const arr: [2]u8 = .{ 1, 2, 3 }; break :blk arr[0]; }"}, .reject = true },
    });
}

test "compliance: empty init to array and slice-via-address-of" {
    try compliance.check(a, &.{
        // `T{}` on an array type yields an empty array.
        .{ .src = &.{"([0]u8{}).len"}, .want = compliance.want(([0]u8{}).len) },
        .{ .src = &.{"@as([0]u8, .{}).len"}, .want = compliance.want(@as([0]u8, .{}).len) },
        // `&.{}` builds a zero-length array behind a slice, carrying the slice's sentinel.
        .{ .src = &.{"@as([]const u8, &.{}).len"}, .want = compliance.want(@as([]const u8, &.{}).len) },
        .{ .src = &.{"@as([:0]const u8, &.{}).len"}, .want = compliance.want(@as([:0]const u8, &.{}).len) },
        // The std.process.Environ.PosixBlock.empty shape: a sentinel slice of optional many-ptrs.
        .{ .src = &.{"@as([:null]const ?[*:0]const u8, &.{}).len"}, .want = compliance.want(@as([:null]const ?[*:0]const u8, &.{}).len) },
        .{ .src = &.{"blk: { const S = struct { slice: [:null]const ?[*:0]const u8 }; const e: S = .{ .slice = &.{} }; break :blk e.slice.len; }"}, .want = compliance.want(blk: {
            const S = struct { slice: [:null]const ?[*:0]const u8 };
            const e: S = .{ .slice = &.{} };
            break :blk e.slice.len;
        }) },
    });
}

test "compliance: sentinel array types ([N:S]T)" {
    try compliance.check(a, &.{
        .{ .src = &.{"[3:0]u8"}, .want = compliance.want([3:0]u8) },
        .{ .src = &.{"blk: { const arr: [3:0]u8 = .{ 1, 2, 3 }; break :blk arr.len; }"}, .want = compliance.want(blk: {
            const arr: [3:0]u8 = .{ 1, 2, 3 };
            break :blk arr.len;
        }) },
        .{ .src = &.{"blk: { const arr: [3:0]u8 = .{ 1, 2, 3 }; break :blk arr[1]; }"}, .want = compliance.want(blk: {
            const arr: [3:0]u8 = .{ 1, 2, 3 };
            break :blk arr[1];
        }) },
        .{ .src = &.{"blk: { const arr = [_:9]u8{ 4, 5 }; break :blk arr.len; }"}, .want = compliance.want(blk: {
            const arr = [_:9]u8{ 4, 5 };
            break :blk arr.len;
        }) },
        .{ .src = &.{"blk: { const arr = [_:9]u8{ 4, 5 }; break :blk arr[0]; }"}, .want = compliance.want(blk: {
            const arr = [_:9]u8{ 4, 5 };
            break :blk arr[0];
        }) },
        .{ .src = &.{"@as(type, [3:0]u8) == @as(type, [3:0]u8)"}, .want = compliance.want(@as(type, [3:0]u8) == @as(type, [3:0]u8)) },
        .{ .src = &.{"@as(type, [3:0]u8) == @as(type, [3:1]u8)"}, .want = compliance.want(@as(type, [3:0]u8) == @as(type, [3:1]u8)) },
        .{ .src = &.{"@as(type, [3:0]u8) == @as(type, [3]u8)"}, .want = compliance.want(@as(type, [3:0]u8) == @as(type, [3]u8)) },
        .{ .src = &.{"blk: { const arr: [2:256]u8 = .{ 1, 2 }; break :blk arr[0]; }"}, .reject = true },
        .{ .src = &.{"blk: { const a: [2:1.5]u8 = .{ 1, 2 }; break :blk a[0]; }"}, .reject = true },
        .{ .src = &.{"blk: { const a: [2:\"hi\"]u8 = .{ 1, 2 }; break :blk a[0]; }"}, .reject = true },
        .{ .src = &.{"blk: { const T = [3:undefined]u8; break :blk @sizeOf(T); }"}, .reject = true },
        .{ .src = &.{"blk: { const S = struct { x: u8 }; const T = [2:S{ .x = 0 }]S; break :blk @sizeOf(T); }"}, .reject = true },
        .{ .src = &.{"blk: { const T = [2:\"x\"][]const u8; break :blk @sizeOf(T); }"}, .reject = true },
    });
}

test "compliance: slices nested in structs and arrays of slices" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const S = struct { name: []const u8 }; const s = S{ .name = \"hello\" }; break :blk s.name.len; }"}, .want = compliance.want(blk: {
            const S = struct { name: []const u8 };
            const s = S{ .name = "hello" };
            break :blk s.name.len;
        }) },
        .{ .src = &.{"blk: { const S = struct { name: []const u8 }; const s = S{ .name = \"abc\" }; break :blk s.name[1]; }"}, .want = compliance.want(blk: {
            const S = struct { name: []const u8 };
            const s = S{ .name = "abc" };
            break :blk s.name[1];
        }) },
        .{ .src = &.{"blk: { const arr = [_][]const u8{ \"a\", \"bb\", \"ccc\" }; break :blk arr[2].len; }"}, .want = compliance.want(blk: {
            const arr = [_][]const u8{ "a", "bb", "ccc" };
            break :blk arr[2].len;
        }) },
        .{ .src = &.{"blk: { const arr = [_][]const u8{ \"a\", \"bb\", \"ccc\" }; break :blk arr[0][0]; }"}, .want = compliance.want(blk: {
            const arr = [_][]const u8{ "a", "bb", "ccc" };
            break :blk arr[0][0];
        }) },
        .{ .src = &.{"blk: { const W = struct { rows: [2][]const u8 }; const w = W{ .rows = .{ \"xy\", \"z\" } }; break :blk w.rows[0][1]; }"}, .want = compliance.want(blk: {
            const W = struct { rows: [2][]const u8 };
            const w = W{ .rows = .{ "xy", "z" } };
            break :blk w.rows[0][1];
        }) },
    });
}

// Array/string/tuple concatenation via `++` (array_cat).
test "compliance: concatenation with ++" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const x = [_]i32{ 1, 2, 3 } ++ [_]i32{ 4, 5 }; break :blk x[3]; }"}, .want = compliance.want(blk: {
            const x = [_]i32{ 1, 2, 3 } ++ [_]i32{ 4, 5 };
            break :blk x[3];
        }) },
        .{ .src = &.{"blk: { const x = [_]i32{ 1, 2, 3 } ++ [_]i32{ 4, 5 }; break :blk x.len; }"}, .want = compliance.want(blk: {
            const x = [_]i32{ 1, 2, 3 } ++ [_]i32{ 4, 5 };
            break :blk x.len;
        }) },
        .{ .src = &.{"blk: { const s = \"ab\" ++ \"cd\"; break :blk s[3]; }"}, .want = compliance.want(blk: {
            const s = "ab" ++ "cd";
            break :blk s[3];
        }) },
        .{ .src = &.{"blk: { const s = \"ab\" ++ \"cd\"; break :blk s.len; }"}, .want = compliance.want(blk: {
            const s = "ab" ++ "cd";
            break :blk s.len;
        }) },
        .{ .src = &.{"blk: { const t = .{ 1, 2 } ++ .{3.5}; break :blk t[2]; }"}, .want = compliance.want(blk: {
            const t = .{ 1, 2 } ++ .{3.5};
            break :blk t[2];
        }) },
    });
}

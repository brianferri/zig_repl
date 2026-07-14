const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: string literals -- length and byte indexing" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const s = \"hello\"; break :blk s.len; }"}, .want = blk: {
            const s = "hello";
            break :blk s.len;
        } },
        .{ .src = &.{"blk: { break :blk \"hi\".len; }"}, .want = blk: {
            break :blk "hi".len;
        } },
        .{ .src = &.{"blk: { break :blk \"hi\"[0]; }"}, .want = blk: {
            break :blk "hi"[0];
        } },
        .{ .src = &.{"blk: { const s = \"abc\"; break :blk s[2]; }"}, .want = blk: {
            const s = "abc";
            break :blk s[2];
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30 }; break :blk arr.len; }"}, .want = blk: {
            const arr = [_]u8{ 10, 20, 30 };
            break :blk arr.len;
        } },
        .{ .src = &.{"blk: { break :blk \"hi\"[5]; }"}, .reject = {} },
    });
}

test "compliance: slices -- coercion from a string literal, .len, indexing" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const s: []const u8 = \"hello\"; break :blk s.len; }"}, .want = blk: {
            const s: []const u8 = "hello";
            break :blk s.len;
        } },
        .{ .src = &.{"blk: { const s: []const u8 = \"hello\"; break :blk s[1]; }"}, .want = blk: {
            const s: []const u8 = "hello";
            break :blk s[1];
        } },
        .{ .src = &.{"blk: { const E = enum { north, east }; const s: []const u8 = @tagName(E.east); break :blk s[0]; }"}, .want = blk: {
            const E = enum { north, east };
            const s: []const u8 = @tagName(E.east);
            break :blk s[0];
        } },
        .{ .src = &.{"blk: { const s: []const u8 = \"hi\"; break :blk s[5]; }"}, .reject = {} },
    });
}

test "compliance: address-of an array literal coerces to slice/many-ptr" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const s: []const u8 = &[_]u8{ 1, 2, 3 }; break :blk s[1]; }"}, .want = blk: {
            const s: []const u8 = &[_]u8{ 1, 2, 3 };
            break :blk s[1];
        } },
        .{ .src = &.{"blk: { const s: []const u8 = &[_]u8{ 1, 2, 3 }; break :blk s.len; }"}, .want = blk: {
            const s: []const u8 = &[_]u8{ 1, 2, 3 };
            break :blk s.len;
        } },
        .{ .src = &.{"blk: { const t: []const u32 = &[_]u32{ 10, 20, 30 }; break :blk t[2]; }"}, .want = blk: {
            const t: []const u32 = &[_]u32{ 10, 20, 30 };
            break :blk t[2];
        } },
        .{ .src = &.{"blk: { const m: [*]const u8 = &[_]u8{ 9, 8, 7 }; break :blk m[0]; }"}, .want = blk: {
            const m: [*]const u8 = &[_]u8{ 9, 8, 7 };
            break :blk m[0];
        } },
        .{ .src = &.{"blk: { const y: u32 = 5; const x: u32 = &y; break :blk x; }"}, .reject = {} },
        .{ .src = &.{ "const s: []const u8 = &[_]u8{ 1, 2, 3 };", "s[2]" }, .want = blk: {
            const s: []const u8 = &[_]u8{ 1, 2, 3 };
            break :blk s[2];
        } },
        .{ .src = &.{ "const m: [*]const u8 = &[_]u8{ 9, 8 };", "m[1]" }, .want = blk: {
            const m: [*]const u8 = &[_]u8{ 9, 8 };
            break :blk m[1];
        } },
    });
}

test "compliance: indexing a const pointer built on an earlier line" {
    try compliance.check(a, .{
        .{ .src = &.{ "const s: []const u8 = \"abc\";", "s[0]" }, .want = blk: {
            const s: []const u8 = "abc";
            break :blk s[0];
        } },
        .{ .src = &.{ "const s: []const u8 = \"abc\";", "s.len" }, .want = blk: {
            const s: []const u8 = "abc";
            break :blk s.len;
        } },
        .{ .src = &.{ "const a = [_]u8{ 4, 5, 6 };", "const p = &a;", "p[0]" }, .want = blk: {
            const arr = [_]u8{ 4, 5, 6 };
            const p = &arr;
            break :blk p[0];
        } },
        .{ .src = &.{ "const arr = [_]u8{ 10, 20, 30, 40 };", "const s = arr[1..3];", "s[0]" }, .want = blk: {
            const arr = [_]u8{ 10, 20, 30, 40 };
            const s = arr[1..3];
            break :blk s[0];
        } },
    });
}

test "compliance: array element store" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { var arr = [_]u8{ 1, 2, 3 }; arr[1] = 9; break :blk arr[1]; }"}, .want = blk: {
            var arr = [_]u8{ 1, 2, 3 };
            arr[1] = 9;
            break :blk arr[1];
        } },
        .{ .src = &.{"blk: { var arr = [_]u8{ 1, 2, 3 }; arr[0] = 10; arr[2] = 30; break :blk arr[0] + arr[2]; }"}, .want = blk: {
            var arr = [_]u8{ 1, 2, 3 };
            arr[0] = 10;
            arr[2] = 30;
            break :blk arr[0] + arr[2];
        } },
        .{ .src = &.{"blk: { var arr = [_]u8{ 5, 6 }; const p = &arr[1]; p.* = 99; break :blk arr[1]; }"}, .want = blk: {
            var arr = [_]u8{ 5, 6 };
            const p = &arr[1];
            p.* = 99;
            break :blk arr[1];
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 1, 2 }; arr[0] = 5; break :blk arr[0]; }"}, .reject = {} },
    });
}

test "compliance: array slicing (a[start..end])" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s.len; }"}, .want = blk: {
            const arr = [_]u8{ 10, 20, 30, 40 };
            const s = arr[1..3];
            break :blk s.len;
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s[0]; }"}, .want = blk: {
            const arr = [_]u8{ 10, 20, 30, 40 };
            const s = arr[1..3];
            break :blk s[0];
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s[1]; }"}, .want = blk: {
            const arr = [_]u8{ 10, 20, 30, 40 };
            const s = arr[1..3];
            break :blk s[1];
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[0..4]; break :blk s[3]; }"}, .want = blk: {
            const arr = [_]u8{ 10, 20, 30, 40 };
            const s = arr[0..4];
            break :blk s[3];
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s[2]; }"}, .reject = {} },
        .{ .src = &.{"blk: { const arr = [_]u8{ 1, 2 }; const s = arr[0..9]; break :blk s.len; }"}, .reject = {} },
        .{ .src = &.{"blk: { const arr = [_]u8{ 1, 2, 3 }; const p = &arr.len; break :blk p.*; }"}, .want = blk: {
            const arr = [_]u8{ 1, 2, 3 };
            const p = &arr.len;
            break :blk p.*;
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30 }; const s = arr[0..2]; const p = &s.len; break :blk p.*; }"}, .want = blk: {
            const arr = [_]u8{ 10, 20, 30 };
            const s = arr[0..2];
            const p = &s.len;
            break :blk p.*;
        } },
    });
}

test "compliance: slicing a slice and a string literal" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const s: []const u8 = \"hello\"; const t = s[1..4]; break :blk t.len; }"}, .want = blk: {
            const s: []const u8 = "hello";
            const t = s[1..4];
            break :blk t.len;
        } },
        .{ .src = &.{"blk: { const s: []const u8 = \"hello\"; const t = s[1..4]; break :blk t[0] + t[2]; }"}, .want = blk: {
            const s: []const u8 = "hello";
            const t = s[1..4];
            break :blk t[0] + t[2];
        } },
        .{ .src = &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[0..3]; const t = s[1..3]; break :blk t[0] + t[1]; }"}, .want = blk: {
            const arr = [_]u8{ 10, 20, 30, 40 };
            const s = arr[0..3];
            const t = s[1..3];
            break :blk t[0] + t[1];
        } },
        .{ .src = &.{"\"hello\"[1..3].len"}, .want = "hello"[1..3].len },
        .{ .src = &.{"blk: { const s = \"hi\"; const t = s[0..1]; break :blk t[0]; }"}, .want = blk: {
            const s = "hi";
            const t = s[0..1];
            break :blk t[0];
        } },
        .{ .src = &.{"blk: { const s: []const u8 = \"hi\"; const t = s[0..5]; break :blk t[0]; }"}, .reject = {} },
    });
}

test "compliance: slicing an array pointer yields a pointer-to-array" {
    try compliance.check(a, .{
        .{ .src = &.{"(&[_]i32{ 1, 2, 3, 4, 5 })[2..].*"}, .want = (&[_]i32{ 1, 2, 3, 4, 5 })[2..].* },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3, 4, 5 })[0..].*"}, .want = (&[_]i32{ 1, 2, 3, 4, 5 })[0..].* },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3, 4, 5 })[1..3].*"}, .want = (&[_]i32{ 1, 2, 3, 4, 5 })[1..3].* },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3, 4, 5 })[1..3 :4].*"}, .want = (&[_]i32{ 1, 2, 3, 4, 5 })[1..3 :4].* },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3, 4, 5 })[1..][0..2].*"}, .want = (&[_]i32{ 1, 2, 3, 4, 5 })[1..][0..2].* },
        // A `[3]u8` value renders as a string, not `{any}`'s byte list.
        .{ .src = &.{"\"hello\"[1..4].*"}, .rendered = "\"ell\".*" },
        .{ .src = &.{"blk: { const s: []const i32 = &.{ 1, 2, 3, 4 }; break :blk s[1..3].*; }"}, .want = blk: {
            const s: []const i32 = &.{ 1, 2, 3, 4 };
            break :blk s[1..3].*;
        } },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3, 4, 5 })[1..4][1]"}, .want = (&[_]i32{ 1, 2, 3, 4, 5 })[1..4][1] },
        .{ .src = &.{"(&[_:0]i32{ 1, 2, 3 })[1..].*"}, .want = (&[_:0]i32{ 1, 2, 3 })[1..].* },
        .{ .src = &.{"@TypeOf((&[_]i32{ 1, 2, 3 })[0..2])"}, .want = @TypeOf((&[_]i32{ 1, 2, 3 })[0..2]) },
    });
}

test "compliance: storing through a pointer-to-array writes the sub-array range" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { var d = [_]u8{ 1, 2, 3, 4 }; d[1..3].* = .{ 8, 9 }; break :blk d[0] + d[1] + d[2] + d[3]; }"}, .want = blk: {
            var d = [_]u8{ 1, 2, 3, 4 };
            d[1..3].* = .{ 8, 9 };
            break :blk d[0] + d[1] + d[2] + d[3];
        } },
        .{ .src = &.{"blk: { var d = [_]u8{ 1, 2, 3, 4 }; d[1..3].* = .{ 8, 9, 10 }; break :blk d[1]; }"}, .reject = {} },
    });
}

test "compliance: out-of-bounds and mismatched-sentinel slices are rejected" {
    try compliance.check(a, .{
        .{ .src = &.{"(&[_]i32{ 1, 2, 3 })[1..5].*"}, .reject = {} },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3 })[2..1].*"}, .reject = {} },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3, 4, 5 })[1..3 :9].*"}, .reject = {} },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3 })[5..].*"}, .reject = {} },
        .{ .src = &.{"(&[_]i32{ 1, 2, 3 })[1..][0..5].*"}, .reject = {} },
        .{ .src = &.{"blk: { var x: i32 = 5; _ = &x; const p: *i32 = &x; break :blk p[0..1 :0]; }"}, .reject = {} },
    });
}

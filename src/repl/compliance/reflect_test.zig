const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @field reads a field by comptime-string name" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; break :blk @field(s, \"x\"); }"},
            .want = blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                break :blk @field(s, "x");
            },
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; break :blk @field(s, \"x\") + @field(s, \"y\"); }"},
            .want = blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                break :blk @field(s, "x") + @field(s, "y");
            },
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; const u = U{ .a = 5 }; break :blk @field(u, \"a\"); }"},
            .want = blk: {
                const U = union(enum) { a: u8, b: bool };
                const u = U{ .a = 5 };
                break :blk @field(u, "a");
            },
        },
        .{
            .src = &.{"blk: { const E = enum { north, south }; break :blk @field(E, \"south\") == E.south; }"},
            .want = blk: {
                const E = enum { north, south };
                break :blk @field(E, "south") == E.south;
            },
        },
        .{
            .src = &.{"blk: { const s: []const u8 = \"hello\"; break :blk @field(s, \"len\"); }"},
            .want = blk: {
                const s: []const u8 = "hello";
                break :blk @field(s, "len");
            },
        },
        .{
            .src = &.{"blk: { const arr = [_]u8{ 1, 2, 3, 4 }; break :blk @field(arr, \"len\"); }"},
            .want = blk: {
                const arr = [_]u8{ 1, 2, 3, 4 };
                break :blk @field(arr, "len");
            },
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; const p = &@field(s, \"x\"); break :blk p.*; }"},
            .want = blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                const p = &@field(s, "x");
                break :blk p.*;
            },
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; var s = S{ .x = 1, .y = 2 }; @field(s, \"x\") = 9; break :blk s.x; }"},
            .want = blk: {
                const S = struct { x: u32, y: u8 };
                var s = S{ .x = 1, .y = 2 };
                @field(s, "x") = 9;
                break :blk s.x;
            },
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; const n: []const u8 = \"x\"; break :blk @field(s, n); }"},
            .want = blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                const n: []const u8 = "x";
                break :blk @field(s, n);
            },
        },
        .{
            .src = &.{"blk: { const N = struct { inner: struct { x: u8 } }; const s = N{ .inner = .{ .x = 3 } }; break :blk @field(@field(s, \"inner\"), \"x\"); }"},
            .want = blk: {
                const N = struct { inner: struct { x: u8 } };
                const s = N{ .inner = .{ .x = 3 } };
                break :blk @field(@field(s, "inner"), "x");
            },
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 1, .y = 2 }; break :blk @field(s, \"z\"); }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; const u = U{ .a = 5 }; break :blk @field(u, \"b\"); }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const n: u32 = 5; break :blk @field(n, \"x\"); }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 1, .y = 2 }; @field(s, \"x\") = 9; break :blk s.x; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 1, .y = 2 }; break :blk @field(s, 5); }"},
            .reject = {},
        },
    });
}

test "compliance: @hasField and @hasDecl" {
    @setEvalBranchQuota(20_000); // many cases, each comptime-rendering its want
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: bool }; break :blk @hasField(S, \"x\"); }"},
            .want = blk: {
                const S = struct { x: u32, y: bool };
                break :blk @hasField(S, "x");
            },
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: bool }; break :blk @hasField(S, \"z\"); }"},
            .want = blk: {
                const S = struct { x: u32, y: bool };
                break :blk @hasField(S, "z");
            },
        },
        .{
            .src = &.{"blk: { const U = union { a: u8, b: bool }; break :blk @hasField(U, \"b\"); }"},
            .want = blk: {
                const U = union { a: u8, b: bool };
                break :blk @hasField(U, "b");
            },
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; break :blk @hasField(U, \"c\"); }"},
            .want = blk: {
                const U = union(enum) { a: u8, b: bool };
                break :blk @hasField(U, "c");
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b }; break :blk @hasField(E, \"a\"); }"},
            .want = blk: {
                const E = enum { a, b };
                break :blk @hasField(E, "a");
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b }; break :blk @hasField(E, \"c\"); }"},
            .want = blk: {
                const E = enum { a, b };
                break :blk @hasField(E, "c");
            },
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"1\"); }"},
            .want = blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "1");
            },
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"2\"); }"},
            .want = blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "2");
            },
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"a\"); }"},
            .want = blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "a");
            },
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"01\"); }"},
            .want = blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "01");
            },
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"1_0\"); }"},
            .want = blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "1_0");
            },
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"9999999999999999999999999\"); }"},
            .want = blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "9999999999999999999999999");
            },
        },
        .{
            .src = &.{"blk: { const S = struct { a: i32, pub const nope = 1; }; break :blk @hasField(S, \"nope\"); }"},
            .want = blk: {
                const S = struct {
                    a: i32,
                    pub const nope = 1;
                };
                break :blk @hasField(S, "nope");
            },
        },
        .{
            .src = &.{"blk: { const U = union { a: u64, pub const nope = 1; }; break :blk @hasField(U, \"nope\"); }"},
            .want = blk: {
                const U = union {
                    a: u64,
                    pub const nope = 1;
                };
                break :blk @hasField(U, "nope");
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, pub const nope = 1; }; break :blk @hasField(E, \"nope\"); }"},
            .want = blk: {
                const E = enum {
                    a,
                    pub const nope = 1;
                };
                break :blk @hasField(E, "nope");
            },
        },
        .{
            .src = &.{"blk: { const S = struct { xx: u8 }; const n: []const u8 = \"xx\"; break :blk @hasField(S, n); }"},
            .want = blk: {
                const S = struct { xx: u8 };
                const n: []const u8 = "xx";
                break :blk @hasField(S, n);
            },
        },
        .{
            .src = &.{"@hasField([3]u8, \"len\")"},
            .want = @hasField([3]u8, "len"),
        },
        .{
            .src = &.{"@hasField([3]u8, \"ptr\")"},
            .want = @hasField([3]u8, "ptr"),
        },
        .{
            .src = &.{"@hasField([]const u8, \"ptr\")"},
            .want = @hasField([]const u8, "ptr"),
        },
        .{
            .src = &.{"@hasField([]const u8, \"len\")"},
            .want = @hasField([]const u8, "len"),
        },
        .{
            .src = &.{"blk: { const T = struct { x: u8, const K = 9; }; break :blk @hasDecl(T, \"K\"); }"},
            .want = blk: {
                const T = struct {
                    x: u8,
                    const K = 9;
                };
                break :blk @hasDecl(T, "K");
            },
        },
        .{
            .src = &.{"blk: { const T = struct { x: u8, const K = 9; }; break :blk @hasDecl(T, \"x\"); }"},
            .want = blk: {
                const T = struct {
                    x: u8,
                    const K = 9;
                };
                break :blk @hasDecl(T, "x");
            },
        },
        .{
            .src = &.{"blk: { const T = struct { fn f() void {} }; break :blk @hasDecl(T, \"f\"); }"},
            .want = blk: {
                const T = struct {
                    fn f() void {}
                };
                break :blk @hasDecl(T, "f");
            },
        },
        .{
            .src = &.{"blk: { const T = struct { fn f() void {} }; break :blk @hasDecl(T, \"g\"); }"},
            .want = blk: {
                const T = struct {
                    fn f() void {}
                };
                break :blk @hasDecl(T, "g");
            },
        },
        .{
            .src = &.{"blk: { const B = struct { nope: i32, const hi = 1; }; break :blk @hasDecl(B, \"hi\"); }"},
            .want = blk: {
                const B = struct {
                    nope: i32,
                    const hi = 1;
                };
                break :blk @hasDecl(B, "hi");
            },
        },
        .{
            .src = &.{"blk: { const B = struct { nope: i32, pub var blah = 3; }; break :blk @hasDecl(B, \"blah\"); }"},
            .want = blk: {
                const B = struct {
                    nope: i32,
                    pub var blah = 3;
                };
                break :blk @hasDecl(B, "blah");
            },
        },
        .{
            .src = &.{"blk: { const B = struct { nope: i32, const hi = 1; }; break :blk @hasDecl(B, \"nope\"); }"},
            .want = blk: {
                const B = struct {
                    nope: i32,
                    const hi = 1;
                };
                break :blk @hasDecl(B, "nope");
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, const N = 2; }; break :blk @hasDecl(E, \"N\"); }"},
            .want = blk: {
                const E = enum {
                    a,
                    const N = 2;
                };
                break :blk @hasDecl(E, "N");
            },
        },
        .{
            .src = &.{"blk: { const T = struct { const K = 9; }; const n: []const u8 = \"K\"; break :blk @hasDecl(T, n); }"},
            .want = blk: {
                const T = struct {
                    const K = 9;
                };
                const n: []const u8 = "K";
                break :blk @hasDecl(T, n);
            },
        },
        .{
            .src = &.{"blk: { const O = struct { const I = struct { const K = 7; }; }; break :blk @hasDecl(O.I, \"K\"); }"},
            .want = blk: {
                const O = struct {
                    const I = struct {
                        const K = 7;
                    };
                };
                break :blk @hasDecl(O.I, "K");
            },
        },
        .{
            .src = &.{"blk: { const O = struct { const I = struct {}; }; break :blk @hasDecl(O, \"I\"); }"},
            .want = blk: {
                const O = struct {
                    const I = struct {};
                };
                break :blk @hasDecl(O, "I");
            },
        },
        .{
            .src = &.{"@hasField(u32, \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasField(*u32, \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasField(?u32, \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasField(@Vector(4, i32), \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasField(void, \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasDecl(u32, \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasDecl(bool, \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasDecl([3]u8, \"x\")"},
            .reject = {},
        },
        .{
            .src = &.{"@hasDecl(?u32, \"x\")"},
            .reject = {},
        },
    });
}

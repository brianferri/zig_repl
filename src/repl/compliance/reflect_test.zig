const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @field reads a field by comptime-string name" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; break :blk @field(s, \"x\"); }"},
            .want = compliance.want(blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                break :blk @field(s, "x");
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; break :blk @field(s, \"x\") + @field(s, \"y\"); }"},
            .want = compliance.want(blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                break :blk @field(s, "x") + @field(s, "y");
            }),
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; const u = U{ .a = 5 }; break :blk @field(u, \"a\"); }"},
            .want = compliance.want(blk: {
                const U = union(enum) { a: u8, b: bool };
                const u = U{ .a = 5 };
                break :blk @field(u, "a");
            }),
        },
        .{
            .src = &.{"blk: { const E = enum { north, south }; break :blk @field(E, \"south\") == E.south; }"},
            .want = compliance.want(blk: {
                const E = enum { north, south };
                break :blk @field(E, "south") == E.south;
            }),
        },
        .{
            .src = &.{"blk: { const s: []const u8 = \"hello\"; break :blk @field(s, \"len\"); }"},
            .want = compliance.want(blk: {
                const s: []const u8 = "hello";
                break :blk @field(s, "len");
            }),
        },
        .{
            .src = &.{"blk: { const arr = [_]u8{ 1, 2, 3, 4 }; break :blk @field(arr, \"len\"); }"},
            .want = compliance.want(blk: {
                const arr = [_]u8{ 1, 2, 3, 4 };
                break :blk @field(arr, "len");
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; const p = &@field(s, \"x\"); break :blk p.*; }"},
            .want = compliance.want(blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                const p = &@field(s, "x");
                break :blk p.*;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; var s = S{ .x = 1, .y = 2 }; @field(s, \"x\") = 9; break :blk s.x; }"},
            .want = compliance.want(blk: {
                const S = struct { x: u32, y: u8 };
                var s = S{ .x = 1, .y = 2 };
                @field(s, "x") = 9;
                break :blk s.x;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 7, .y = 3 }; const n: []const u8 = \"x\"; break :blk @field(s, n); }"},
            .want = compliance.want(blk: {
                const S = struct { x: u32, y: u8 };
                const s = S{ .x = 7, .y = 3 };
                const n: []const u8 = "x";
                break :blk @field(s, n);
            }),
        },
        .{
            .src = &.{"blk: { const N = struct { inner: struct { x: u8 } }; const s = N{ .inner = .{ .x = 3 } }; break :blk @field(@field(s, \"inner\"), \"x\"); }"},
            .want = compliance.want(blk: {
                const N = struct { inner: struct { x: u8 } };
                const s = N{ .inner = .{ .x = 3 } };
                break :blk @field(@field(s, "inner"), "x");
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 1, .y = 2 }; break :blk @field(s, \"z\"); }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; const u = U{ .a = 5 }; break :blk @field(u, \"b\"); }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const n: u32 = 5; break :blk @field(n, \"x\"); }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 1, .y = 2 }; @field(s, \"x\") = 9; break :blk s.x; }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: u8 }; const s = S{ .x = 1, .y = 2 }; break :blk @field(s, 5); }"},
            .reject = true,
        },
    });
}

test "compliance: @hasField and @hasDecl" {
    @setEvalBranchQuota(20_000); // many cases, each comptime-rendering its want
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: bool }; break :blk @hasField(S, \"x\"); }"},
            .want = compliance.want(blk: {
                const S = struct { x: u32, y: bool };
                break :blk @hasField(S, "x");
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { x: u32, y: bool }; break :blk @hasField(S, \"z\"); }"},
            .want = compliance.want(blk: {
                const S = struct { x: u32, y: bool };
                break :blk @hasField(S, "z");
            }),
        },
        .{
            .src = &.{"blk: { const U = union { a: u8, b: bool }; break :blk @hasField(U, \"b\"); }"},
            .want = compliance.want(blk: {
                const U = union { a: u8, b: bool };
                break :blk @hasField(U, "b");
            }),
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; break :blk @hasField(U, \"c\"); }"},
            .want = compliance.want(blk: {
                const U = union(enum) { a: u8, b: bool };
                break :blk @hasField(U, "c");
            }),
        },
        .{
            .src = &.{"blk: { const E = enum { a, b }; break :blk @hasField(E, \"a\"); }"},
            .want = compliance.want(blk: {
                const E = enum { a, b };
                break :blk @hasField(E, "a");
            }),
        },
        .{
            .src = &.{"blk: { const E = enum { a, b }; break :blk @hasField(E, \"c\"); }"},
            .want = compliance.want(blk: {
                const E = enum { a, b };
                break :blk @hasField(E, "c");
            }),
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"1\"); }"},
            .want = compliance.want(blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "1");
            }),
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"2\"); }"},
            .want = compliance.want(blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "2");
            }),
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"a\"); }"},
            .want = compliance.want(blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "a");
            }),
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"01\"); }"},
            .want = compliance.want(blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "01");
            }),
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"1_0\"); }"},
            .want = compliance.want(blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "1_0");
            }),
        },
        .{
            .src = &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"9999999999999999999999999\"); }"},
            .want = compliance.want(blk: {
                const Tup = struct { u32, u8 };
                break :blk @hasField(Tup, "9999999999999999999999999");
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { a: i32, pub const nope = 1; }; break :blk @hasField(S, \"nope\"); }"},
            .want = compliance.want(blk: {
                const S = struct {
                    a: i32,
                    pub const nope = 1;
                };
                break :blk @hasField(S, "nope");
            }),
        },
        .{
            .src = &.{"blk: { const U = union { a: u64, pub const nope = 1; }; break :blk @hasField(U, \"nope\"); }"},
            .want = compliance.want(blk: {
                const U = union {
                    a: u64,
                    pub const nope = 1;
                };
                break :blk @hasField(U, "nope");
            }),
        },
        .{
            .src = &.{"blk: { const E = enum { a, pub const nope = 1; }; break :blk @hasField(E, \"nope\"); }"},
            .want = compliance.want(blk: {
                const E = enum {
                    a,
                    pub const nope = 1;
                };
                break :blk @hasField(E, "nope");
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { xx: u8 }; const n: []const u8 = \"xx\"; break :blk @hasField(S, n); }"},
            .want = compliance.want(blk: {
                const S = struct { xx: u8 };
                const n: []const u8 = "xx";
                break :blk @hasField(S, n);
            }),
        },
        .{
            .src = &.{"@hasField([3]u8, \"len\")"},
            .want = compliance.want(@hasField([3]u8, "len")),
        },
        .{
            .src = &.{"@hasField([3]u8, \"ptr\")"},
            .want = compliance.want(@hasField([3]u8, "ptr")),
        },
        .{
            .src = &.{"@hasField([]const u8, \"ptr\")"},
            .want = compliance.want(@hasField([]const u8, "ptr")),
        },
        .{
            .src = &.{"@hasField([]const u8, \"len\")"},
            .want = compliance.want(@hasField([]const u8, "len")),
        },
        .{
            .src = &.{"blk: { const T = struct { x: u8, const K = 9; }; break :blk @hasDecl(T, \"K\"); }"},
            .want = compliance.want(blk: {
                const T = struct {
                    x: u8,
                    const K = 9;
                };
                break :blk @hasDecl(T, "K");
            }),
        },
        .{
            .src = &.{"blk: { const T = struct { x: u8, const K = 9; }; break :blk @hasDecl(T, \"x\"); }"},
            .want = compliance.want(blk: {
                const T = struct {
                    x: u8,
                    const K = 9;
                };
                break :blk @hasDecl(T, "x");
            }),
        },
        .{
            .src = &.{"blk: { const T = struct { fn f() void {} }; break :blk @hasDecl(T, \"f\"); }"},
            .want = compliance.want(blk: {
                const T = struct {
                    fn f() void {}
                };
                break :blk @hasDecl(T, "f");
            }),
        },
        .{
            .src = &.{"blk: { const T = struct { fn f() void {} }; break :blk @hasDecl(T, \"g\"); }"},
            .want = compliance.want(blk: {
                const T = struct {
                    fn f() void {}
                };
                break :blk @hasDecl(T, "g");
            }),
        },
        .{
            .src = &.{"blk: { const B = struct { nope: i32, const hi = 1; }; break :blk @hasDecl(B, \"hi\"); }"},
            .want = compliance.want(blk: {
                const B = struct {
                    nope: i32,
                    const hi = 1;
                };
                break :blk @hasDecl(B, "hi");
            }),
        },
        .{
            .src = &.{"blk: { const B = struct { nope: i32, pub var blah = 3; }; break :blk @hasDecl(B, \"blah\"); }"},
            .want = compliance.want(blk: {
                const B = struct {
                    nope: i32,
                    pub var blah = 3;
                };
                break :blk @hasDecl(B, "blah");
            }),
        },
        .{
            .src = &.{"blk: { const B = struct { nope: i32, const hi = 1; }; break :blk @hasDecl(B, \"nope\"); }"},
            .want = compliance.want(blk: {
                const B = struct {
                    nope: i32,
                    const hi = 1;
                };
                break :blk @hasDecl(B, "nope");
            }),
        },
        .{
            .src = &.{"blk: { const E = enum { a, const N = 2; }; break :blk @hasDecl(E, \"N\"); }"},
            .want = compliance.want(blk: {
                const E = enum {
                    a,
                    const N = 2;
                };
                break :blk @hasDecl(E, "N");
            }),
        },
        .{
            .src = &.{"blk: { const T = struct { const K = 9; }; const n: []const u8 = \"K\"; break :blk @hasDecl(T, n); }"},
            .want = compliance.want(blk: {
                const T = struct {
                    const K = 9;
                };
                const n: []const u8 = "K";
                break :blk @hasDecl(T, n);
            }),
        },
        .{
            .src = &.{"blk: { const O = struct { const I = struct { const K = 7; }; }; break :blk @hasDecl(O.I, \"K\"); }"},
            .want = compliance.want(blk: {
                const O = struct {
                    const I = struct {
                        const K = 7;
                    };
                };
                break :blk @hasDecl(O.I, "K");
            }),
        },
        .{
            .src = &.{"blk: { const O = struct { const I = struct {}; }; break :blk @hasDecl(O, \"I\"); }"},
            .want = compliance.want(blk: {
                const O = struct {
                    const I = struct {};
                };
                break :blk @hasDecl(O, "I");
            }),
        },
        .{
            .src = &.{"@hasField(u32, \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasField(*u32, \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasField(?u32, \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasField(@Vector(4, i32), \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasField(void, \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasDecl(u32, \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasDecl(bool, \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasDecl([3]u8, \"x\")"},
            .reject = true,
        },
        .{
            .src = &.{"@hasDecl(?u32, \"x\")"},
            .reject = true,
        },
    });
}

test "compliance: @typeInfo reads type structure" {
    @setEvalBranchQuota(20_000); // many cases, each comptime-rendering its want
    try compliance.check(a, &.{
        .{ .src = &.{"@typeInfo(u8).int.bits"}, .want = compliance.want(@typeInfo(u8).int.bits) },
        .{ .src = &.{"@typeInfo(i64).int.signedness == .signed"}, .want = compliance.want(@typeInfo(i64).int.signedness == .signed) },
        .{ .src = &.{"@typeInfo([4]u32).array.len"}, .want = compliance.want(@typeInfo([4]u32).array.len) },
        .{ .src = &.{"@typeInfo([4]u32).array.child == u32"}, .want = compliance.want(@typeInfo([4]u32).array.child == u32) },
        .{ .src = &.{"@typeInfo(*const u8).pointer.attrs.@\"const\""}, .want = compliance.want(@typeInfo(*const u8).pointer.attrs.@"const") },
        .{ .src = &.{"@typeInfo(?u8).optional.child == u8"}, .want = compliance.want(@typeInfo(?u8).optional.child == u8) },
        .{ .src = &.{"@typeInfo(fn (u8, u16) u8).@\"fn\".param_types.len"}, .want = compliance.want(@typeInfo(fn (u8, u16) u8).@"fn".param_types.len) },
        .{ .src = &.{"@typeInfo(fn (u8) u8).@\"fn\".return_type.? == u8"}, .want = compliance.want(@typeInfo(fn (u8) u8).@"fn".return_type.? == u8) },
        .{ .src = &.{"@typeInfo(enum { a, b, c }).@\"enum\".field_names.len"}, .want = compliance.want(@typeInfo(enum { a, b, c }).@"enum".field_names.len) },
        .{ .src = &.{"@typeInfo(struct { x: u8, y: u16 }).@\"struct\".field_names.len"}, .want = compliance.want(@typeInfo(struct { x: u8, y: u16 }).@"struct".field_names.len) },
    });
}

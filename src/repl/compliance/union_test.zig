const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @unionInit builds the union with the named field active" {
    try compliance.check(a, .{
        .{
            .src = &.{"@unionInit(union { a: u8, b: bool }, \"a\", @as(u8, 5)).a"},
            .want = @unionInit(union { a: u8, b: bool }, "a", @as(u8, 5)).a,
        },
        .{
            .src = &.{"@unionInit(union { a: u8, b: bool }, \"b\", true).b"},
            .want = @unionInit(union { a: u8, b: bool }, "b", true).b,
        },
        .{
            .src = &.{"@unionInit(union { a: u8 }, \"z\", @as(u8, 1)).a"},
            .reject = {},
        },
    });
}

test "compliance: @tagName of a tagged union names the active field" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = union(enum) { a: u32, b: bool }; const e = E{ .b = true }; break :blk @tagName(e)[0]; }"},
            .want = blk: {
                const E = union(enum) { a: u32, b: bool };
                const e = E{ .b = true };
                break :blk @tagName(e)[0];
            },
        },
        .{
            .src = &.{"blk: { const E = union(enum) { a: u32, b: bool }; const e = E{ .a = 9 }; const c: u8 = @tagName(e)[0]; break :blk c; }"},
            .want = blk: {
                const E = union(enum) { a: u32, b: bool };
                const e = E{ .a = 9 };
                const c: u8 = @tagName(e)[0];
                break :blk c;
            },
        },
        .{
            .src = &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .a = 5 }; break :blk @tagName(u)[0]; }"},
            .reject = {},
        },
    });
    try compliance.expectDiagnostic(a, &.{ "const U = union { a: u32 };", "const u = U{ .a = 5 };", "@tagName(u)" }, "is untagged");
}

test "compliance: switch on a tagged union captures the active payload" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = union(enum) { a: u32, b: u8 }; const e = E{ .a = 5 }; break :blk switch (e) { .a => |v| v, .b => 0 }; }"},
            .want = blk: {
                const E = union(enum) { a: u32, b: u8 };
                const e = E{ .a = 5 };
                break :blk switch (e) {
                    .a => |v| v,
                    .b => 0,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = union(enum) { a: u32, b: u8 }; const e = E{ .b = 7 }; break :blk switch (e) { .a => |v| v, .b => |v| v + 1 }; }"},
            .want = blk: {
                const E = union(enum) { a: u32, b: u8 };
                const e = E{ .b = 7 };
                break :blk switch (e) {
                    .a => |v| v,
                    .b => |v| v + 1,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = union(enum) { a: u32, b: u8 }; const e = E{ .a = 42 }; break :blk switch (e) { .a => |*v| v.*, .b => 0 }; }"},
            .want = blk: {
                const E = union(enum) { a: u32, b: u8 };
                const e = E{ .a = 42 };
                break :blk switch (e) {
                    .a => |*v| v.*,
                    .b => 0,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = union(enum) { a: u32, b: u8 }; const e = E{ .b = 7 }; break :blk switch (e) { .a => |v| v, .b => 100 }; }"},
            .want = blk: {
                const E = union(enum) { a: u32, b: u8 };
                const e = E{ .b = 7 };
                break :blk switch (e) {
                    .a => |v| v,
                    .b => 100,
                };
            },
        },
        .{
            .src = &.{"blk: { const V = union(enum) { a: u32, b: u8, c: u8 }; const v = V{ .c = 3 }; break :blk switch (v) { .a => |x| x, else => 99 }; }"},
            .want = blk: {
                const V = union(enum) { a: u32, b: u8, c: u8 };
                const v = V{ .c = 3 };
                break :blk switch (v) {
                    .a => |x| x,
                    else => 99,
                };
            },
        },
        .{
            .src = &.{"blk: { const V = union(enum) { a: u8, b: u8, c: u8 }; const v = V{ .b = 7 }; break :blk switch (v) { .a, .b => |x| x, .c => 0 }; }"},
            .want = blk: {
                const V = union(enum) { a: u8, b: u8, c: u8 };
                const v = V{ .b = 7 };
                break :blk switch (v) {
                    .a, .b => |x| x,
                    .c => 0,
                };
            },
        },
        .{
            .src = &.{"blk: { const U = union { a: u32, b: u8 }; const u = U{ .a = 5 }; break :blk switch (u) { .a => |v| v, .b => 0 }; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const V = union(enum) { a: u32, b: bool }; const v = V{ .a = 5 }; break :blk switch (v) { .a, .b => |x| x }; }"},
            .reject = {},
        },
    });
}

test "compliance: unions with explicit tag types" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const T = union(enum(u8)) { a: u32, b: u8 }; const t = T{ .b = 7 }; break :blk switch (t) { .a => |v| v, .b => |v| v + 1 }; }"},
            .want = blk: {
                const T = union(enum(u8)) { a: u32, b: u8 };
                const t = T{ .b = 7 };
                break :blk switch (t) {
                    .a => |v| v,
                    .b => |v| v + 1,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b = 10 }; const U = union(E) { a: u32, b: u8 }; const u = U{ .b = 9 }; break :blk u.b; }"},
            .want = blk: {
                const E = enum(u8) { a = 5, b = 10 };
                const U = union(E) { a: u32, b: u8 };
                const u = U{ .b = 9 };
                break :blk u.b;
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b = 10 }; const U = union(E) { a: u32, b: u8 }; const u = U{ .a = 3 }; break :blk switch (u) { .a => |v| v, .b => 0 }; }"},
            .want = blk: {
                const E = enum(u8) { a = 5, b = 10 };
                const U = union(E) { a: u32, b: u8 };
                const u = U{ .a = 3 };
                break :blk switch (u) {
                    .a => |v| v,
                    .b => 0,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b = 10 }; const U = union(E) { a: u32, b: u8 }; const u = U{ .b = 9 }; const c: u8 = @tagName(u)[0]; break :blk c; }"},
            .want = blk: {
                const E = enum(u8) { a = 5, b = 10 };
                const U = union(E) { a: u32, b: u8 };
                const u = U{ .b = 9 };
                const c: u8 = @tagName(u)[0];
                break :blk c;
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b = 10 }; const U = union(E) { a: u32, b: u8 }; const u = U{ .b = 9 }; break :blk u.a; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const U = union(u8) { a: u32, b: u8 }; const u = U{ .a = 5 }; break :blk u.a; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const E = enum { a, b }; const U = union(E) { a: u32, x: u8 }; const u = U{ .x = 1 }; break :blk u.x; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const E = enum { a, b }; const U = union(E) { b: bool, a: u32 }; const u = U{ .a = 5 }; break :blk u.a; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const U = union(E) { a: u32, b: u8 }; const u = U{ .a = 5 }; break :blk u.a; }"},
            .reject = {},
        },
    });
}

test "compliance: union sad paths pin the REPL's diagnostics" {
    const U = "const U = union(enum) { a: u32, b: u8 };";
    try compliance.expectDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .z = 1 }; break :blk u.a; }"}, "no field named 'z' in union");
    try compliance.expectDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 1 }; break :blk u.z; }"}, "no field named 'z' in union");
    try compliance.expectDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 1 }; break :blk u.z; }"}, "union declared here");
    try compliance.expectDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 1, .b = 2 }; break :blk u.a; }"}, "union initialization expects exactly one field");
    try compliance.expectDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .a = true }; break :blk u.a; }"}, "cannot coerce value to destination type");
    try compliance.expectDiagnostic(a, &.{"blk: { const S = struct { x: u8 }; const s = S{ .x = 1 }; break :blk @tagName(s); }"}, "expected enum or union");
    try compliance.expectDiagnostic(a, &.{"blk: { const V = union(u8) { a: u32, b: u8 }; const v = V{ .a = 1 }; break :blk v.a; }"}, "expected enum tag type, found 'u8'");
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b }; const V = union(E) { b: bool, a: u32 }; const v = V{ .a = 1 }; break :blk v.a; }"}, "union field order does not match tag enum field order");
}

test "compliance: union initialization and active-field access" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .a = 5 }; break :blk u.a; }"},
            .want = blk: {
                const U = union { a: u32, b: bool };
                const u = U{ .a = 5 };
                break :blk u.a;
            },
        },
        .{
            .src = &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .b = true }; break :blk u.b; }"},
            .want = blk: {
                const U = union { a: u32, b: bool };
                const u = U{ .b = true };
                break :blk u.b;
            },
        },
        .{
            .src = &.{"blk: { const W = struct { x: u8, y: u8 }; const V = union { p: W, n: u8 }; const v = V{ .p = W{ .x = 3, .y = 4 } }; break :blk v.p.x + v.p.y; }"},
            .want = blk: {
                const W = struct { x: u8, y: u8 };
                const V = union { p: W, n: u8 };
                const v = V{ .p = W{ .x = 3, .y = 4 } };
                break :blk v.p.x + v.p.y;
            },
        },
        .{
            .src = &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .a = 5 }; break :blk u.b; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .a = 5 }; const q = &u.b; _ = q; break :blk 0; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .a = 5, .b = true }; break :blk u.a; }"},
            .reject = {},
        },
    });
    try compliance.expectDiagnostic(
        a,
        &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .a = 5 }; break :blk u.b; }"},
        "access of union field 'b' while field 'a' is active",
    );
}

test "compliance: union member declarations and decl literals" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool, pub const zero = @This(){ .a = 0 }; }; break :blk U.zero.a; }"},
            .want = blk: {
                const U = union(enum) {
                    a: u8,
                    b: bool,
                    pub const zero = @This(){ .a = 0 };
                };
                break :blk U.zero.a;
            },
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool, pub const zero = @This(){ .a = 0 }; }; const x: U = .zero; break :blk x.a; }"},
            .want = blk: {
                const U = union(enum) {
                    a: u8,
                    b: bool,
                    pub const zero = @This(){ .a = 0 };
                };
                const x: U = .zero;
                break :blk x.a;
            },
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; const t = U{ .a = 1 }; break :blk t == .a; }"},
            .want = blk: {
                const U = union(enum) { a: u8, b: bool };
                const t = U{ .a = 1 };
                break :blk t == .a;
            },
        },
        .{
            .src = &.{"blk: { const U = union(enum) { a: u8, b: bool }; const t = U{ .a = 1 }; break :blk t == .b; }"},
            .want = blk: {
                const U = union(enum) { a: u8, b: bool };
                const t = U{ .a = 1 };
                break :blk t == .b;
            },
        },
        .{
            .src = &.{"blk: { const B = union { a: u8, b: bool }; const u = B{ .a = 1 }; break :blk u == .a; }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const N = union(enum) { a: u8, b: noreturn }; const u = N{ .a = 1 }; break :blk u == .b; }"},
            .want = blk: {
                const N = union(enum) { a: u8, b: noreturn };
                const u = N{ .a = 1 };
                break :blk u == .b;
            },
        },
        .{
            .src = &.{"blk: { const N = union(enum) { a: u8, b: noreturn }; const u = N{ .a = 1 }; break :blk u == .a; }"},
            .want = blk: {
                const N = union(enum) { a: u8, b: noreturn };
                const u = N{ .a = 1 };
                break :blk u == .a;
            },
        },
        .{
            .src = &.{"blk: { const NS = union(enum) { a: u8, b: struct { x: noreturn } }; const u = NS{ .a = 1 }; break :blk u == .b; }"},
            .want = blk: {
                const NS = union(enum) { a: u8, b: struct { x: noreturn } };
                const u = NS{ .a = 1 };
                break :blk u == .b;
            },
        },
        .{
            .src = &.{"blk: { const NO = union(enum) { a: u8, b: ?noreturn }; const u = NO{ .b = null }; break :blk u == .b; }"},
            .want = blk: {
                const NO = union(enum) { a: u8, b: ?noreturn };
                const u = NO{ .b = null };
                break :blk u == .b;
            },
        },
        // Reading a field of an undefined union cannot determine the active field: use-of-undef, not a crash.
        .{ .src = &.{"blk: { const U = union(enum) { a: u32, b: u32 }; const u: U = undefined; break :blk u.a; }"}, .reject = {} },
    });
}

// A packed union stores its value as a backing-integer bitpack; any field reads reinterpret the
// bits (no active-tag check), like a packed struct field.
test "compliance: a packed union field reinterprets the backing bits" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const U = packed union { x: u8, y: i8 }; const u = U{ .x = 200 }; break :blk u.x; }"}, .want = blk: {
            const U = packed union { x: u8, y: i8 };
            const u = U{ .x = 200 };
            break :blk u.x;
        } },
        .{ .src = &.{"blk: { const U = packed union { x: u8, y: i8 }; const u = U{ .x = 200 }; break :blk u.y; }"}, .want = blk: {
            const U = packed union { x: u8, y: i8 };
            const u = U{ .x = 200 };
            break :blk u.y;
        } },
        // All fields of a packed union must share one bit width.
        .{ .src = &.{"blk: { const U = packed union { a: u8, b: u4 }; const u = U{ .a = 1 }; break :blk u.a; }"}, .reject = {} },
    });
}

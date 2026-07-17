const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: pointer types render as zig prints" {
    try compliance.check(a, .{
        .{ .src = &.{"*const u8"}, .want = *const u8 },
        .{ .src = &.{"[*]u32"}, .want = [*]u32 },
        .{ .src = &.{"[]i32"}, .want = []i32 },
        .{ .src = &.{"*const *const u32"}, .want = *const *const u32 },
        .{ .src = &.{"*align(4) u8"}, .want = *align(4) u8 },
        .{ .src = &.{"*align(16) u32"}, .want = *align(16) u32 },
        .{ .src = &.{"*align(8) const u32"}, .want = *align(8) const u32 },
        .{ .src = &.{"[]align(2) i16"}, .want = []align(2) i16 },
        .{ .src = &.{"*align(1) u8"}, .want = *align(1) u8 },
        .{ .src = &.{"@as(type, *const u8)"}, .want = @as(type, *const u8) },
        .{ .src = &.{"@as(type, [*]i32)"}, .want = @as(type, [*]i32) },
        .{ .src = &.{"@as(type, *const *const u32)"}, .want = @as(type, *const *const u32) },
    });
}

test "compliance: @alignOf matches the host target ABI" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, .{
        .{ .src = &.{"@alignOf(u8)"}, .want = @alignOf(u8) },
        .{ .src = &.{"@alignOf(u32)"}, .want = @alignOf(u32) },
        .{ .src = &.{"@alignOf(u64)"}, .want = @alignOf(u64) },
        .{ .src = &.{"@alignOf(u128)"}, .want = @alignOf(u128) },
        .{ .src = &.{"@alignOf(i7)"}, .want = @alignOf(i7) },
        .{ .src = &.{"@alignOf(bool)"}, .want = @alignOf(bool) },
        .{ .src = &.{"@alignOf(usize)"}, .want = @alignOf(usize) },
        .{ .src = &.{"@alignOf(f32)"}, .want = @alignOf(f32) },
        .{ .src = &.{"@alignOf(f64)"}, .want = @alignOf(f64) },
        .{ .src = &.{"@alignOf(*u8)"}, .want = @alignOf(*u8) },
        .{ .src = &.{"@alignOf(*align(16) u8)"}, .want = @alignOf(*align(16) u8) },
        .{ .src = &.{"@alignOf(comptime_int)"}, .want = @alignOf(comptime_int) },
    });
}

test "compliance: @sizeOf matches the host target ABI" {
    try compliance.check(a, .{
        .{ .src = &.{"@sizeOf(u8)"}, .want = @sizeOf(u8) },
        .{ .src = &.{"@sizeOf(u32)"}, .want = @sizeOf(u32) },
        .{ .src = &.{"@sizeOf(u64)"}, .want = @sizeOf(u64) },
        .{ .src = &.{"@sizeOf(f16)"}, .want = @sizeOf(f16) },
        .{ .src = &.{"@sizeOf(void)"}, .want = @sizeOf(void) },
        .{ .src = &.{"@sizeOf([]u8)"}, .want = @sizeOf([]u8) },
        .{ .src = &.{"@sizeOf([4]u16)"}, .want = @sizeOf([4]u16) },
        .{ .src = &.{"@sizeOf(usize)"}, .want = @sizeOf(usize) },
        .{ .src = &.{"@sizeOf(comptime_int)"}, .reject = {} },
        .{ .src = &.{"@sizeOf(noreturn)"}, .reject = {} },
        // Packed struct/union layout resolves via the backing integer.
        .{ .src = &.{"@sizeOf(packed struct(u16) { a: u8, b: u8 })"}, .want = @sizeOf(packed struct(u16) { a: u8, b: u8 }) },
        .{ .src = &.{"@sizeOf(packed union { a: u8, b: u8 })"}, .want = @sizeOf(packed union { a: u8, b: u8 }) },
    });
}

test "compliance: a packed struct value round-trips through @bitCast" {
    try compliance.check(a, .{
        .{
            .src = &.{"@as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21)))))"},
            .want = @as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21))))),
        },
    });
}

test "compliance: @as to a named packed struct resolves its layout without clobbering the ref cache" {
    // Referencing a named `packed struct(T)` as `@as`'s dest resolves its explicit backing-int body in
    // the decl's own ZIR; that nested evaluation must not clobber the caller's cached instruction results.
    try compliance.check(a, .{
        .{
            .src = &.{ "const S = packed struct(u8) { a: u4, b: u4 };", "@as(u8, @bitCast(@as(S, @bitCast(@as(u8, 0x21)))))" },
            .want = @as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21))))),
        },
        .{
            .src = &.{ "const S = packed struct(u8) { a: u4, b: u4 };", "@as(S, @bitCast(@as(u8, 0x21))).a" },
            .want = @as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21))).a,
        },
    });
}

test "compliance: a packed struct literal packs fields into the backing int" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 }; break :blk x.a; }"}, .want = blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 };
            break :blk x.a;
        } },
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 }; break :blk x.b; }"}, .want = blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 };
            break :blk x.b;
        } },
        .{
            .src = &.{"@as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, .{ .a = 1, .b = 2 })))"},
            .want = @as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, .{ .a = 1, .b = 2 }))),
        },
    });
}

test "compliance: a packed union literal bitcasts its field into the backing int" {
    try compliance.check(a, .{
        .{
            .src = &.{"@as(u8, @bitCast(@as(packed union { a: u8, b: u8 }, .{ .a = 0x21 })))"},
            .want = @as(u8, @bitCast(@as(packed union { a: u8, b: u8 }, .{ .a = 0x21 }))),
        },
    });
}

test "compliance: packed struct field access extracts the field bits" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21)); break :blk x.a; }"}, .want = blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21));
            break :blk x.a;
        } },
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21)); break :blk x.b; }"}, .want = blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21));
            break :blk x.b;
        } },
    });
}

test "compliance: @bitSizeOf matches the host target ABI" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, .{
        .{ .src = &.{"@bitSizeOf(u0)"}, .want = @bitSizeOf(u0) },
        .{ .src = &.{"@bitSizeOf(u7)"}, .want = @bitSizeOf(u7) },
        .{ .src = &.{"@bitSizeOf(u8)"}, .want = @bitSizeOf(u8) },
        .{ .src = &.{"@bitSizeOf(u64)"}, .want = @bitSizeOf(u64) },
        .{ .src = &.{"@bitSizeOf(bool)"}, .want = @bitSizeOf(bool) },
        .{ .src = &.{"@bitSizeOf(void)"}, .want = @bitSizeOf(void) },
        .{ .src = &.{"@bitSizeOf(f32)"}, .want = @bitSizeOf(f32) },
        .{ .src = &.{"@bitSizeOf(f64)"}, .want = @bitSizeOf(f64) },
        .{ .src = &.{"@bitSizeOf(*u8)"}, .want = @bitSizeOf(*u8) },
        .{ .src = &.{"@bitSizeOf([4]u8)"}, .want = @bitSizeOf([4]u8) },
        // Exercises the int_tag_mode `.explicit` path: enum bitSize routes through intInfo -> int tag.
        .{ .src = &.{"@bitSizeOf(enum(u8) { a, b })"}, .want = @bitSizeOf(enum(u8) { a, b }) },
        // hasBitRepresentation rejects comptime-only operands.
        .{ .src = &.{"@bitSizeOf(comptime_int)"}, .reject = {} },
        .{ .src = &.{"@bitSizeOf(type)"}, .reject = {} },
    });
}

test "compliance: &decl carries the binding's constness and alignment" {
    try compliance.check(a, .{
        .{ .src = &.{ "var x: u32 = 5;", "@TypeOf(&x)" }, .want = *u32 },
        .{ .src = &.{ "const z: u32 = 5;", "@TypeOf(&z)" }, .want = *const u32 },
        .{ .src = &.{ "var w: u32 align(4) = 5;", "@TypeOf(&w)" }, .want = *align(4) u32 },
        .{ .src = &.{ "const c: u8 align(16) = 1;", "@TypeOf(&c)" }, .want = *align(16) const u8 },
    });
}

test "compliance: @intFromPtr honors the pointer's alignment" {
    // The REPL's address is synthetic, so it never equals a `zig run` address.
    // Both sides honor `@intFromPtr(&x) % align == 0` and pointer identity, so
    // pin those invariants rather than a concrete (unfoldable) address.
    try compliance.check(a, .{
        .{ .src = &.{ "var x: u32 align(8) = 5;", "@intFromPtr(&x) % 8" }, .rendered = "0" },
        .{ .src = &.{ "var w: u64 align(16) = 5;", "@intFromPtr(&w) % 16" }, .rendered = "0" },
        .{ .src = &.{ "var p: u32 = 5;", "@intFromPtr(&p) % @alignOf(u32)" }, .rendered = "0" },
        .{ .src = &.{ "const a = [_]u8{ 1, 2, 3 };", "@intFromPtr(&a) == @intFromPtr(&a)" }, .rendered = "true" },
        .{ .src = &.{ "const a = [_]u8{ 1, 2 };", "const b = [_]u8{ 3, 4 };", "@intFromPtr(&a) == @intFromPtr(&b)" }, .rendered = "false" },
        .{ .src = &.{ "var v: u32 = 5;", "@intFromPtr(&v) == @intFromPtr(&v)" }, .rendered = "true" },
    });
}

test "compliance: var mutation and pointer store/load" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { var x: u8 = 0; x = x + 1; break :blk x; }"}, .want = blk: {
            var x: u8 = 0;
            x = x + 1;
            break :blk x;
        } },
        .{ .src = &.{"blk: { var x: u8 = 200; x = x +% 100; break :blk x; }"}, .want = blk: {
            var x: u8 = 200;
            x = x +% 100;
            break :blk x;
        } },
        .{ .src = &.{"blk: { var a: u8 = 1; var b: u8 = 2; a = 10; b = 20; break :blk a + b; }"}, .want = blk: {
            var av: u8 = 1;
            var bv: u8 = 2;
            av = 10;
            bv = 20;
            break :blk av + bv;
        } },
        .{ .src = &.{"blk: { var y: u32 = 1; const p = &y; p.* = 5; break :blk y; }"}, .want = blk: {
            var y: u32 = 1;
            const p = &y;
            p.* = 5;
            break :blk y;
        } },
        .{ .src = &.{"blk: { var y: u32 = 1; const p = &y; p.* = 9; break :blk p.*; }"}, .want = blk: {
            var y: u32 = 1;
            const p = &y;
            p.* = 9;
            break :blk p.*;
        } },
        .{ .src = &.{"blk: { var y: i32 = 10; const p = &y; p.* = p.* - 3; break :blk y; }"}, .want = blk: {
            var y: i32 = 10;
            const p = &y;
            p.* = p.* - 3;
            break :blk y;
        } },
    });
}

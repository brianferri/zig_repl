const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

// `@fieldParentPtr` recovers a pointer to the containing struct/union from a pointer to one of its
// fields; the `.auto`-layout case reads the field pointer's base, the alignment mismatch case requires
// an `@alignCast`.
test "compliance: @fieldParentPtr recovers the parent pointer" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { a: u32, b: u32 }; var s: S = .{ .a = 1, .b = 7 }; break :blk @as(*S, @fieldParentPtr(\"b\", &s.b)).a; }"},
            .want = compliance.want(blk: {
                const S = struct { a: u32, b: u32 };
                var s: S = .{ .a = 1, .b = 7 };
                break :blk @as(*S, @fieldParentPtr("b", &s.b)).a;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { a: u32, b: u32, c: u32 }; var s: S = .{ .a = 10, .b = 20, .c = 30 }; break :blk @as(*S, @fieldParentPtr(\"c\", &s.c)).a + @as(*S, @fieldParentPtr(\"b\", &s.b)).c; }"},
            .want = compliance.want(blk: {
                const S = struct { a: u32, b: u32, c: u32 };
                var s: S = .{ .a = 10, .b = 20, .c = 30 };
                break :blk @as(*S, @fieldParentPtr("c", &s.c)).a + @as(*S, @fieldParentPtr("b", &s.b)).c;
            }),
        },
        .{
            .src = &.{"blk: { const U = union { a: u32, b: u32 }; var u: U = .{ .b = 42 }; break :blk @as(*U, @fieldParentPtr(\"b\", &u.b)).b; }"},
            .want = compliance.want(blk: {
                const U = union { a: u32, b: u32 };
                var u: U = .{ .b = 42 };
                break :blk @as(*U, @fieldParentPtr("b", &u.b)).b;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { x: u8, y: u16 }; var s: S = .{ .x = 3, .y = 500 }; break :blk @as(*S, @alignCast(@fieldParentPtr(\"x\", &s.x))).y; }"},
            .want = compliance.want(blk: {
                const S = struct { x: u8, y: u16 };
                var s: S = .{ .x = 3, .y = 500 };
                break :blk @as(*S, @alignCast(@fieldParentPtr("x", &s.x))).y;
            }),
        },
    });
}

test "compliance: pointer types render as zig prints" {
    try compliance.check(a, &.{
        .{ .src = &.{"*const u8"}, .want = compliance.want(*const u8) },
        .{ .src = &.{"[*]u32"}, .want = compliance.want([*]u32) },
        .{ .src = &.{"[]i32"}, .want = compliance.want([]i32) },
        .{ .src = &.{"*const *const u32"}, .want = compliance.want(*const *const u32) },
        .{ .src = &.{"*align(4) u8"}, .want = compliance.want(*align(4) u8) },
        .{ .src = &.{"*align(16) u32"}, .want = compliance.want(*align(16) u32) },
        .{ .src = &.{"*align(8) const u32"}, .want = compliance.want(*align(8) const u32) },
        .{ .src = &.{"[]align(2) i16"}, .want = compliance.want([]align(2) i16) },
        .{ .src = &.{"*align(1) u8"}, .want = compliance.want(*align(1) u8) },
        .{ .src = &.{"@as(type, *const u8)"}, .want = compliance.want(@as(type, *const u8)) },
        .{ .src = &.{"@as(type, [*]i32)"}, .want = compliance.want(@as(type, [*]i32)) },
        .{ .src = &.{"@as(type, *const *const u32)"}, .want = compliance.want(@as(type, *const *const u32)) },
    });
}

test "compliance: @alignOf matches the host target ABI" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, &.{
        .{ .src = &.{"@alignOf(u8)"}, .want = compliance.want(@alignOf(u8)) },
        .{ .src = &.{"@alignOf(u32)"}, .want = compliance.want(@alignOf(u32)) },
        .{ .src = &.{"@alignOf(u64)"}, .want = compliance.want(@alignOf(u64)) },
        .{ .src = &.{"@alignOf(u128)"}, .want = compliance.want(@alignOf(u128)) },
        .{ .src = &.{"@alignOf(i7)"}, .want = compliance.want(@alignOf(i7)) },
        .{ .src = &.{"@alignOf(bool)"}, .want = compliance.want(@alignOf(bool)) },
        .{ .src = &.{"@alignOf(usize)"}, .want = compliance.want(@alignOf(usize)) },
        .{ .src = &.{"@alignOf(f32)"}, .want = compliance.want(@alignOf(f32)) },
        .{ .src = &.{"@alignOf(f64)"}, .want = compliance.want(@alignOf(f64)) },
        .{ .src = &.{"@alignOf(*u8)"}, .want = compliance.want(@alignOf(*u8)) },
        .{ .src = &.{"@alignOf(*align(16) u8)"}, .want = compliance.want(@alignOf(*align(16) u8)) },
        .{ .src = &.{"@alignOf(comptime_int)"}, .want = compliance.want(@alignOf(comptime_int)) },
        // An explicit field alignment is stored as an Alignment and drives the container's layout.
        .{ .src = &.{"@alignOf(struct { a: u8, b: u32 align(16) })"}, .want = compliance.want(@alignOf(struct { a: u8, b: u32 align(16) })) },
        .{ .src = &.{"@sizeOf(struct { a: u8, b: u32 align(16) })"}, .want = compliance.want(@sizeOf(struct { a: u8, b: u32 align(16) })) },
    });
}

test "compliance: @sizeOf matches the host target ABI" {
    try compliance.check(a, &.{
        .{ .src = &.{"@sizeOf(u8)"}, .want = compliance.want(@sizeOf(u8)) },
        .{ .src = &.{"@sizeOf(u32)"}, .want = compliance.want(@sizeOf(u32)) },
        .{ .src = &.{"@sizeOf(u64)"}, .want = compliance.want(@sizeOf(u64)) },
        .{ .src = &.{"@sizeOf(f16)"}, .want = compliance.want(@sizeOf(f16)) },
        .{ .src = &.{"@sizeOf(void)"}, .want = compliance.want(@sizeOf(void)) },
        .{ .src = &.{"@sizeOf([]u8)"}, .want = compliance.want(@sizeOf([]u8)) },
        .{ .src = &.{"@sizeOf([4]u16)"}, .want = compliance.want(@sizeOf([4]u16)) },
        .{ .src = &.{"@sizeOf(usize)"}, .want = compliance.want(@sizeOf(usize)) },
        .{ .src = &.{"@sizeOf(comptime_int)"}, .reject = true },
        .{ .src = &.{"@sizeOf(noreturn)"}, .reject = true },
        // Packed struct/union layout resolves via the backing integer.
        .{ .src = &.{"@sizeOf(packed struct(u16) { a: u8, b: u8 })"}, .want = compliance.want(@sizeOf(packed struct(u16) { a: u8, b: u8 })) },
        .{ .src = &.{"@sizeOf(packed union { a: u8, b: u8 })"}, .want = compliance.want(@sizeOf(packed union { a: u8, b: u8 })) },
    });
}

test "compliance: a packed struct value round-trips through @bitCast" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21)))))"},
            .want = compliance.want(@as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21)))))),
        },
    });
}

test "compliance: @as to a named packed struct resolves its layout without clobbering the ref cache" {
    // Referencing a named `packed struct(T)` as `@as`'s dest resolves its explicit backing-int body in
    // the decl's own ZIR; that nested evaluation must not clobber the caller's cached instruction results.
    try compliance.check(a, &.{
        .{
            .src = &.{ "const S = packed struct(u8) { a: u4, b: u4 };", "@as(u8, @bitCast(@as(S, @bitCast(@as(u8, 0x21)))))" },
            .want = compliance.want(@as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21)))))),
        },
        .{
            .src = &.{ "const S = packed struct(u8) { a: u4, b: u4 };", "@as(S, @bitCast(@as(u8, 0x21))).a" },
            .want = compliance.want(@as(packed struct(u8) { a: u4, b: u4 }, @bitCast(@as(u8, 0x21))).a),
        },
    });
}

test "compliance: a packed struct literal packs fields into the backing int" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 }; break :blk x.a; }"}, .want = compliance.want(blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 };
            break :blk x.a;
        }) },
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 }; break :blk x.b; }"}, .want = compliance.want(blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = .{ .a = 1, .b = 2 };
            break :blk x.b;
        }) },
        .{
            .src = &.{"@as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, .{ .a = 1, .b = 2 })))"},
            .want = compliance.want(@as(u8, @bitCast(@as(packed struct(u8) { a: u4, b: u4 }, .{ .a = 1, .b = 2 })))),
        },
    });
}

test "compliance: a packed union literal bitcasts its field into the backing int" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@as(u8, @bitCast(@as(packed union { a: u8, b: u8 }, .{ .a = 0x21 })))"},
            .want = compliance.want(@as(u8, @bitCast(@as(packed union { a: u8, b: u8 }, .{ .a = 0x21 })))),
        },
    });
}

test "compliance: @unionInit on a packed union bitcasts the field into the backing int" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@as(u8, @bitCast(@unionInit(packed union { a: u8, b: u8 }, \"a\", 0x21)))"},
            .want = compliance.want(@as(u8, @bitCast(@unionInit(packed union { a: u8, b: u8 }, "a", 0x21)))),
        },
    });
}

test "compliance: packed struct field access extracts the field bits" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21)); break :blk x.a; }"}, .want = compliance.want(blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21));
            break :blk x.a;
        }) },
        .{ .src = &.{"blk: { const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21)); break :blk x.b; }"}, .want = compliance.want(blk: {
            const x: packed struct(u8) { a: u4, b: u4 } = @bitCast(@as(u8, 0x21));
            break :blk x.b;
        }) },
    });
}

test "compliance: @bitSizeOf matches the host target ABI" {
    @setEvalBranchQuota(20_000);
    try compliance.check(a, &.{
        .{ .src = &.{"@bitSizeOf(u0)"}, .want = compliance.want(@bitSizeOf(u0)) },
        .{ .src = &.{"@bitSizeOf(u7)"}, .want = compliance.want(@bitSizeOf(u7)) },
        .{ .src = &.{"@bitSizeOf(u8)"}, .want = compliance.want(@bitSizeOf(u8)) },
        .{ .src = &.{"@bitSizeOf(u64)"}, .want = compliance.want(@bitSizeOf(u64)) },
        .{ .src = &.{"@bitSizeOf(bool)"}, .want = compliance.want(@bitSizeOf(bool)) },
        .{ .src = &.{"@bitSizeOf(void)"}, .want = compliance.want(@bitSizeOf(void)) },
        .{ .src = &.{"@bitSizeOf(f32)"}, .want = compliance.want(@bitSizeOf(f32)) },
        .{ .src = &.{"@bitSizeOf(f64)"}, .want = compliance.want(@bitSizeOf(f64)) },
        .{ .src = &.{"@bitSizeOf(*u8)"}, .want = compliance.want(@bitSizeOf(*u8)) },
        .{ .src = &.{"@bitSizeOf([4]u8)"}, .want = compliance.want(@bitSizeOf([4]u8)) },
        // Exercises the int_tag_mode `.explicit` path: enum bitSize routes through intInfo -> int tag.
        .{ .src = &.{"@bitSizeOf(enum(u8) { a, b })"}, .want = compliance.want(@bitSizeOf(enum(u8) { a, b })) },
        // hasBitRepresentation rejects comptime-only operands.
        .{ .src = &.{"@bitSizeOf(comptime_int)"}, .reject = true },
        .{ .src = &.{"@bitSizeOf(type)"}, .reject = true },
    });
}

test "compliance: &decl carries the binding's constness and alignment" {
    try compliance.check(a, &.{
        .{ .src = &.{ "var x: u32 = 5;", "@TypeOf(&x)" }, .want = compliance.want(*u32) },
        .{ .src = &.{ "const z: u32 = 5;", "@TypeOf(&z)" }, .want = compliance.want(*const u32) },
        .{ .src = &.{ "var w: u32 align(4) = 5;", "@TypeOf(&w)" }, .want = compliance.want(*align(4) u32) },
        .{ .src = &.{ "const c: u8 align(16) = 1;", "@TypeOf(&c)" }, .want = compliance.want(*align(16) const u8) },
    });
}

test "compliance: @intFromPtr honors the pointer's alignment" {
    // The REPL's address is synthetic, so it never equals a `zig run` address.
    // Both sides honor `@intFromPtr(&x) % align == 0` and pointer identity, so
    // pin those invariants rather than a concrete (unfoldable) address.
    try compliance.check(a, &.{
        .{ .src = &.{ "var x: u32 align(8) = 5;", "@intFromPtr(&x) % 8" }, .rendered = "0" },
        .{ .src = &.{ "var w: u64 align(16) = 5;", "@intFromPtr(&w) % 16" }, .rendered = "0" },
        .{ .src = &.{ "var p: u32 = 5;", "@intFromPtr(&p) % @alignOf(u32)" }, .rendered = "0" },
        .{ .src = &.{ "const a = [_]u8{ 1, 2, 3 };", "@intFromPtr(&a) == @intFromPtr(&a)" }, .rendered = "true" },
        .{ .src = &.{ "const a = [_]u8{ 1, 2 };", "const b = [_]u8{ 3, 4 };", "@intFromPtr(&a) == @intFromPtr(&b)" }, .rendered = "false" },
        .{ .src = &.{ "var v: u32 = 5;", "@intFromPtr(&v) == @intFromPtr(&v)" }, .rendered = "true" },
    });
}

test "compliance: var mutation and pointer store/load" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { var x: u8 = 0; x = x + 1; break :blk x; }"}, .want = compliance.want(blk: {
            var x: u8 = 0;
            x = x + 1;
            break :blk x;
        }) },
        .{ .src = &.{"blk: { var x: u8 = 200; x = x +% 100; break :blk x; }"}, .want = compliance.want(blk: {
            var x: u8 = 200;
            x = x +% 100;
            break :blk x;
        }) },
        .{ .src = &.{"blk: { var a: u8 = 1; var b: u8 = 2; a = 10; b = 20; break :blk a + b; }"}, .want = compliance.want(blk: {
            var av: u8 = 1;
            var bv: u8 = 2;
            av = 10;
            bv = 20;
            break :blk av + bv;
        }) },
        .{ .src = &.{"blk: { var y: u32 = 1; const p = &y; p.* = 5; break :blk y; }"}, .want = compliance.want(blk: {
            var y: u32 = 1;
            const p = &y;
            p.* = 5;
            break :blk y;
        }) },
        .{ .src = &.{"blk: { var y: u32 = 1; const p = &y; p.* = 9; break :blk p.*; }"}, .want = compliance.want(blk: {
            var y: u32 = 1;
            const p = &y;
            p.* = 9;
            break :blk p.*;
        }) },
        .{ .src = &.{"blk: { var y: i32 = 10; const p = &y; p.* = p.* - 3; break :blk y; }"}, .want = compliance.want(blk: {
            var y: i32 = 10;
            const p = &y;
            p.* = p.* - 3;
            break :blk y;
        }) },
    });
}

// A field pointer routes through structFieldPtrByIndex / unionFieldPtr, then loads or stores through it.
test "compliance: struct and union field pointers" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const S = struct { a: u32, b: u32 }; const s: S = .{ .a = 3, .b = 4 }; const p = &s.b; break :blk p.*; }"}, .want = compliance.want(blk: {
            const S = struct { a: u32, b: u32 };
            const s: S = .{ .a = 3, .b = 4 };
            const p = &s.b;
            break :blk p.*;
        }) },
        .{ .src = &.{"blk: { const S = struct { a: u32, b: u32 }; var s: S = .{ .a = 3, .b = 4 }; const p = &s.a; p.* = 10; break :blk s.a + s.b; }"}, .want = compliance.want(blk: {
            const S = struct { a: u32, b: u32 };
            var s: S = .{ .a = 3, .b = 4 };
            const p = &s.a;
            p.* = 10;
            break :blk s.a + s.b;
        }) },
        .{ .src = &.{"blk: { const Inner = struct { x: u32 }; const S = struct { inner: Inner }; const s: S = .{ .inner = .{ .x = 7 } }; break :blk (&s.inner.x).*; }"}, .want = compliance.want(blk: {
            const Inner = struct { x: u32 };
            const S = struct { inner: Inner };
            const s: S = .{ .inner = .{ .x = 7 } };
            break :blk (&s.inner.x).*;
        }) },
        .{ .src = &.{"blk: { const U = union(enum) { a: u32, b: u32 }; const u: U = .{ .a = 9 }; break :blk (&u.a).*; }"}, .want = compliance.want(blk: {
            const U = union(enum) { a: u32, b: u32 };
            const u: U = .{ .a = 9 };
            break :blk (&u.a).*;
        }) },
        // A pointer to an inactive union field is rejected, like the value access.
        .{ .src = &.{"blk: { const U = union(enum) { a: u32, b: u32 }; const u: U = .{ .a = 9 }; break :blk (&u.b).*; }"}, .reject = true },
    });
}

test "compliance: @ptrFromInt builds a pointer at an address" {
    try compliance.check(a, &.{
        .{ .src = &.{"@intFromPtr(@as(*const u8, @ptrFromInt(0x1000)))"}, .want = compliance.want(@intFromPtr(@as(*const u8, @ptrFromInt(0x1000)))) },
        .{ .src = &.{"blk: { const p: ?*const u8 = @ptrFromInt(0); break :blk p == null; }"}, .want = compliance.want(blk: {
            const p: ?*const u8 = @ptrFromInt(0);
            break :blk p == null;
        }) },
        // Address zero for a non-optional, non-allowzero pointer is rejected.
        .{ .src = &.{"@as(*const u8, @ptrFromInt(0))"}, .reject = true },
        // An address that does not satisfy the pointee alignment is rejected.
        .{ .src = &.{"@as(*const u32, @ptrFromInt(0x1001))"}, .reject = true },
        // The destination must be a pointer type.
        .{ .src = &.{"@as(u32, @ptrFromInt(0x10))"}, .reject = true },
    });
}

// A single-item pointer coerces to `*anyopaque` by re-typing the pointer, not the
// pointee (the compiler's to_anyopaque). This is the coercion a reified struct's
// `default_value_ptr` (a `?*const anyopaque`) relies on.
test "compliance: a pointer coerces to *anyopaque" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const p: ?*const anyopaque = &@as(u32, 5); break :blk @as(u8, @intFromBool(p != null)); }"}, .want = compliance.want(blk: {
            const p: ?*const anyopaque = &@as(u32, 5);
            break :blk @as(u8, @intFromBool(p != null));
        }) },
    });
}

test "compliance: pointer-cast family" {
    try compliance.check(a, &.{
        // @ptrCast changes element type; result type is the destination.
        .{ .src = &.{"blk: { const p: *const u32 = @ptrFromInt(0x1000); const q: *const u8 = @ptrCast(p); break :blk @intFromPtr(q); }"}, .want = compliance.want(blk: {
            const p: *const u32 = @ptrFromInt(0x1000);
            const q: *const u8 = @ptrCast(p);
            break :blk @intFromPtr(q);
        }) },
        // @constCast / @volatileCast need no result type; they clear a qualifier.
        .{ .src = &.{ "const p: *const u32 = @ptrFromInt(0x1000);", "@TypeOf(@constCast(p))" }, .want = compliance.want(*u32) },
        .{ .src = &.{ "const p: *volatile u32 = @ptrFromInt(0x1000);", "@TypeOf(@volatileCast(p))" }, .want = compliance.want(*u32) },
        // @alignCast asserts a higher alignment; the address already satisfies it.
        .{ .src = &.{ "const p: *u32 = @ptrFromInt(0x1000);", "@intFromPtr(@as(*align(4) u32, @alignCast(p)))" }, .want = compliance.want(@intFromPtr(@as(*align(4) u32, @alignCast(@as(*u32, @ptrFromInt(0x1000)))))) },
        // A slice @ptrCast recomputes the length from element sizes.
        .{ .src = &.{ "var arr = [_]u32{ 1, 2, 3 };", "const s: []u32 = &arr;", "@as([]const u8, @ptrCast(s)).len" }, .rendered = "12" },
        // Rejections: each qualifier/alignment change requires its own builtin.
        .{ .src = &.{"blk: { const p: *const u32 = @ptrFromInt(0x1000); const q: *u32 = @ptrCast(p); break :blk @intFromPtr(q); }"}, .reject = true },
        .{ .src = &.{"blk: { const p: *volatile u32 = @ptrFromInt(0x1000); const q: *u32 = @ptrCast(p); break :blk @intFromPtr(q); }"}, .reject = true },
    });
}

test "compliance: pointer equality compares base and offset" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const a2 = [_]u8{ 1, 2, 3 }; const p: [*]const u8 = &a2; break :blk p == p; }"}, .want = compliance.want(blk: {
            const a2 = [_]u8{ 1, 2, 3 };
            const p: [*]const u8 = &a2;
            break :blk p == p;
        }) },
        .{ .src = &.{"blk: { const a2 = [_]u8{ 1, 2 }; const b = [_]u8{ 3, 4 }; const pa: [*]const u8 = &a2; const pb: [*]const u8 = &b; break :blk pa == pb; }"}, .want = compliance.want(blk: {
            const a2 = [_]u8{ 1, 2 };
            const b = [_]u8{ 3, 4 };
            const pa: [*]const u8 = &a2;
            const pb: [*]const u8 = &b;
            break :blk pa == pb;
        }) },
        // std.mem.eql (and the family built on it) hinges on `a.ptr == b.ptr`.
        .{ .src = &.{ "const std = @import(\"std\");", "std.mem.eql(u8, \"foo\", \"foo\")" }, .want = compliance.want(std.mem.eql(u8, "foo", "foo")) },
        .{ .src = &.{ "const std = @import(\"std\");", "std.mem.indexOf(u8, \"hello world\", \"world\").?" }, .want = compliance.want(std.mem.indexOf(u8, "hello world", "world").?) },
    });
}

// The C-pointer coercion family: `*[N]T`/`[*]T`/`null`/integer sources coerce into a `[*c]T`, and a
// `[*c]T` source retypes back into any non-slice pointer whose element type matches -- but a coercion that
// would drop `const` is rejected (compiler: coerceExtra's src_array_ptr/src_c_ptr/`.c` arms guarded by
// checkPtrAttributes). Null-ness of a C pointer is its address, so `c == null` follows the address.
test "compliance: the C-pointer coercion family" {
    try compliance.check(a, &.{
        // *[N]T -> [*c]T (decay by retype), then index and slice.
        .{ .src = &.{"blk: { const a2 = [_]u8{ 10, 20, 30, 40 }; const c: [*c]const u8 = &a2; break :blk c[1]; }"}, .want = compliance.want(blk: {
            const a2 = [_]u8{ 10, 20, 30, 40 };
            const c: [*c]const u8 = &a2;
            break :blk c[1];
        }) },
        .{ .src = &.{"blk: { const a2 = [_]u8{ 10, 20, 30, 40 }; const c: [*c]const u8 = &a2; const s = c[1..3]; break :blk s[0]; }"}, .want = compliance.want(blk: {
            const a2 = [_]u8{ 10, 20, 30, 40 };
            const c: [*c]const u8 = &a2;
            const s = c[1..3];
            break :blk s[0];
        }) },
        // [*c]T source -> [*]T, retyped through checkPtrAttributes.
        .{ .src = &.{"blk: { const a2 = [_]u8{ 7, 8, 9 }; const c: [*c]const u8 = &a2; const m: [*]const u8 = c; break :blk m[2]; }"}, .want = compliance.want(blk: {
            const a2 = [_]u8{ 7, 8, 9 };
            const c: [*c]const u8 = &a2;
            const m: [*]const u8 = c;
            break :blk m[2];
        }) },
        // null and integer sources: a C pointer's null-ness is its address.
        .{ .src = &.{"blk: { const c: [*c]const u8 = null; break :blk c == null; }"}, .want = compliance.want(blk: {
            const c: [*c]const u8 = null;
            break :blk c == null;
        }) },
        .{ .src = &.{"blk: { const c: [*c]const u8 = 0; break :blk c == null; }"}, .want = compliance.want(blk: {
            const c: [*c]const u8 = 0;
            break :blk c == null;
        }) },
        .{ .src = &.{"blk: { const a2 = [_]u8{ 5, 6 }; const c: [*c]const u8 = &a2; break :blk c != null; }"}, .want = compliance.want(blk: {
            const a2 = [_]u8{ 5, 6 };
            const c: [*c]const u8 = &a2;
            break :blk c != null;
        }) },
        // Dropping `const` through the C pointer is rejected.
        .{ .src = &.{"blk: { const a2 = [_]u8{ 1, 2 }; const c: [*c]const u8 = &a2; const m: [*]u8 = c; break :blk m[0]; }"}, .reject = true },
    });
}

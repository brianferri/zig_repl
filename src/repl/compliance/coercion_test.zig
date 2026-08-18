const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: a comptime-known int coerces to a fixed-width int when it fits" {
    try compliance.check(a, .{
        .{ .src = &.{"@as(i64, @as(u32, 42))"}, .want = @as(i64, @as(u32, 42)) },
        .{ .src = &.{"@as(i32, @as(u8, 200))"}, .want = @as(i32, @as(u8, 200)) },
        .{ .src = &.{"@as(i8, @as(u32, 200))"}, .reject = {} },
        .{ .src = &.{"@as(u16, @as(u32, 70000))"}, .reject = {} },
    });
}

// A comptime-known float with no fractional part coerces to an integer type; a fractional value is
// rejected (compiler: coerceExtra's int-dest / float-source arm, via `intFromFloat(.exact)`).
test "compliance: a comptime-known float coerces to an integer when it has no fractional part" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: u8 = 2.0; break :blk x; }"}, .want = blk: {
            const x: u8 = 2.0;
            break :blk x;
        } },
        .{ .src = &.{"blk: { const z: i32 = 100.0; break :blk z; }"}, .want = blk: {
            const z: i32 = 100.0;
            break :blk z;
        } },
        .{ .src = &.{"@as(u8, 3.0)"}, .want = @as(u8, 3.0) },
        .{ .src = &.{"blk: { const y: u8 = 2.5; break :blk y; }"}, .reject = {} },
    });
}

// A comptime-known number coerces to a float type only when the float represents it exactly: a
// `comptime_float` always fits (it rounds), a fixed-width float or an integer must survive a round-trip
// (compiler: coerceExtra's float-dest arm, via `floatCast`/`floatValue` + representability check).
test "compliance: a comptime-known number coerces to a float only when represented exactly" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: f32 = @as(f64, 1.5); break :blk x; }"}, .want = blk: {
            const x: f32 = @as(f64, 1.5);
            break :blk x;
        } },
        .{ .src = &.{"blk: { const x: f64 = @as(f32, 1.5); break :blk x; }"}, .want = blk: {
            const x: f64 = @as(f32, 1.5);
            break :blk x;
        } },
        .{ .src = &.{"@as(f32, 5)"}, .want = @as(f32, 5) },
        .{ .src = &.{"@as(f32, 16777217.0)"}, .want = @as(f32, 16777217.0) },
        .{ .src = &.{"blk: { const x: f32 = @as(f64, 0.1); break :blk x; }"}, .reject = {} },
        .{ .src = &.{"@as(f32, 16777217)"}, .reject = {} },
    });
}

test "compliance: a function return coerces to the declared return type" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn five() i32 { return 5; }", "five()" }, .want = (struct {
            fn five() i32 {
                return 5;
            }
        }).five() },
        .{ .src = &.{ "fn widen(a: u8) u32 { return a; }", "widen(7)" }, .want = (struct {
            fn widen(x: u8) u32 {
                return x;
            }
        }).widen(7) },
        .{ .src = &.{ "fn small() u8 { return 300; }", "small()" }, .reject = {} },
        .{ .src = &.{ "fn id(a: u32) i32 { return a; }", "id(7)" }, .reject = {} },
        .{ .src = &.{ "fn add(a: u32, b: u32) i32 { return a + b; }", "add(40, 2)" }, .reject = {} },
    });
}

test "compliance: runtime-ness propagates through operations" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn f(x: u32) i32 { return x & 1; }", "f(7)" }, .reject = {} },
        .{ .src = &.{ "fn f(x: u32) i32 { return x << 1; }", "f(7)" }, .reject = {} },
        .{ .src = &.{ "fn f(x: i32) i16 { return -x; }", "f(7)" }, .reject = {} },
        .{ .src = &.{ "fn f(x: u8) i32 { return @as(u32, x); }", "f(7)" }, .reject = {} },
        .{ .src = &.{ "fn f(x: u32) i32 { return blk: { break :blk x; }; }", "f(7)" }, .reject = {} },
        .{ .src = &.{ "fn f(x: u8) u32 { return x & 1; }", "f(7)" }, .want = (struct {
            fn f(x: u8) u32 {
                return x & 1;
            }
        }).f(7) },
        .{ .src = &.{ "fn f(x: u8) u32 { return blk: { break :blk x; }; }", "f(7)" }, .want = (struct {
            fn f(x: u8) u32 {
                return blk: {
                    break :blk x;
                };
            }
        }).f(7) },
    });
}

test "compliance: runtime float coercion is type-based" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn f(x: f64) f32 { return x; }", "f(1.5)" }, .reject = {} },
        .{ .src = &.{ "fn f(x: u32) f32 { return x; }", "f(5)" }, .reject = {} },
        .{ .src = &.{ "fn f(x: f32) f64 { return x; }", "f(1.5)" }, .want = (struct {
            fn f(x: f32) f64 {
                return x;
            }
        }).f(1.5) },
    });
}

test "compliance: a generic return type resolves per instantiation" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn make(comptime T: type) T { return 300; }", "make(u16)" }, .want = (struct {
            fn make(comptime T: type) T {
                return 300;
            }
        }).make(u16) },
        .{ .src = &.{ "fn make(comptime T: type) T { return 300; }", "@TypeOf(make(u16))" }, .want = @TypeOf((struct {
            fn make(comptime T: type) T {
                return 300;
            }
        }).make(u16)) },
        .{ .src = &.{ "fn make(comptime T: type) T { return 300; }", "make(u8)" }, .reject = {} },
    });
}

test "compliance: a generic return body computes through arithmetic and @as" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn make(comptime T: type) T { return 1 + 2; }", "make(u8)" }, .want = (struct {
            fn make(comptime T: type) T {
                return 1 + 2;
            }
        }).make(u8) },
        .{ .src = &.{ "fn make(comptime T: type) T { return @as(T, 7) * 2; }", "make(u8)" }, .want = (struct {
            fn make(comptime T: type) T {
                return @as(T, 7) * 2;
            }
        }).make(u8) },
    });
}

test "compliance: a generic return body assigns and mutates a T-typed local" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn make(comptime T: type) T { var x: T = 10; x = x + 5; return x; }", "make(u8)" }, .want = (struct {
            fn make(comptime T: type) T {
                var x: T = 10;
                x = x + 5;
                return x;
            }
        }).make(u8) },
        .{ .src = &.{ "fn make(comptime T: type) T { const n: T = 3; return n; }", "make(i32)" }, .want = (struct {
            fn make(comptime T: type) T {
                const n: T = 3;
                return n;
            }
        }).make(i32) },
    });
}

test "compliance: a generic return coerces a runtime value type-based" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn make(comptime T: type, x: u16) T { return x; }", "make(u16, 300)" }, .want = (struct {
            fn make(comptime T: type, x: u16) T {
                return x;
            }
        }).make(u16, 300) },
        .{ .src = &.{ "fn make(comptime T: type, x: u16) T { return x; }", "make(u8, 5)" }, .reject = {} },
    });
}

test "compliance: a generic parameter type resolves per instantiation" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn id(comptime T: type, x: T) T { return x; }", "id(u8, 5)" }, .want = (struct {
            fn id(comptime T: type, x: T) T {
                return x;
            }
        }).id(u8, 5) },
        .{ .src = &.{ "fn id(comptime T: type, x: T) T { return x; }", "id(i32, -7)" }, .want = (struct {
            fn id(comptime T: type, x: T) T {
                return x;
            }
        }).id(i32, -7) },
        .{ .src = &.{ "fn id(comptime T: type, x: T) T { return x; }", "@TypeOf(id(u16, 1))" }, .want = @TypeOf((struct {
            fn id(comptime T: type, x: T) T {
                return x;
            }
        }).id(u16, 1)) },
        .{ .src = &.{ "fn id(comptime T: type, x: T) T { return x; }", "id(u8, 300)" }, .reject = {} },
    });
}

test "compliance: generic and concrete parameters mix in one signature" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn add(comptime T: type, x: T, y: T) T { return x + y; }", "add(u16, 40, 2)" }, .want = (struct {
            fn add(comptime T: type, x: T, y: T) T {
                return x + y;
            }
        }).add(u16, 40, 2) },
        .{ .src = &.{ "fn f(comptime T: type, x: T, y: u8) T { return x + y; }", "f(u16, 40, 2)" }, .want = (struct {
            fn f(comptime T: type, x: T, y: u8) T {
                return x + y;
            }
        }).f(u16, 40, 2) },
    });
}

test "compliance: an anytype parameter takes the argument's type per call" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn dbl(x: anytype) @TypeOf(x) { return x + x; }", "dbl(21)" }, .want = (struct {
            fn dbl(x: anytype) @TypeOf(x) {
                return x + x;
            }
        }).dbl(21) },
        .{ .src = &.{ "fn dbl(x: anytype) @TypeOf(x) { return x + x; }", "dbl(@as(u8, 100))" }, .want = (struct {
            fn dbl(x: anytype) @TypeOf(x) {
                return x + x;
            }
        }).dbl(@as(u8, 100)) },
        .{ .src = &.{ "fn dbl(x: anytype) @TypeOf(x) { return x + x; }", "@TypeOf(dbl(@as(u16, 3)))" }, .want = @TypeOf((struct {
            fn dbl(x: anytype) @TypeOf(x) {
                return x + x;
            }
        }).dbl(@as(u16, 3))) },
        .{ .src = &.{ "fn add(x: anytype, y: anytype) @TypeOf(x) { return x + y; }", "add(@as(u8, 40), @as(u8, 2))" }, .want = (struct {
            fn add(x: anytype, y: anytype) @TypeOf(x) {
                return x + y;
            }
        }).add(@as(u8, 40), @as(u8, 2)) },
    });
}

test "compliance: an anytype generic dispatches over the argument type (math.order-style)" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn cmp(a: anytype, b: anytype) i8 { return if (a < b) -1 else if (a > b) 1 else 0; }", "cmp(3, 7)" }, .want = (struct {
            fn cmp(x: anytype, y: anytype) i8 {
                return if (x < y) -1 else if (x > y) 1 else 0;
            }
        }).cmp(3, 7) },
        .{ .src = &.{ "fn cmp(a: anytype, b: anytype) i8 { return if (a < b) -1 else if (a > b) 1 else 0; }", "cmp(9, 4)" }, .want = (struct {
            fn cmp(x: anytype, y: anytype) i8 {
                return if (x < y) -1 else if (x > y) 1 else 0;
            }
        }).cmp(9, 4) },
        .{ .src = &.{ "fn cmp(a: anytype, b: anytype) i8 { return if (a < b) -1 else if (a > b) 1 else 0; }", "cmp(5, 5)" }, .want = (struct {
            fn cmp(x: anytype, y: anytype) i8 {
                return if (x < y) -1 else if (x > y) 1 else 0;
            }
        }).cmp(5, 5) },
        .{ .src = &.{ "fn cmp(a: anytype, b: anytype) i8 { return if (a < b) -1 else if (a > b) 1 else 0; }", "cmp(@as(f64, 1.5), @as(f64, 2.5))" }, .want = (struct {
            fn cmp(x: anytype, y: anytype) i8 {
                return if (x < y) -1 else if (x > y) 1 else 0;
            }
        }).cmp(@as(f64, 1.5), @as(f64, 2.5)) },
    });
}

test "compliance: anytype params over comptime, fixed-width, and multi-statement bodies" {
    try compliance.check(a, .{
        .{ .src = &.{ "fn tw(comptime x: anytype) @TypeOf(x) { return x + x; }", "tw(21)" }, .want = (struct {
            fn tw(comptime x: anytype) @TypeOf(x) {
                return x + x;
            }
        }).tw(21) },
        .{ .src = &.{ "fn sq(x: anytype) @TypeOf(x) { const y = x * x; return y; }", "sq(@as(u8, 9))" }, .want = (struct {
            fn sq(x: anytype) @TypeOf(x) {
                const y = x * x;
                return y;
            }
        }).sq(@as(u8, 9)) },
    });
}

test "compliance: multi-arg @TypeOf peer-resolves the operand types" {
    try compliance.check(a, .{
        .{ .src = &.{"@TypeOf(1, 2, 3)"}, .want = @TypeOf(1, 2, 3) },
        .{ .src = &.{"@TypeOf(@as(u8, 1), @as(u16, 2))"}, .want = @TypeOf(@as(u8, 1), @as(u16, 2)) },
        .{ .src = &.{"@TypeOf(@as(f32, 1), @as(f64, 2))"}, .want = @TypeOf(@as(f32, 1), @as(f64, 2)) },
        .{ .src = &.{"@TypeOf(1, @as(f32, 2))"}, .want = @TypeOf(1, @as(f32, 2)) },
        .{ .src = &.{"@TypeOf(@as(i32, 5), 1.5)"}, .reject = {} },
    });
}

test "compliance: std.math.clamp-style anytype generic with @TypeOf(v, lo, hi)" {
    const clamp = "fn clamp(v: anytype, lo: anytype, hi: anytype) @TypeOf(v, lo, hi) { return if (v < lo) lo else if (v > hi) hi else v; }";
    try compliance.check(a, .{
        .{ .src = &.{ clamp, "clamp(5, 0, 10)" }, .want = (struct {
            fn cl(v: anytype, lo: anytype, hi: anytype) @TypeOf(v, lo, hi) {
                return if (v < lo) lo else if (v > hi) hi else v;
            }
        }).cl(5, 0, 10) },
        .{ .src = &.{ clamp, "clamp(15, 0, 10)" }, .want = (struct {
            fn cl(v: anytype, lo: anytype, hi: anytype) @TypeOf(v, lo, hi) {
                return if (v < lo) lo else if (v > hi) hi else v;
            }
        }).cl(15, 0, 10) },
        .{ .src = &.{ clamp, "clamp(@as(i32, -5), @as(i32, 0), @as(i32, 10))" }, .want = (struct {
            fn cl(v: anytype, lo: anytype, hi: anytype) @TypeOf(v, lo, hi) {
                return if (v < lo) lo else if (v > hi) hi else v;
            }
        }).cl(@as(i32, -5), @as(i32, 0), @as(i32, 10)) },
        .{ .src = &.{ clamp, "clamp(@as(f64, 1.5), @as(f64, 0.0), @as(f64, 1.0))" }, .want = (struct {
            fn cl(v: anytype, lo: anytype, hi: anytype) @TypeOf(v, lo, hi) {
                return if (v < lo) lo else if (v > hi) hi else v;
            }
        }).cl(@as(f64, 1.5), @as(f64, 0.0), @as(f64, 1.0)) },
    });
}

test "compliance: a type-returning generic function and composition" {
    const id = "fn Id(comptime T: type) type { return T; }";
    const make = "fn make(comptime T: type) T { return 200 + 100; }";
    try compliance.check(a, .{
        .{ .src = &.{ id, "Id(u8)" }, .want = (struct {
            fn Id(comptime T: type) type {
                return T;
            }
        }).Id(u8) },
        .{ .src = &.{ id, make, "@TypeOf(make(Id(u16)))" }, .want = @TypeOf((struct {
            fn mk(comptime T: type) T {
                return 200 + 100;
            }
        }).mk((struct {
            fn Id(comptime T: type) type {
                return T;
            }
        }).Id(u16))) },
        .{ .src = &.{ id, make, "make(Id(u16))" }, .want = (struct {
            fn mk(comptime T: type) T {
                return 200 + 100;
            }
        }).mk((struct {
            fn Id(comptime T: type) type {
                return T;
            }
        }).Id(u16)) },
    });
}

test "compliance: the % operator" {
    try compliance.check(a, .{
        .{ .src = &.{"17 % 8"}, .want = 17 % 8 },
        .{ .src = &.{"@as(u32, 17) % @as(u32, 8)"}, .want = @as(u32, 17) % @as(u32, 8) },
        .{ .src = &.{"@as(i32, 7) % @as(i32, 3)"}, .want = @as(i32, 7) % @as(i32, 3) },
        .{ .src = &.{"@as(f64, 5.5) % @as(f64, 2.0)"}, .want = @as(f64, 5.5) % @as(f64, 2.0) },
        .{ .src = &.{"@as(i32, -9) % @as(i32, 3)"}, .want = @as(i32, -9) % @as(i32, 3) },
        .{ .src = &.{"@as(i32, -7) % @as(i32, 3)"}, .reject = {} },
        .{ .src = &.{"@as(f64, -9.5) % @as(f64, 2.0)"}, .reject = {} },
    });
}

test "compliance: compound assignment" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { var s: u32 = 5; s += 1; break :blk s; }"}, .want = blk: {
            var s: u32 = 5;
            s += 1;
            break :blk s;
        } },
        .{ .src = &.{"blk: { var s: i32 = 5; s -= 8; break :blk s; }"}, .want = blk: {
            var s: i32 = 5;
            s -= 8;
            break :blk s;
        } },
        .{ .src = &.{"blk: { var s: u32 = 5; s *= 3; break :blk s; }"}, .want = blk: {
            var s: u32 = 5;
            s *= 3;
            break :blk s;
        } },
        .{ .src = &.{"blk: { var s: u32 = 9; s /= 2; break :blk s; }"}, .want = blk: {
            var s: u32 = 9;
            s /= 2;
            break :blk s;
        } },
        .{ .src = &.{"blk: { var i: u32 = 0; while (i < 5) : (i += 1) {} break :blk i; }"}, .want = blk: {
            var i: u32 = 0;
            while (i < 5) : (i += 1) {}
            break :blk i;
        } },
    });
}

// A tuple coerces element-wise to an array or vector of matching length (coerceTupleToArray).
test "compliance: a tuple coerces to an array or vector" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const t = .{ @as(i32, 1), @as(i32, 2), @as(i32, 3) }; const arr: [3]i32 = t; break :blk arr; }"}, .want = blk: {
            const t = .{ @as(i32, 1), @as(i32, 2), @as(i32, 3) };
            const arr: [3]i32 = t;
            break :blk arr;
        } },
        .{ .src = &.{"blk: { const arr: [3]i32 = .{ 1, 2, 3 }; break :blk arr[2]; }"}, .want = blk: {
            const arr: [3]i32 = .{ 1, 2, 3 };
            break :blk arr[2];
        } },
        .{ .src = &.{"blk: { const v: @Vector(3, i32) = .{ 1, 2, 3 }; break :blk v[1]; }"}, .want = blk: {
            const v: @Vector(3, i32) = .{ 1, 2, 3 };
            break :blk v[1];
        } },
        .{ .src = &.{"blk: { const t = .{ @as(u8, 1), @as(u8, 2), @as(u8, 3) }; const arr: [3:0]u8 = t; break :blk arr[3]; }"}, .want = blk: {
            const t = .{ @as(u8, 1), @as(u8, 2), @as(u8, 3) };
            const arr: [3:0]u8 = t;
            break :blk arr[3];
        } },
        .{ .src = &.{"blk: { const arr: [2]i32 = .{ 1, 2, 3 }; break :blk arr[0]; }"}, .reject = {} },
    });
}

// An anonymous array literal reaches its element type through an optional/error-union result type
// (`array_init_elem_type`/`zirArrayInit` peel via optEuBaseType).
test "compliance: an anonymous array literal initializes through ?/! result types" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: ?[2]i32 = .{ 1, 2 }; break :blk x.?[1]; }"}, .want = blk: {
            const x: ?[2]i32 = .{ 1, 2 };
            break :blk x.?[1];
        } },
        .{ .src = &.{"blk: { const x: anyerror![2]i32 = .{ 7, 8 }; break :blk (x catch unreachable)[0]; }"}, .want = blk: {
            const x: anyerror![2]i32 = .{ 7, 8 };
            break :blk (x catch unreachable)[0];
        } },
        .{ .src = &.{"blk: { const x: ?[2]i32 = .{ 1, 2 }; break :blk x; }"}, .want = blk: {
            const x: ?[2]i32 = .{ 1, 2 };
            break :blk x;
        } },
    });
}

// A single-item pointer to a sentinel-terminated array drops the sentinel through the pointer
// (`*const [n:s]T` -> `*const [n]T`), the special case in coerceInMemoryAllowedPtrs.
test "compliance: a pointer to a sentinel array coerces to the same pointer without the sentinel" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const p: *const [5]u8 = \"hello\"; break :blk p[1]; }"}, .want = blk: {
            const p: *const [5]u8 = "hello";
            break :blk p[1];
        } },
        // The coerced pointer keeps the byte-string display form (deliberate `.rendered`
        // divergence from `{any}`, like any `*const [n]u8`; see string_render_test).
        .{ .src = &.{"@as(*const [5]u8, \"hello\")"}, .rendered = "\"hello\"" },
    });
}

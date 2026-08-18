const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: function calls resolve same-input and cross-line" {
    try compliance.check(a, .{
        .{
            .src = &.{ "fn double(x: u32) u32 { return x + x; } const r = double(7);", "r" },
            .want = blk: {
                const double = struct {
                    fn double(x: u32) u32 {
                        return x + x;
                    }
                }.double;
                const r = double(7);
                break :blk r;
            },
        },
        .{
            .src = &.{ "fn add(a2: u32, b: u32) u32 { return a2 + b; } const r = add(3, 4);", "r" },
            .want = blk: {
                const add = struct {
                    fn add(a2: u32, b: u32) u32 {
                        return a2 + b;
                    }
                }.add;
                const r = add(3, 4);
                break :blk r;
            },
        },
        .{
            .src = &.{ "fn fact(n: u32) u32 { return if (n == 0) 1 else n * fact(n - 1); } const r = fact(5);", "r" },
            .want = blk: {
                const fact = struct {
                    fn fact(n: u32) u32 {
                        return if (n == 0) 1 else n * fact(n - 1);
                    }
                }.fact;
                const r = fact(5);
                break :blk r;
            },
        },
        .{
            .src = &.{ "fn d(x: u32) u32 { return x + x; } const r = d(d(5));", "r" },
            .want = blk: {
                const d = struct {
                    fn d(x: u32) u32 {
                        return x + x;
                    }
                }.d;
                const r = d(d(5));
                break :blk r;
            },
        },
        .{
            .src = &.{ "fn id(x: u32) u32 { return x; }", "id(42)" },
            .want = blk: {
                const id = struct {
                    fn id(x: u32) u32 {
                        return x;
                    }
                }.id;
                break :blk id(42);
            },
        },
        .{
            .src = &.{ "fn fib(n: u32) u32 { return if (n < 2) n else fib(n - 1) + fib(n - 2); }", "fib(10)" },
            .want = blk: {
                const fib = struct {
                    fn fib(n: u32) u32 {
                        return if (n < 2) n else fib(n - 1) + fib(n - 2);
                    }
                }.fib;
                break :blk fib(10);
            },
        },
        .{
            .src = &.{ "fn add(a2: u32, b: u32) u32 { return a2 + b; }", "add(3, 4)" },
            .want = blk: {
                const add = struct {
                    fn add(a2: u32, b: u32) u32 {
                        return a2 + b;
                    }
                }.add;
                break :blk add(3, 4);
            },
        },
    });
}

test "compliance: a call resolves a fn-pointer field, binding no receiver" {
    // `x.f(args)` where `f` is a field holding a callable (a vtable-style fn pointer) calls the
    // field, not a method -- the mechanism the std `Io` interface dispatches through.
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const S = struct { f: *const fn (u8) u8 }; const s: S = .{ .f = struct { fn dbl(x: u8) u8 { return x *% 2; } }.dbl }; break :blk s.f(3); }"}, .want = blk: {
            const S = struct { f: *const fn (u8) u8 };
            const s: S = .{ .f = struct {
                fn dbl(x: u8) u8 {
                    return x *% 2;
                }
            }.dbl };
            break :blk s.f(3);
        } },
        .{ .src = &.{"blk: { const S = struct { f: *const fn (u8) u8 }; const s: S = .{ .f = struct { fn dbl(x: u8) u8 { return x *% 2; } }.dbl }; const p = &s; break :blk p.f(3); }"}, .want = blk: {
            const S = struct { f: *const fn (u8) u8 };
            const s: S = .{ .f = struct {
                fn dbl(x: u8) u8 {
                    return x *% 2;
                }
            }.dbl };
            const p = &s;
            break :blk p.f(3);
        } },
        // A `comptime` field holding a callable binds through the comptime-field value directly,
        // not through a materialized field pointer.
        .{ .src = &.{"blk: { const S = struct { comptime f: *const fn (u8) u8 = struct { fn dbl(x: u8) u8 { return x *% 2; } }.dbl }; const s: S = .{}; break :blk s.f(21); }"}, .want = blk: {
            const S = struct {
                comptime f: *const fn (u8) u8 = struct {
                    fn dbl(x: u8) u8 {
                        return x *% 2;
                    }
                }.dbl,
            };
            const s: S = .{};
            break :blk s.f(21);
        } },
        .{ .src = &.{"blk: { const U = union(enum) { f: *const fn (u8) u8, g: u8 }; const u: U = .{ .f = struct { fn inc(x: u8) u8 { return x +% 1; } }.inc }; break :blk u.f(4); }"}, .want = blk: {
            const U = union(enum) { f: *const fn (u8) u8, g: u8 };
            const u: U = .{ .f = struct {
                fn inc(x: u8) u8 {
                    return x +% 1;
                }
            }.inc };
            break :blk u.f(4);
        } },
    });
}

test "compliance: defer runs at scope exit in LIFO order over live state" {
    try compliance.check(a, .{
        .{
            .src = &.{ "fn run() u32 { var s: u32 = 0; { defer s = 1; s = 2; } return s; }", "run()" },
            .want = blk: {
                const run = struct {
                    fn run() u32 {
                        var s: u32 = 0;
                        {
                            defer s = 1;
                            s = 2;
                        }
                        return s;
                    }
                }.run;
                break :blk run();
            },
        },
        .{
            .src = &.{ "fn run() u32 { var t: u32 = 1; { defer t = t * 2; defer t = t + 10; } return t; }", "run()" },
            .want = blk: {
                const run = struct {
                    fn run() u32 {
                        var t: u32 = 1;
                        {
                            defer t = t * 2;
                            defer t = t + 10;
                        }
                        return t;
                    }
                }.run;
                break :blk run();
            },
        },
        .{
            .src = &.{ "fn run() u32 { var x: u32 = 5; { defer x = x * 100; x = 7; } return x; }", "run()" },
            .want = blk: {
                const run = struct {
                    fn run() u32 {
                        var x: u32 = 5;
                        {
                            defer x = x * 100;
                            x = 7;
                        }
                        return x;
                    }
                }.run;
                break :blk run();
            },
        },
    });
}

test "compliance: a later arg's result type resolves from an earlier comptime param" {
    try compliance.check(a, .{
        // @intCast's destination is the dependent param type T, bound by the first arg.
        .{ .src = &.{"blk: { const F = struct { fn f(comptime T: type, x: T) T { return x; } }; break :blk F.f(u32, @intCast(@as(u64, 7))); }"}, .want = blk: {
            const F = struct {
                fn f(comptime T: type, x: T) T {
                    return x;
                }
            };
            break :blk F.f(u32, @intCast(@as(u64, 7)));
        } },
        .{ .src = &.{ "const std = @import(\"std\");", "std.math.log2(@as(u32, 48))" }, .want = std.math.log2(@as(u32, 48)) },
        .{ .src = &.{ "const std = @import(\"std\");", "std.math.gcd(@as(u32, 48), 36)" }, .want = std.math.gcd(@as(u32, 48), 36) },
        // A comptime-only arg to an anytype param stays comptime-known, so u16 + (comptime int) peers.
        .{ .src = &.{ "const std = @import(\"std\");", "std.math.IntFittingRange(0, 48)" }, .want = std.math.IntFittingRange(0, 48) },
        // Reflecting a runtime param's type (@sizeOf of @TypeOf) yields a comptime-known
        // comptime_int, so it peers with a concrete int instead of reading as runtime.
        .{ .src = &.{"blk: { const F = struct { fn f(x: f64) i32 { const b: comptime_int = @sizeOf(@TypeOf(x)); return @as(i32, 5) - b; } }; break :blk F.f(2.0); }"}, .want = blk: {
            const F = struct {
                fn f(x: f64) i32 {
                    const b: comptime_int = @sizeOf(@TypeOf(x));
                    return @as(i32, 5) - b;
                }
            };
            break :blk F.f(2.0);
        } },
        .{ .src = &.{ "const std = @import(\"std\");", "std.math.frexp(@as(f64, 2.0)).exponent" }, .want = std.math.frexp(@as(f64, 2.0)).exponent },
        .{ .src = &.{ "const std = @import(\"std\");", "std.math.pow(f64, 2.0, 10.0)" }, .want = std.math.pow(f64, 2.0, 10.0) },
    });
}

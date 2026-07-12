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

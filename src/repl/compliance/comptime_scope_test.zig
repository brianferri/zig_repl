const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

// A comptime-required operand makes a function call in that position inline, so its parameters and result are comptime-known.
test "comptime scope: a comptime-required operand folds a function-call result" {
    try compliance.check(a, &.{
        .{ .src = &.{ "const f = struct { fn g(n: usize) usize { return n; } }.g;", "@Int(.unsigned, f(8))" }, .rendered = "u8" },
        .{ .src = &.{ "fn bits(n: u16) u16 { return n; }", "@Int(.signed, bits(8))" }, .rendered = "i8" },
        .{ .src = &.{ "fn alen(n: usize) usize { return n; }", "[alen(3)]u8" }, .rendered = "[3]u8" },
        .{ .src = &.{ "fn vlen(n: usize) usize { return n; }", "@Vector(vlen(4), u8)" }, .rendered = "@Vector(4, u8)" },
        .{ .src = &.{ "fn id(n: usize) usize { return n; }", "@Int(.unsigned, id(id(8)))" }, .rendered = "u8" },
        .{ .src = &.{ "const std = @import(\"std\");", "@Int(.unsigned, std.math.ceilPowerOfTwoAssert(usize, 5))" }, .rendered = "u8" },
    });
}

// A container-level declaration's initializer is itself a comptime scope, so a call there folds without an explicit comptime-required operand.
test "comptime scope: a container declaration initializer folds a call" {
    try compliance.check(a, &.{
        .{
            .src = &.{ "const w = struct { fn g(n: usize) usize { return n; } }.g(200);", "w" },
            .want = compliance.want(blk: {
                const g = struct {
                    fn g(n: usize) usize {
                        return n;
                    }
                }.g;
                break :blk g(200);
            }),
        },
        .{
            .src = &.{ "fn alen(n: usize) usize { return n; }", "const arr_ty = [alen(2)]u16;", "@sizeOf(arr_ty)" },
            .want = compliance.want(@sizeOf([2]u16)),
        },
    });
}

// A top-level REPL expression evaluates in a runtime function body, so a runtime narrowing without a cast is rejected at the call site as the compiler does.
test "comptime scope: a runtime narrowing in a called function is rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const S = struct { fn f(x: u32) u8 { return x; } }; break :blk S.f(5); }"}, .reject = true, .ctx = .runtime_body },
        .{ .src = &.{"blk: { const S = struct { fn f(x: u64) u8 { return x; } }; break :blk S.f(1); }"}, .reject = true, .ctx = .runtime_body },
    });
    try compliance.expectDiagnostic(
        a,
        &.{"blk: { const S = struct { fn f(x: u32) u8 { return x; } }; break :blk S.f(5); }"},
        "expected type 'u8', found 'u32'",
    );
}

// A container-scope `comptime {}` block is analyzed for its side effects, so illegal behavior inside it is caught as the compiler's comptime-unit analysis does.
test "comptime scope: a container comptime block is evaluated" {
    try compliance.check(a, &.{
        .{ .src = &.{"comptime { _ = @as(u8, 300); }"}, .reject = true },
        .{ .src = &.{"comptime { _ = @as(?i32, null).?; }"}, .reject = true },
        .{ .src = &.{"comptime { const p: *u8 = undefined; _ = p.*; }"}, .reject = true },
        .{ .src = &.{"comptime { var arr: [2]u8 = undefined; arr[5] = 1; }"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"comptime { _ = @as(?i32, null).?; }"}, "unable to unwrap null");
}

// A nested container reads an enclosing declaration through a closure capture, which arises once the outer container is declared in a runtime function body.
test "comptime scope: a nested container captures an enclosing declaration" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { const x: u8 = 9; const A = struct { const y: u8 = x; }; }; break :blk S.A.y; }"},
            .want = compliance.want(blk: {
                const S = struct {
                    const x: u8 = 9;
                    const A = struct {
                        const y: u8 = x;
                    };
                };
                break :blk S.A.y;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { const x: u8 = 5; const A = struct { const B = struct { const z: u8 = x + 1; }; }; }; break :blk S.A.B.z; }"},
            .want = compliance.want(blk: {
                const S = struct {
                    const x: u8 = 5;
                    const A = struct {
                        const B = struct {
                            const z: u8 = x + 1;
                        };
                    };
                };
                break :blk S.A.B.z;
            }),
        },
    });
}

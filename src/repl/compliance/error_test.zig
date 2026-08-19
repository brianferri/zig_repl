const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: an error value widens into a superset error type" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const e: anyerror = error.Boom; break :blk e; }"},
            .want = compliance.want(blk: {
                const e: anyerror = error.Boom;
                break :blk e;
            }),
        },
        .{
            .src = &.{"blk: { const S = error{ A, B }; const e: S = error.A; const w: anyerror = e; break :blk w; }"},
            .want = compliance.want(blk: {
                const S = error{ A, B };
                const e: S = error.A;
                const w: anyerror = e;
                break :blk w;
            }),
        },
    });
}

test "compliance: `||` merges error sets" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const E = error{A} || error{B}; const e: E = error.B; break :blk @errorName(e)[0]; }"},
            .want = compliance.want(blk: {
                const E = error{A} || error{B};
                const e: E = error.B;
                break :blk @errorName(e)[0];
            }),
        },
        .{
            .src = &.{"blk: { const E = error{A} || error{ A, C }; const e: E = error.C; break :blk @errorName(e)[0]; }"},
            .want = compliance.want(blk: {
                const E = error{A} || error{ A, C };
                const e: E = error.C;
                break :blk @errorName(e)[0];
            }),
        },
        .{
            .src = &.{"blk: { const x = true || false; break :blk x; }"},
            .reject = true,
        },
    });
}

test "compliance: error values and set/union types render as zig prints" {
    try compliance.check(a, &.{
        .{ .src = &.{"error.Foo"}, .want = compliance.want(error.Foo) },
        .{ .src = &.{"error{Foo, Bar}"}, .want = compliance.want(error{ Foo, Bar }) },
        .{ .src = &.{"error{Charlie, Alpha, Bravo}"}, .want = compliance.want(error{ Charlie, Alpha, Bravo }) },
        .{ .src = &.{"error{Z,Y,X,W,V,U,T,S,R,Q,P,O,N,M,L,K,J,I,H,G,F,E,D,C,B,A}"}, .want = compliance.want(error{ Z, Y, X, W, V, U, T, S, R, Q, P, O, N, M, L, K, J, I, H, G, F, E, D, C, B, A }) },
        .{ .src = &.{"error{Bad}!u32"}, .want = compliance.want(error{Bad}!u32) },
        .{ .src = &.{"@as(error{Bad}!u32, error.Bad)"}, .want = compliance.want(@as(error{Bad}!u32, error.Bad)) },
        .{ .src = &.{"@as(error{Bad}!u32, 42)"}, .want = compliance.want(@as(error{Bad}!u32, 42)) },
        .{ .src = &.{"error{Worse,Bad}!i64"}, .want = compliance.want(error{ Worse, Bad }!i64) },
    });
}

test "compliance: cross-line error set and union round-trips" {
    try compliance.check(a, &.{
        .{
            .src = &.{ "const E = error{Oops};", "const EU = E!u8;", "EU" },
            .want = compliance.want(blk: {
                const E = error{Oops};
                const EU = E!u8;
                break :blk EU;
            }),
        },
        .{
            .src = &.{ "const E = error{Oops};", "const EU = E!u8;", "@as(EU, error.Oops)" },
            .want = compliance.want(blk: {
                const E = error{Oops};
                const EU = E!u8;
                break :blk @as(EU, error.Oops);
            }),
        },
        .{
            .src = &.{ "const E = error{Oops};", "const EU = E!u8;", "@as(EU, 7)" },
            .want = compliance.want(blk: {
                const E = error{Oops};
                const EU = E!u8;
                break :blk @as(EU, 7);
            }),
        },
        .{
            .src = &.{ "const x: u32 = 100;", "x + 5" },
            .want = compliance.want(blk: {
                const x: u32 = 100;
                break :blk x + 5;
            }),
        },
    });
}

test "compliance: catch unwraps error unions" {
    try compliance.check(a, &.{
        .{ .src = &.{"@as(error{Bad}!u32, error.Bad) catch |e| e"}, .want = compliance.want(@as(error{Bad}!u32, error.Bad) catch |e| e) },
        .{ .src = &.{"@as(error{Bad}!u32, error.Bad) catch @as(u32, 0)"}, .want = compliance.want(@as(error{Bad}!u32, error.Bad) catch @as(u32, 0)) },
        .{ .src = &.{"@as(error{Bad}!u32, 99) catch @as(u32, 0)"}, .want = compliance.want(@as(error{Bad}!u32, 99) catch @as(u32, 0)) },
        .{ .src = &.{"@as(error{Bad}!u32, 99) catch |e| e"}, .want = compliance.want(@as(error{Bad}!u32, 99) catch |e| e) },
        .{
            .src = &.{ "const E = error{Bad};", "const EU = E!u32;", "const x: EU = error.Bad;", "x catch |e| e" },
            .want = compliance.want(blk: {
                const E = error{Bad};
                const EU = E!u32;
                const x: EU = error.Bad;
                break :blk x catch |e| e;
            }),
        },
        .{
            .src = &.{ "const E = error{Bad};", "const EU = E!u32;", "const y: EU = 42;", "y catch @as(u32, 0)" },
            .want = compliance.want(blk: {
                const E = error{Bad};
                const EU = E!u32;
                const y: EU = 42;
                break :blk y catch @as(u32, 0);
            }),
        },
    });
}

test "compliance: @intFromError / @errorFromInt round-trip" {
    try compliance.check(a, &.{
        .{ .src = &.{"@errorFromInt(@intFromError(error.Bar))"}, .want = compliance.want(@errorFromInt(@intFromError(error.Bar))) },
    });
    try compliance.expectDiagnostic(a, &.{"@errorFromInt(0)"}, "represents no error");
}

test "compliance: @errorCast recasts across error sets and unions" {
    // @errorCast takes one argument; its destination is the result-location type,
    // supplied here by the enclosing @as.
    try compliance.check(a, &.{
        // Widen a subset into a superset, and to anyerror.
        .{ .src = &.{"@as(error{ A, B, C }, @errorCast(@as(error{ A, B }, error.A)))"}, .want = compliance.want(@as(error{ A, B, C }, @errorCast(@as(error{ A, B }, error.A)))) },
        .{ .src = &.{"@as(anyerror, @errorCast(@as(error{A}, error.A)))"}, .want = compliance.want(@as(anyerror, @errorCast(@as(error{A}, error.A)))) },
        // Narrow a superset to a subset the value belongs to.
        .{ .src = &.{"@as(error{A}, @errorCast(@as(error{ A, B }, error.A)))"}, .want = compliance.want(@as(error{A}, @errorCast(@as(error{ A, B }, error.A)))) },
        // Error set -> error union (the value wraps as the error arm).
        .{ .src = &.{"@as(error{A}!u8, @errorCast(@as(error{A}, error.A)))"}, .want = compliance.want(@as(error{A}!u8, @errorCast(@as(error{A}, error.A)))) },
        // Error union -> error union: error arm and payload arm both recast.
        .{ .src = &.{"@as(error{ A, B }!u8, @errorCast(@as(error{A}!u8, error.A)))"}, .want = compliance.want(@as(error{ A, B }!u8, @errorCast(@as(error{A}!u8, error.A)))) },
        .{ .src = &.{"@as(error{ A, B }!u8, @errorCast(@as(error{A}!u8, 5)))"}, .want = compliance.want(@as(error{ A, B }!u8, @errorCast(@as(error{A}!u8, 5)))) },
        // An optional destination peels one layer (.remove_opt): the cast targets
        // the error set, then the outer @as re-wraps the optional.
        .{ .src = &.{"@as(?error{ A, B }, @errorCast(@as(error{A}, error.A)))"}, .want = compliance.want(@as(?error{ A, B }, @errorCast(@as(error{A}, error.A)))) },
        // Rejections: non-error destination, EU -> error set, payload mismatch,
        // disjoint sets, and a value outside an overlapping destination set.
        .{ .src = &.{"@as(u8, @errorCast(error.A))"}, .reject = true },
        .{ .src = &.{"@as(error{A}, @errorCast(@as(error{A}!u8, error.A)))"}, .reject = true },
        .{ .src = &.{"@as(error{A}!u16, @errorCast(@as(error{A}!u8, error.A)))"}, .reject = true },
        .{ .src = &.{"@as(error{B}, @errorCast(@as(error{A}, error.A)))"}, .reject = true },
        .{ .src = &.{"@as(error{ A, C }, @errorCast(@as(error{ A, B }, error.B)))"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"@as(error{ A, C }, @errorCast(@as(error{ A, B }, error.B)))"}, "not a member of error set");
    try compliance.expectDiagnostic(a, &.{"@as(error{B}, @errorCast(@as(error{A}, error.A)))"}, "have no common errors");
    try compliance.expectDiagnostic(a, &.{"@as(error{A}!u16, @errorCast(@as(error{A}!u8, error.A)))"}, "payload types of error unions must match");
}

// Equality of error sets folds on the error name; error-union vs error-set unwraps the code, and a
// payload never equals an error -- bool_false for both == and != (op-independent), matching Zig.
test "compliance: error-set and error-union equality" {
    try compliance.check(a, &.{
        .{ .src = &.{"error.A == error.B"}, .want = compliance.want(error.A == error.B) },
        .{ .src = &.{"error.A == error.A"}, .want = compliance.want(error.A == error.A) },
        .{ .src = &.{"error.A != error.B"}, .want = compliance.want(error.A != error.B) },
        .{ .src = &.{"blk: { const z: anyerror!i32 = error.A; break :blk z == error.A; }"}, .want = compliance.want(blk: {
            const z: anyerror!i32 = error.A;
            break :blk z == error.A;
        }) },
        .{ .src = &.{"blk: { const z: anyerror!i32 = error.A; break :blk z != error.B; }"}, .want = compliance.want(blk: {
            const z: anyerror!i32 = error.A;
            break :blk z != error.B;
        }) },
        .{ .src = &.{"blk: { const y: anyerror!i32 = 5; break :blk y == error.A; }"}, .want = compliance.want(blk: {
            const y: anyerror!i32 = 5;
            break :blk y == error.A;
        }) },
        .{ .src = &.{"blk: { const y: anyerror!i32 = 5; break :blk y != error.A; }"}, .want = compliance.want(blk: {
            const y: anyerror!i32 = 5;
            break :blk y != error.A;
        }) },
    });
}

test "compliance: member access on an error set type yields the error value" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const E = error{ A, B }; break :blk @intFromError(E.B) == @intFromError(error.B); }"}, .want = compliance.want(blk: {
            const E = error{ A, B };
            break :blk @intFromError(E.B) == @intFromError(error.B);
        }) },
        .{ .src = &.{"blk: { const E = error{ A, B }; const e: E = E.A; break :blk e == error.A; }"}, .want = compliance.want(blk: {
            const E = error{ A, B };
            const e: E = E.A;
            break :blk e == error.A;
        }) },
        // `anyerror.name` mints (or reuses) a global error.
        .{ .src = &.{"blk: { const e = anyerror.Whatever; break :blk e == error.Whatever; }"}, .want = compliance.want(blk: {
            const e = anyerror.Whatever;
            break :blk e == error.Whatever;
        }) },
        // A name outside the set is rejected.
        .{ .src = &.{"blk: { const E = error{A}; break :blk E.C; }"}, .reject = true },
    });
}

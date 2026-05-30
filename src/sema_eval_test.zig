//! Lives at src/ rather than src/sema/ so it can import from front/ and
//! sema/ both; Zig blocks cross-directory imports inside one subdir.

const std = @import("std");
const testing = std.testing;

const Pipeline = @import("front/Pipeline.zig");
const Sema = @import("sema/Sema.zig");
const Session = @import("Session.zig");
const InternPool = @import("sema/InternPool.zig");
const Value = @import("sema/Value.zig");

fn evalSource(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    diag_buf: []u8,
) !Value {
    var result = try Pipeline.run(gpa, source);
    defer result.deinit(gpa);

    try testing.expect(!result.hasParseErrors());
    try testing.expect(!result.hasZirErrors());

    const ns = try intern_pool.createNamespace(gpa, .none);
    var session = Session.initForTest(gpa, intern_pool, ns);
    defer session.deinit();

    var writer = std.Io.Writer.fixed(diag_buf);
    const maybe_value = try Sema.analyze(&session, result.zir, &writer);
    return maybe_value orelse error.NoValue;
}

fn expectEvalDecimal(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    expected: []const u8,
) !void {
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, intern_pool, source, &diag_buf);
    const key = intern_pool.indexToKey(value.index);
    try testing.expect(key == .int);

    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const big = key.int.storage.toBigInt(&space);
    const decimal = try big.toStringAlloc(gpa, 10, .lower);
    defer gpa.free(decimal);
    try testing.expectEqualStrings(expected, decimal);
}

test "int literal fitting in u64" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "42", "42");
    try expectEvalDecimal(gpa, &pool, "1234567890", "1234567890");
}

test "int_big literal: 2^128 round-trip" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const two_to_128 = "340282366920938463463374607431768211456";
    try expectEvalDecimal(gpa, &pool, two_to_128, two_to_128);
}

test "int_big literal: 2^256 round-trip" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const two_to_256 =
        "115792089237316195423570985008687907853269984665640564039457584007913129639936";
    try expectEvalDecimal(gpa, &pool, two_to_256, two_to_256);
}

test "negate composes with int_big" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const negated = "-340282366920938463463374607431768211456";
    try expectEvalDecimal(gpa, &pool, negated, negated);
}

test "arithmetic crosses the u64/int_big boundary" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // u64.max + 1 promotes to a 2-limb result on 64-bit hosts.
    try expectEvalDecimal(gpa, &pool, "18446744073709551615 + 1", "18446744073709551616");
    // Multiplying two values that exceed u64.
    try expectEvalDecimal(
        gpa,
        &pool,
        "340282366920938463463374607431768211456 * 2",
        "680564733841876926926749214863536422912",
    );
}

test "division returns sign-correct results" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "@divTrunc(-7, 2)", "-3");
    try expectEvalDecimal(gpa, &pool, "@divFloor(-7, 2)", "-4");
    try expectEvalDecimal(gpa, &pool, "@mod(-7, 2)", "1");
    try expectEvalDecimal(gpa, &pool, "@rem(-7, 2)", "-1");
}

fn expectEvalBool(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    expected: bool,
) !void {
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, intern_pool, source, &diag_buf);
    const expected_index: InternPool.Index = if (expected) .bool_true else .bool_false;
    try testing.expectEqual(expected_index, value.index);
}

test "comparison operators yield the well-known bool indices" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "1 < 2", true);
    try expectEvalBool(gpa, &pool, "2 < 2", false);
    try expectEvalBool(gpa, &pool, "2 <= 2", true);
    try expectEvalBool(gpa, &pool, "2 == 2", true);
    try expectEvalBool(gpa, &pool, "2 != 2", false);
    try expectEvalBool(gpa, &pool, "3 >= 2", true);
    try expectEvalBool(gpa, &pool, "3 > 2", true);
}

test "if expression selects then branch" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "if (true) 10 else 20", "10");
    try expectEvalDecimal(gpa, &pool, "if (1 < 2) 100 else 200", "100");
}

test "if expression selects else branch" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "if (false) 10 else 20", "20");
    try expectEvalDecimal(gpa, &pool, "if (2 < 1) 100 else 200", "200");
}

test "if expression composes with arithmetic" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "if (true) 1 + 2 else 9", "3");
    try expectEvalDecimal(gpa, &pool, "(if (1 < 2) 10 else 20) + 5", "15");
}

test "nested if expressions" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "if (1 == 1) if (2 > 1) 7 else 8 else 9", "7");
    try expectEvalDecimal(gpa, &pool, "if (1 == 1) if (2 < 1) 7 else 8 else 9", "8");
    try expectEvalDecimal(gpa, &pool, "if (1 != 1) if (2 > 1) 7 else 8 else 9", "9");
}

test "if / else if chains" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // else-if desugars to else { if ... }; exercises the recursive condbr
    // path through the picked else-body.
    const ladder = "if (false) 1 else if (false) 2 else if (true) 3 else 4";
    try expectEvalDecimal(gpa, &pool, ladder, "3");
}

test "labeled block as expression" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // `blk: { break :blk N; }` exercises block / break_inline directly,
    // without an `if` wrapper.
    try expectEvalDecimal(gpa, &pool, "blk: { break :blk 42; }", "42");
    try expectEvalDecimal(gpa, &pool, "blk: { break :blk 1 + 2; }", "3");
}

fn expectEvalTypedDecimal(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    expected_type: InternPool.Index,
    expected_decimal: []const u8,
) !void {
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, intern_pool, source, &diag_buf);
    const key = intern_pool.indexToKey(value.index);
    try testing.expect(key == .int);
    try testing.expectEqual(expected_type, key.int.ty);

    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const big = key.int.storage.toBigInt(&space);
    const decimal = try big.toStringAlloc(gpa, 10, .lower);
    defer gpa.free(decimal);
    try testing.expectEqualStrings(expected_decimal, decimal);
}

fn expectEvalFails(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    expected_diagnostic_substring: []const u8,
) !void {
    var result = try Pipeline.run(gpa, source);
    defer result.deinit(gpa);

    const ns = try intern_pool.createNamespace(gpa, .none);
    var session = Session.initForTest(gpa, intern_pool, ns);
    defer session.deinit();

    var diag_buf: [4096]u8 = undefined;
    var writer = std.Io.Writer.fixed(&diag_buf);
    const sema_result = Sema.analyze(&session, result.zir, &writer);
    try testing.expectError(error.AnalysisFail, sema_result);

    const written = diag_buf[0 .. writer.buffer.len - writer.unusedCapacityLen()];
    try testing.expect(std.mem.indexOf(u8, written, expected_diagnostic_substring) != null);
}

test "@as coerces comptime_int to fixed-width int and stores the type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(u32, 5)", .u32_type, "5");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i32, -100)", .i32_type, "-100");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u64, 1234567890)", .u64_type, "1234567890");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i8, -128)", .i8_type, "-128");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 255)", .u8_type, "255");
}

test "@as identity coercion is a free passthrough" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // comptime_int -> comptime_int (identity) was the original supported case.
    try expectEvalDecimal(gpa, &pool, "@as(comptime_int, 42)", "42");
}

test "@as rejects values that don't fit in the target int type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalFails(gpa, &pool, "@as(u8, 256)", "does not fit in u8");
    try expectEvalFails(gpa, &pool, "@as(i8, 128)", "does not fit in i8");
    try expectEvalFails(gpa, &pool, "@as(u32, -1)", "does not fit in u32");
}

test "array_init rejects elements that don't fit the element type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalFails(gpa, &pool, "[_]u3{8}", "does not fit in u3");
    try expectEvalFails(gpa, &pool, "[_]u8{256}", "does not fit in u8");
    try expectEvalFails(gpa, &pool, "[_]i4{8}", "does not fit in i4"); // i4 holds -8..7
    try expectEvalFails(gpa, &pool, "[_]u8{-1}", "does not fit in u8");
}

test "if branches with negative results" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "if (3 < 0) 3 else -3", "-3");
    try expectEvalDecimal(gpa, &pool, "if (-7 < 0) -1 else 1", "-1");
}

test "if-as-value inside bool short-circuit" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // The rhs of `and` is a ZIR body; an if inside it exercises a
    // condbr nested under bool_br.
    try expectEvalBool(gpa, &pool, "true and (if (1 < 2) true else false)", true);
    try expectEvalBool(gpa, &pool, "true and (if (1 > 2) true else false)", false);
    try expectEvalBool(gpa, &pool, "false or (if (1 < 2) true else false)", true);
}

test "bool_not flips well-known bool values" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "!true", false);
    try expectEvalBool(gpa, &pool, "!false", true);
    try expectEvalBool(gpa, &pool, "!!true", true);
}

test "short-circuit and / or cover the full truth tables" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "true and true", true);
    try expectEvalBool(gpa, &pool, "true and false", false);
    try expectEvalBool(gpa, &pool, "false and true", false);
    try expectEvalBool(gpa, &pool, "false and false", false);

    try expectEvalBool(gpa, &pool, "true or true", true);
    try expectEvalBool(gpa, &pool, "true or false", true);
    try expectEvalBool(gpa, &pool, "false or true", true);
    try expectEvalBool(gpa, &pool, "false or false", false);
}

test "short-circuit composes with comparisons" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "1 < 2 and 3 < 4", true);
    try expectEvalBool(gpa, &pool, "1 < 2 and 4 < 3", false);
    try expectEvalBool(gpa, &pool, "1 > 2 or 3 < 4", true);
    try expectEvalBool(gpa, &pool, "1 > 2 or 3 > 4", false);
}

test "shifts on comptime_int" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "1 << 5", "32");
    try expectEvalDecimal(gpa, &pool, "1 << 128", "340282366920938463463374607431768211456");
    try expectEvalDecimal(gpa, &pool, "1024 >> 3", "128");
    try expectEvalDecimal(gpa, &pool, "0xFF00 >> 8", "255");
}

test "bitwise binary ops on comptime_int" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalDecimal(gpa, &pool, "0b1100 & 0b1010", "8"); // 0b1000
    try expectEvalDecimal(gpa, &pool, "0b1100 | 0b1010", "14"); // 0b1110
    try expectEvalDecimal(gpa, &pool, "0b1100 ^ 0b1010", "6"); // 0b0110
    try expectEvalDecimal(gpa, &pool, "0xFF & 0x0F", "15");
    try expectEvalDecimal(gpa, &pool, "0xCAFE ^ 0xCAFE", "0");
}

test "comparison handles negatives and big ints" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "-7 < 0", true);
    try expectEvalBool(gpa, &pool, "-7 < -3", true);
    try expectEvalBool(gpa, &pool, "-3 > -7", true);
    try expectEvalBool(
        gpa,
        &pool,
        "340282366920938463463374607431768211456 > 18446744073709551615",
        true,
    );
}

fn expectEvalComptimeFloat(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    expected: f128,
) !void {
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, intern_pool, source, &diag_buf);
    const key = intern_pool.indexToKey(value.index);
    try testing.expect(key == .float);
    try testing.expectEqual(InternPool.Index.comptime_float_type, key.float.ty);
    try testing.expectEqual(expected, key.float.storage.f128);
}

fn expectEvalTypedFloat(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    expected_type: InternPool.Index,
    expected_bits: u128,
) !void {
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, intern_pool, source, &diag_buf);
    const key = intern_pool.indexToKey(value.index);
    try testing.expect(key == .float);
    try testing.expectEqual(expected_type, key.float.ty);

    const actual_bits: u128 = switch (key.float.storage) {
        .f16 => |v| @as(u16, @bitCast(v)),
        .f32 => |v| @as(u32, @bitCast(v)),
        .f64 => |v| @as(u64, @bitCast(v)),
        .f80 => |v| @as(u80, @bitCast(v)),
        .f128 => |v| @as(u128, @bitCast(v)),
    };
    try testing.expectEqual(expected_bits, actual_bits);
}

test "float arithmetic on comptime_float" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalComptimeFloat(gpa, &pool, "1.5 + 2.5", 4.0);
    try expectEvalComptimeFloat(gpa, &pool, "10.0 - 3.5", 6.5);
    try expectEvalComptimeFloat(gpa, &pool, "2.0 * 3.5", 7.0);
    try expectEvalComptimeFloat(gpa, &pool, "7.5 / 2.5", 3.0);
    try expectEvalComptimeFloat(gpa, &pool, "@divTrunc(7.5, 2.5)", 3.0);
    try expectEvalComptimeFloat(gpa, &pool, "@divFloor(-7.5, 2.5)", -3.0);
    try expectEvalComptimeFloat(gpa, &pool, "@divExact(6.0, 2.0)", 3.0);
    try expectEvalComptimeFloat(gpa, &pool, "@mod(7.5, 2.5)", 0.0);
}

test "float division errors surface at Sema" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalFails(gpa, &pool, "1.5 / 0.0", "division by zero");
    try expectEvalFails(gpa, &pool, "@divExact(7.0, 2.0)", "remainder is non-zero");
}

test "float comparison yields the well-known bool indices" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "1.5 < 2.5", true);
    try expectEvalBool(gpa, &pool, "1.5 == 1.5", true);
    try expectEvalBool(gpa, &pool, "3.14 != 3.14", false);
    try expectEvalBool(gpa, &pool, "-1.5 > -2.5", true);
}

test "@as coerces comptime_float to fixed-width float and stores the type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // 1.5 has an exact representation in every IEEE-754 width.
    try expectEvalTypedFloat(gpa, &pool, "@as(f16, 1.5)", .f16_type, @as(u16, @bitCast(@as(f16, 1.5))));
    try expectEvalTypedFloat(gpa, &pool, "@as(f32, 1.5)", .f32_type, @as(u32, @bitCast(@as(f32, 1.5))));
    try expectEvalTypedFloat(gpa, &pool, "@as(f64, 1.5)", .f64_type, @as(u64, @bitCast(@as(f64, 1.5))));
    try expectEvalTypedFloat(gpa, &pool, "@as(f128, 1.5)", .f128_type, @as(u128, @bitCast(@as(f128, 1.5))));
}

test "fixed-width float arithmetic at every width" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // f32 path
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, 1.5) + @as(f32, 2.5)",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 4.0))),
    );
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, 10.0) - @as(f32, 3.5)",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 6.5))),
    );
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, 7.5) / @as(f32, 2.5)",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 3.0))),
    );

    // f64 path
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f64, 2.0) * @as(f64, 3.5)",
        .f64_type,
        @as(u64, @bitCast(@as(f64, 7.0))),
    );
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@divTrunc(@as(f64, 7.5), @as(f64, 2.5))",
        .f64_type,
        @as(u64, @bitCast(@as(f64, 3.0))),
    );

    // f128 path
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f128, 1.0) + @as(f128, 1.0)",
        .f128_type,
        @as(u128, @bitCast(@as(f128, 2.0))),
    );
}

test "fixed-width float comparison and negation" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "@as(f32, 1.5) < @as(f32, 2.5)", true);
    try expectEvalBool(gpa, &pool, "@as(f64, 3.14) == @as(f64, 3.14)", true);
    try expectEvalBool(gpa, &pool, "@as(f32, 1.0) != @as(f32, 1.0)", false);
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "-@as(f32, 1.5)",
        .f32_type,
        @as(u32, @bitCast(@as(f32, -1.5))),
    );
}

test "@floatCast widens and narrows between float widths" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Comptime_float -> any fixed-width
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, @floatCast(1.5))",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 1.5))),
    );

    // f32 -> f64 (lossless widening)
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f64, @floatCast(@as(f32, 1.5)))",
        .f64_type,
        @as(u64, @bitCast(@as(f64, @as(f32, 1.5)))),
    );

    // f64 -> f32 (narrowing, precision loss permitted). The expected
    // bits are computed via `@floatCast` rather than `@as` because Zig's
    // comptime guard would reject the latter for a value f32 cannot
    // represent exactly.
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, @floatCast(@as(f64, 3.14)))",
        .f32_type,
        @as(u32, @bitCast(@as(f32, @floatCast(@as(f64, 3.14))))),
    );
}

test "@intFromFloat truncates toward zero and range-checks" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(i32, @intFromFloat(3.7))", .i32_type, "3");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i32, @intFromFloat(-3.7))", .i32_type, "-3");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, @intFromFloat(255.999))", .u8_type, "255");
    try expectEvalDecimal(gpa, &pool, "@as(comptime_int, @intFromFloat(1234567890.5))", "1234567890");

    try expectEvalFails(gpa, &pool, "@as(u8, @intFromFloat(256.0))", "does not fit in u8");
    try expectEvalFails(gpa, &pool, "@as(i32, @intFromFloat(1.0e30))", "does not fit in i32");
}

test "@floatFromInt rounds to nearest-even at the destination width" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, @floatFromInt(5))",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 5.0))),
    );
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f64, @floatFromInt(-100))",
        .f64_type,
        @as(u64, @bitCast(@as(f64, -100.0))),
    );
    // 16777217 (= 2^24 + 1) is not representable exactly in f32 (24-bit
    // mantissa); nearest-even rounds to 16777216 (= 2^24).
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, @floatFromInt(16777217))",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 16777216.0))),
    );
}

test "mixed-width float arith widens to the wider float type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // f32 + f64 -> f64 (compiler: `resolvePeerTypes` picks the wider).
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, 1.5) + @as(f64, 2.5)",
        .f64_type,
        @as(u64, @bitCast(@as(f64, 4.0))),
    );
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f64, 1.0) - @as(f32, 0.5)",
        .f64_type,
        @as(u64, @bitCast(@as(f64, 0.5))),
    );
}

test "fixed-width int + fixed-width float resolves to the fixed-width float" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // `@as(f32, 1.5) + @as(i32, 2)` -> 3.5 f32 in real Zig: peer
    // resolution picks `fixed_float`, coerces the i32 to f32, computes.
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, 1.5) + @as(i32, 2)",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 3.5))),
    );
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(i32, 2) + @as(f32, 1.5)",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 3.5))),
    );
}

test "@as fixed-width int to fixed-width float is permitted" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, @as(i32, 5))",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 5.0))),
    );
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f64, @as(i32, 1000000))",
        .f64_type,
        @as(u64, @bitCast(@as(f64, 1000000.0))),
    );
}

test "fixed-width int + comptime_float is rejected" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Real Zig: "incompatible types: 'i32' and 'comptime_float'". Our
    // diagnostic groups this with the still-pending fixed-width-int
    // arith axis.
    try expectEvalFails(gpa, &pool, "@as(i32, 5) + 1.5", "incompatible numeric operands");
    try expectEvalFails(gpa, &pool, "1.5 + @as(i32, 5)", "incompatible numeric operands");
}

test "fixed-width int arithmetic same width" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(i32, 1) + @as(i32, 2)", .i32_type, "3");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u32, 10) - @as(u32, 3)", .u32_type, "7");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i32, 5) * @as(i32, 6)", .i32_type, "30");
    try expectEvalTypedDecimal(gpa, &pool, "@divTrunc(@as(i32, 7), @as(i32, 2))", .i32_type, "3");
}

test "fixed-width int + comptime_int range-checks via peer resolution" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(i32, 5) + 1", .i32_type, "6");
    try expectEvalTypedDecimal(gpa, &pool, "1 + @as(i32, 5)", .i32_type, "6");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 100) + 50", .u8_type, "150");

    // Overflow at the fixed width is a comptime error in real Zig
    // ("overflow of integer type 'u8' with value '300'"); we surface
    // the same condition via the post-arith range check.
    try expectEvalFails(gpa, &pool, "@as(u8, 200) + @as(u8, 100)", "does not fit in u8");
}

test "fixed-width int peer resolution across widths and signedness" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Same signedness: wider wins.
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 5) + @as(u16, 10)", .u16_type, "15");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i8, 5) + @as(i16, 100)", .i16_type, "105");

    // Mixed signedness, signed strictly wider: signed wins.
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 5) + @as(i16, 100)", .i16_type, "105");

    // Mixed signedness, unsigned strictly wider: unsigned wins (compiler
    // legacy compat -- both operands here are comptime-known).
    try expectEvalTypedDecimal(gpa, &pool, "@as(u16, 5) + @as(i8, 100)", .u16_type, "105");
}

test "fixed-width int comparison across widths" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalBool(gpa, &pool, "@as(i32, 5) < @as(i32, 10)", true);
    try expectEvalBool(gpa, &pool, "@as(u16, 1000) > @as(u8, 200)", true);
    try expectEvalBool(gpa, &pool, "@as(i32, -3) == -3", true);
    try expectEvalBool(gpa, &pool, "@as(u8, 5) == @as(i32, 5)", true);
}

test "wrapping arith on fixed-width ints" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 200) +% @as(u8, 100)", .u8_type, "44");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 10) -% @as(u8, 20)", .u8_type, "246");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 100) *% @as(u8, 5)", .u8_type, "244");
    // Signed wrap matches two's-complement.
    try expectEvalTypedDecimal(gpa, &pool, "@as(i8, 127) +% @as(i8, 1)", .i8_type, "-128");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i8, -128) -% @as(i8, 1)", .i8_type, "127");
}

test "saturating arith on fixed-width ints" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 200) +| @as(u8, 100)", .u8_type, "255");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 10) -| @as(u8, 20)", .u8_type, "0");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 100) *| @as(u8, 5)", .u8_type, "255");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i8, 100) +| @as(i8, 100)", .i8_type, "127");
    try expectEvalTypedDecimal(gpa, &pool, "@as(i8, -100) -| @as(i8, 100)", .i8_type, "-128");
}

test "fixed-width bitwise on fixed-width ints" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(u16, 1000) & @as(u16, 0xff)", .u16_type, "232");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 0xf0) | @as(u8, 0x0f)", .u8_type, "255");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 0xff) ^ @as(u8, 0x0f)", .u8_type, "240");
}

test "fixed-width shifts and shift variants" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 1) << 7", .u8_type, "128");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 0xff) >> 4", .u8_type, "15");
    // Saturating shl: 1 << 8 would overflow u8; sat clamps to 255.
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 1) <<| 8", .u8_type, "255");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, 1) <<| 7", .u8_type, "128");
}

test "target-conditioned int types participate in peer resolution" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // usize + comptime_int -> usize; the int operand range-checks
    // against the host's pointer width via @typeInfo(usize).
    try expectEvalTypedDecimal(gpa, &pool, "@as(usize, 100) + 1", .usize_type, "101");
    try expectEvalTypedDecimal(gpa, &pool, "@as(c_int, 5) * 2", .c_int_type, "10");
    try expectEvalBool(gpa, &pool, "@as(usize, 100) > @as(c_int, 50)", true);
}

test "@intCast widens and narrows with range checks" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(u32, @intCast(@as(u8, 200)))", .u32_type, "200");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, @intCast(@as(u32, 200)))", .u8_type, "200");
    try expectEvalFails(gpa, &pool, "@as(u8, @intCast(@as(u32, 500)))", "does not fit in u8");
}

test "@truncate keeps low bits" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, @truncate(@as(u32, 0x1234)))", .u8_type, "52");
    try expectEvalTypedDecimal(gpa, &pool, "@as(u16, @truncate(@as(u32, 0x12345678)))", .u16_type, "22136");
    // u29 is a well-known Index so we can compare against it; truncate
    // keeps the low 29 bits of 0xffff_ffff which is 0x1fff_ffff.
    try expectEvalTypedDecimal(gpa, &pool, "@as(u29, @truncate(@as(u32, 0xffffffff)))", .u29_type, "536870911");
}

test "@bitCast reinterprets matching-width bits" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // f32 1.5 bit pattern is 0x3FC00000.
    try expectEvalTypedDecimal(gpa, &pool, "@as(u32, @bitCast(@as(f32, 1.5)))", .u32_type, "1069547520");
    try expectEvalTypedFloat(
        gpa,
        &pool,
        "@as(f32, @bitCast(@as(u32, 0x3fc00000)))",
        .f32_type,
        @as(u32, @bitCast(@as(f32, 1.5))),
    );
    // i8 -1 (two's-complement 0xff) re-tags as u8 255.
    try expectEvalTypedDecimal(gpa, &pool, "@as(u8, @bitCast(@as(i8, -1)))", .u8_type, "255");
}

/// Drive a type-expression through the full Pipeline + Sema + render,
/// asserting that the rendered name matches `expected`. Used for
/// ptr_type and (later) aggregate / function types.
fn expectEvalTypeName(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    source: []const u8,
    expected: []const u8,
) !void {
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, intern_pool, source, &diag_buf);

    var render_buf: [256]u8 = undefined;
    var render_writer = std.Io.Writer.fixed(&render_buf);
    try @import("render/Value.zig").render(value, intern_pool, &render_writer);

    const rendered_raw = render_buf[0 .. render_writer.buffer.len - render_writer.unusedCapacityLen()];
    const rendered = std.mem.trimEnd(u8, rendered_raw, "\n");
    try testing.expectEqualStrings(expected, rendered);
}

test "int_type: arbitrary widths construct and render across a sweep" {
    @setEvalBranchQuota(20000);
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Spans widths <=16 (well-known Inst.Refs) and wider (the
    // int_type handler) -- distinct paths that must agree.
    const widths = [_]u16{ 0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 69, 127, 128, 255, 420, 1000, 65535 };
    inline for (.{ "u", "i" }) |sign| {
        inline for (widths) |bits| {
            // `i0` is illegal ("signed integer cannot have bit width
            // 0"); `u0` is valid. Skip the one bad combination.
            if (bits == 0 and sign[0] == 'i') continue;
            const name = std.fmt.comptimePrint("{s}{d}", .{ sign, bits });
            try expectEvalTypeName(gpa, &pool, name, name);
        }
    }
}

test "int_type: arbitrary-width array type constructs and renders" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    inline for (.{ 3, 69, 420, 65535 }) |bits| {
        const src = std.fmt.comptimePrint("[4]u{d}", .{bits});
        const want = std.fmt.comptimePrint("[4]u{d}", .{bits});
        try expectEvalTypeName(gpa, &pool, src, want);
    }
}

test "ptr_type: e2e through Pipeline produces interned Key.ptr_type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Drive the expression through the full front end and confirm the
    // pool returns the expected Key shape, not just a rendered string.
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, &pool, "*const u8", &diag_buf);
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .ptr_type);
    try testing.expectEqual(InternPool.Index.u8_type, key.ptr_type.child);
    try testing.expectEqual(true, key.ptr_type.flags.is_const);
    try testing.expectEqual(InternPool.Key.PtrType.Size.one, key.ptr_type.flags.size);

    // Stage 1 dedup check at the e2e layer: same source twice gives
    // the same Index.
    const second = try evalSource(gpa, &pool, "*const u8", &diag_buf);
    try testing.expectEqual(value.index, second.index);
}

test "ptr_type: each size + qualifier renders the Zig surface name" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypeName(gpa, &pool, "*u8", "*u8");
    try expectEvalTypeName(gpa, &pool, "*const u8", "*const u8");
    try expectEvalTypeName(gpa, &pool, "*volatile u32", "*volatile u32");
    try expectEvalTypeName(gpa, &pool, "[*]u8", "[*]u8");
    try expectEvalTypeName(gpa, &pool, "[*]const u8", "[*]const u8");
    try expectEvalTypeName(gpa, &pool, "[]i32", "[]i32");
    try expectEvalTypeName(gpa, &pool, "[]const i32", "[]const i32");
    try expectEvalTypeName(gpa, &pool, "[*c]u8", "[*c]u8");
    // Nested pointer recurses through writeTypeName.
    try expectEvalTypeName(gpa, &pool, "*const [*]u8", "*const [*]u8");
    try expectEvalTypeName(gpa, &pool, "*const *const u32", "*const *const u32");
}

test "ptr_type integrates with @as as a destination type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // `@as(type, *const u8)` is the identity coercion: the operand is
    // already a value of type `type`, so we get back the same Index.
    try expectEvalTypeName(gpa, &pool, "@as(type, *const u8)", "*const u8");
    try expectEvalTypeName(gpa, &pool, "@as(type, [*]i32)", "[*]i32");

    // `@as(*const u8, undefined)` re-tags the untyped undef as a typed
    // undef of `*const u8`. The resulting Key.undef carries the
    // ptr_type Index.
    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, &pool, "@as(*const u8, undefined)", &diag_buf);
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .undef);
    const ty_key = pool.indexToKey(key.undef);
    try testing.expect(ty_key == .ptr_type);
    try testing.expectEqual(InternPool.Index.u8_type, ty_key.ptr_type.child);
}

test "cast builtins reject ptr_type destinations with their own diagnostic" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Each builtin uses `resolveDestType` so a ptr_type dest is now
    // *accepted* as a type Index -- the kind-specific check inside
    // the handler is what rejects the mismatch. Each one names its
    // own kind in the diagnostic, not "destination is not a type".
    try expectEvalFails(gpa, &pool, "@as(*const u8, @intCast(5))", "destination is not a supported int type");
    try expectEvalFails(gpa, &pool, "@as(*u8, @bitCast(@as(u64, 0)))", "operands must be fixed-width numeric types");
}

test "ptr_type: extensions we do not yet support fail with a structured diagnostic" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalFails(gpa, &pool, "[*:0]const u8", "sentinel-terminated pointers not yet supported");
    try expectEvalFails(gpa, &pool, "*align(8) u32", "align / address_space / bit_range not yet supported");
}

test "bit_not on fixed-width ints" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "~@as(u8, 5)", .u8_type, "250");
    try expectEvalTypedDecimal(gpa, &pool, "~@as(u8, 0)", .u8_type, "255");
    try expectEvalTypedDecimal(gpa, &pool, "~@as(i8, 0)", .i8_type, "-1");
    try expectEvalTypedDecimal(gpa, &pool, "~@as(i32, 100)", .i32_type, "-101");
    try expectEvalTypedDecimal(gpa, &pool, "~@as(u16, 0xff00)", .u16_type, "255");
}

test "negate_wrap on fixed-width ints" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // i8 -128 has no positive counterpart; -% wraps back to -128.
    try expectEvalTypedDecimal(gpa, &pool, "-%@as(i8, -128)", .i8_type, "-128");
    try expectEvalTypedDecimal(gpa, &pool, "-%@as(i8, 127)", .i8_type, "-127");
    try expectEvalTypedDecimal(gpa, &pool, "-%@as(u8, 200)", .u8_type, "56");
    try expectEvalTypedDecimal(gpa, &pool, "-%@as(i32, 0)", .i32_type, "0");
}

test "negate on fixed-width int now refits + overflows cleanly" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    try expectEvalTypedDecimal(gpa, &pool, "-@as(i32, 100)", .i32_type, "-100");
    // -minInt(i8) = 128 which overflows i8 (matches the compiler's
    // comptime overflow error).
    try expectEvalFails(gpa, &pool, "-@as(i8, -128)", "value does not fit in i8");
}

test "mixed comptime_int + comptime_float promotes via peer-type resolution" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Both orderings: the int side is promoted to comptime_float (f128
    // nearest-even) before the float kernel runs.
    try expectEvalComptimeFloat(gpa, &pool, "1 + 1.5", 2.5);
    try expectEvalComptimeFloat(gpa, &pool, "1.5 + 1", 2.5);
    try expectEvalComptimeFloat(gpa, &pool, "10 - 2.5", 7.5);
    try expectEvalComptimeFloat(gpa, &pool, "3 * 2.5", 7.5);
    try expectEvalComptimeFloat(gpa, &pool, "10 / 4.0", 2.5);
    try expectEvalComptimeFloat(gpa, &pool, "-3 + 0.5", -2.5);

    // Mixed comparison: the int side promotes the same way.
    try expectEvalBool(gpa, &pool, "1 < 1.5", true);
    try expectEvalBool(gpa, &pool, "2.5 > 2", true);
    try expectEvalBool(gpa, &pool, "1 == 1.0", true);
}

test "alloc/store/load: var read after init" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    // The REPL suppresses AstGen's "local variable is never mutated"
    // diagnostic at the front-end boundary (front/ZirErrors.zig), so a
    // never-mutated `var` is accepted; mutability is enforced at Sema
    // store time, not at parse time.
    try expectEvalTypedDecimal(gpa, &pool, "blk: { var x: u8 = 7; break :blk x; }", .u8_type, "7");
}

test "alloc/store/load: var initialised then overwritten" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    try expectEvalTypedDecimal(gpa, &pool, "blk: { var x: u8 = 7; x = 9; break :blk x; }", .u8_type, "9");
}

test "alloc/store/load: var mutation flows through load" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    try expectEvalTypedDecimal(gpa, &pool, "blk: { var x: u8 = 0; x = x + 1; break :blk x; }", .u8_type, "1");
    try expectEvalTypedDecimal(gpa, &pool, "blk: { var y: i32 = 100; y = y - 50; break :blk y; }", .i32_type, "50");
}

test "alloc/store/load: independent slots do not alias" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    try expectEvalTypedDecimal(
        gpa,
        &pool,
        "blk: { var a: u8 = 0; var b: u8 = 0; a = 1; b = 2; break :blk a + b; }",
        .u8_type,
        "3",
    );
}

test "alloc/store/load: wrap arith through a stored var" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    try expectEvalTypedDecimal(
        gpa,
        &pool,
        "blk: { var x: u8 = 200; x = x +% 100; break :blk x; }",
        .u8_type,
        "44",
    );
}

/// Multi-input session harness: runs each line through
/// Pipeline.runWithInjection + Sema.analyze, persisting bindings in
/// the supplied namespace. Returns the final line's evaluated Value
/// or null when the final line was a declaration.
fn evalSessionLines(
    gpa: std.mem.Allocator,
    pool: *InternPool,
    namespace: InternPool.NamespaceIndex,
    inputs: []const []const u8,
    diag_buf: []u8,
) !?Value {
    var session = Session.initForTest(gpa, pool, namespace);
    defer session.deinit();

    var last_value: ?Value = null;
    for (inputs) |source| {
        var result = try Pipeline.runWithInjection(gpa, source, pool, .init(namespace));
        var committed = false;
        defer if (!committed) result.deinit(gpa);

        try testing.expect(!result.hasParseErrors());
        try testing.expect(!result.hasZirErrors());

        var writer = std.Io.Writer.fixed(diag_buf);
        last_value = try Sema.analyze(&session, result.zir, &writer);
        try session.pipelines.append(gpa, result);
        committed = true;
    }
    return last_value;
}

test "decl: top-level const binds and is readable on the next line" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns, &.{
        "const x = 10;",
        "x",
    }, &diag_buf)).?;
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .int);
    try testing.expectEqual(@as(u64, 10), key.int.storage.u64);
}

test "decl: typed binding survives + participates in arith" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns, &.{
        "const y: i32 = 100;",
        "y + 5",
    }, &diag_buf)).?;
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .int);
    try testing.expectEqual(InternPool.Index.i32_type, key.int.ty);
    try testing.expectEqual(@as(i64, 105), key.int.storage.i64);
}

test "decl: multiple bindings across lines compose" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns, &.{
        "const a = 1;",
        "const b = 2;",
        "const c = 3;",
        "a + b + c",
    }, &diag_buf)).?;
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .int);
    try testing.expectEqual(@as(u64, 6), key.int.storage.u64);
}

test "decl: declaration-shape input returns null (no value to print)" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = try evalSessionLines(gpa, &pool, ns, &.{
        "const x = 10;",
    }, &diag_buf);
    try testing.expect(value == null);
}

test "decl: bindDecls populates the namespace with the right resolved value" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns_idx, &.{
        "const x: u32 = 42;",
    }, &diag_buf);

    // Top-level `const` without an explicit `pub` lives in
    // priv_decls (Zig file-scope semantics). lookupNav walks both
    // pub_decls and priv_decls so callers don't care which.
    const ns = pool.namespacePtr(ns_idx);
    const x_name = try pool.getOrPutString(gpa, "x");
    const nav_idx = ns.lookupNav(&pool, x_name).?;

    const nav = pool.getNav(nav_idx);
    try testing.expectEqual(x_name, nav.name);
    const resolved = nav.resolved.?;
    try testing.expectEqual(InternPool.Index.u32_type, resolved.type);
    try testing.expect(resolved.@"const");
    try testing.expectEqual(@as(u64, 42), pool.indexToKey(resolved.value).int.storage.u64);
}

test "decl: rebinding the same name fails with duplicate-member error" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    // First line binds successfully.
    _ = try evalSessionLines(gpa, &pool, ns, &.{"const x = 10;"}, &diag_buf);

    // Second line tries to rebind x; wrap-injection re-emits the
    // first binding, so AstGen rejects the new one with "duplicate
    // struct member name".
    var result = try Pipeline.runWithInjection(gpa, "const x = 20;", &pool, .init(ns));
    defer result.deinit(gpa);
    try testing.expect(result.hasZirErrors());
}

test "decl: a test decl binds into test_decls, not pub_decls" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns_idx, &.{
        "test \"addition is sound\" { return; }",
    }, &diag_buf);

    const ns = pool.namespacePtr(ns_idx);
    try testing.expectEqual(@as(usize, 0), ns.pub_decls.count());
    try testing.expectEqual(@as(usize, 1), ns.test_decls.items.len);

    const nav = pool.getNav(ns.test_decls.items[0]);
    try testing.expect(nav.resolved == null);
    try testing.expect(nav.analysis != null);
}

test "decl: comptime block binds into comptime_decls" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns_idx, &.{
        "comptime { }",
    }, &diag_buf);

    const ns = pool.namespacePtr(ns_idx);
    try testing.expectEqual(@as(usize, 1), ns.comptime_decls.items.len);
}

const Diagnostic = @import("render/Diagnostic.zig");

/// Run `source` through the same Pipeline + Diagnostic path the
/// REPL uses, capturing whatever the ZIR-error renderer would
/// surface to the user. The session is supplied by the caller so a
/// preceding line can establish a binding before this line tries to
/// shadow / rebind it.
fn renderZirDiagnostic(
    gpa: std.mem.Allocator,
    pool: *InternPool,
    namespace: InternPool.NamespaceIndex,
    source: []const u8,
    out_buf: []u8,
) ![]const u8 {
    var result = try Pipeline.runWithInjection(gpa, source, pool, .init(namespace));
    defer result.deinit(gpa);

    try testing.expect(result.hasZirErrors());

    var writer = std.Io.Writer.fixed(out_buf);
    try Diagnostic.renderZirErrors(gpa, result.zir, result.tree, result.userView(), &writer);

    return out_buf[0 .. writer.buffer.len - writer.unusedCapacityLen()];
}

test "diagnostic: shadow rejection renders main error in user frame" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    // Establish `w` in the session namespace.
    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns, &.{"const w = 10;"}, &diag_buf);

    // Next line tries to shadow `w` inside a block. AstGen rejects
    // with "local constant shadows declaration"; the note that
    // would normally point at the original declaration ("declared
    // here") anchors on the wrap-injected `const w: comptime_int =
    // undefined;` line. UserView.translate returns null for that
    // anchor and the note is suppressed -- the main error stands.
    var out_buf: [4096]u8 = undefined;
    const rendered = try renderZirDiagnostic(
        gpa,
        &pool,
        ns,
        "blk: { const w = 20; break :blk w; }",
        &out_buf,
    );

    try testing.expect(std.mem.indexOf(u8, rendered, "local constant shadows declaration") != null);
    // No misleading "declared here" note pointing at the wrap-injected
    // line -- our injection-anchor suppression dropped it.
    try testing.expectEqual(@as(?usize, null), std.mem.indexOf(u8, rendered, "declared here"));
}

test "decl: cross-line rebind preserves the original binding (silent-drop limitation)" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns, &.{"const z = 1;"}, &diag_buf);

    // Known Stage-2 limitation: cross-line rebind via wrap-injection
    // produces a ZIR "duplicate struct member name" error whose main
    // span anchors on the *injected* `const z: ... = undefined;`
    // line (the original occurrence from AstGen's perspective).
    // `UserView.translate` drops that span, so the whole error item
    // is discarded. The Diagnostic renderer surfaces a fallback
    // line so the user doesn't see silent failure; the semantic
    // contract is also pinned -- the original binding survives the
    // attempted rebind.
    var out_buf: [4096]u8 = undefined;
    const rendered = try renderZirDiagnostic(gpa, &pool, ns, "const z = 2;", &out_buf);

    // Fallback message surfaces -- no silent drop.
    try testing.expect(std.mem.indexOf(u8, rendered, "could not be located") != null);

    // Original binding still intact at value 1 -- AstGen rejected
    // the new decl, bindDecls never ran on it.
    const z_name = try pool.getOrPutString(gpa, "z");
    const nav_idx = pool.namespacePtr(ns).lookupNav(&pool, z_name).?;
    const resolved = pool.getNav(nav_idx).resolved.?;
    try testing.expectEqual(@as(u64, 1), pool.indexToKey(resolved.value).int.storage.u64);
}

test "error_set: error{Foo, Bar} interns as a sorted set type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, &pool, "error{Foo, Bar}", &diag_buf);
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .error_set_type);
    try testing.expectEqual(@as(usize, 2), key.error_set_type.names.len);

    // Names are sorted by their interned-string integer value, not
    // by lexicographic order or source order.
    const a = key.error_set_type.names[0];
    const b = key.error_set_type.names[1];
    try testing.expect(@intFromEnum(a) < @intFromEnum(b));
}

test "error_set: same membership dedups regardless of source ordering" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const v1 = try evalSource(gpa, &pool, "error{Foo, Bar}", &diag_buf);
    const v2 = try evalSource(gpa, &pool, "error{Bar, Foo}", &diag_buf);
    try testing.expectEqual(v1.index, v2.index);
}

test "error_set: distinct membership produces distinct indices" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const v1 = try evalSource(gpa, &pool, "error{Foo, Bar}", &diag_buf);
    const v2 = try evalSource(gpa, &pool, "error{Foo, Baz}", &diag_buf);
    try testing.expect(v1.index != v2.index);
}

test "error_value: error.Foo creates singleton set + err value" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, &pool, "error.Foo", &diag_buf);
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .err);

    // The value's type is a singleton error set containing only "Foo".
    const ty_key = pool.indexToKey(key.err.ty);
    try testing.expect(ty_key == .error_set_type);
    try testing.expectEqual(@as(usize, 1), ty_key.error_set_type.names.len);
    try testing.expectEqual(ty_key.error_set_type.names[0], key.err.name);

    // The name round-trips back to "Foo".
    try testing.expectEqualStrings("Foo", pool.stringSlice(key.err.name));
}

test "error_value: same name interns to the same Index across calls" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const v1 = try evalSource(gpa, &pool, "error.Foo", &diag_buf);
    const v2 = try evalSource(gpa, &pool, "error.Foo", &diag_buf);
    try testing.expectEqual(v1.index, v2.index);
}

test "error_union_type: bare E!T evaluates to a union type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, &pool, "error{Bad}!u32", &diag_buf);
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .error_union_type);
    try testing.expectEqual(InternPool.Index.u32_type, key.error_union_type.payload_type);

    const es = pool.indexToKey(key.error_union_type.error_set_type).error_set_type;
    try testing.expectEqual(@as(usize, 1), es.names.len);
    try testing.expectEqualStrings("Bad", pool.stringSlice(es.names[0]));
}

test "error_union_value: @as(E!T, error.X) wraps as .err arm" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, &pool, "@as(error{Bad}!u32, error.Bad)", &diag_buf);
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .error_union);
    try testing.expect(key.error_union.val == .err_name);
    try testing.expectEqualStrings("Bad", pool.stringSlice(key.error_union.val.err_name));
}

test "error_union_value: @as(E!T, payload) wraps as .payload arm" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const value = try evalSource(gpa, &pool, "@as(error{Bad}!u32, 42)", &diag_buf);
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .error_union);
    try testing.expect(key.error_union.val == .payload);

    // The wrapped payload is the coerced int value.
    const payload_key = pool.indexToKey(key.error_union.val.payload);
    try testing.expect(payload_key == .int);
    try testing.expectEqual(InternPool.Index.u32_type, payload_key.int.ty);
    try testing.expectEqual(@as(u64, 42), payload_key.int.storage.u64);
}

test "error_union_type: dedups by (error_set, payload) pair" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var diag_buf: [4096]u8 = undefined;
    const v1 = try evalSource(gpa, &pool, "error{Bad}!u32", &diag_buf);
    const v2 = try evalSource(gpa, &pool, "error{Bad}!u32", &diag_buf);
    try testing.expectEqual(v1.index, v2.index);

    const v3 = try evalSource(gpa, &pool, "error{Bad}!i32", &diag_buf);
    try testing.expect(v1.index != v3.index);
}

test "error_union_type: cross-line E!T via const-bound error set" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns, &.{
        "const E = error{Oops};",
        "const EU = E!u8;",
        "@as(EU, error.Oops)",
    }, &diag_buf)).?;
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .error_union);
    try testing.expect(key.error_union.val == .err_name);
}

test "error_set: cross-line const E = error{...} binds the type" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns, &.{
        "const E = error{Bad, Worse};",
        "E",
    }, &diag_buf)).?;
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .error_set_type);
    try testing.expectEqual(@as(usize, 2), key.error_set_type.names.len);
}

test "fn decl: nullary void fn binds with correct FuncType" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns_idx, &.{
        "fn foo() void {}",
    }, &diag_buf);

    const ns = pool.namespacePtr(ns_idx);
    const name = try pool.getOrPutString(gpa, "foo");
    const nav_idx = ns.lookupNav(&pool, name).?;
    const nav = pool.getNav(nav_idx);
    const resolved = nav.resolved.?;

    const fn_key = pool.indexToKey(resolved.value).func;
    const fn_ty_key = pool.indexToKey(fn_key.ty).func_type;
    try testing.expectEqual(@as(usize, 0), fn_ty_key.param_types.len);
    try testing.expectEqual(InternPool.Index.void_type, fn_ty_key.return_type);
    try testing.expectEqual(fn_key.ty, fn_key.uncoerced_ty);
    try testing.expectEqual(InternPool.Index.none, fn_key.generic_owner);
}

test "fn decl: typed params populate FuncType.param_types in order" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns_idx, &.{
        "fn add(a: u32, b: i32) u8 { _ = a; _ = b; return 0; }",
    }, &diag_buf);

    const ns = pool.namespacePtr(ns_idx);
    const nav_idx = ns.lookupNav(&pool, try pool.getOrPutString(gpa, "add")).?;
    const fn_key = pool.indexToKey(pool.getNav(nav_idx).resolved.?.value).func;
    const fn_ty = pool.indexToKey(fn_key.ty).func_type;

    try testing.expectEqual(@as(usize, 2), fn_ty.param_types.len);
    try testing.expectEqual(InternPool.Index.u32_type, fn_ty.param_types[0]);
    try testing.expectEqual(InternPool.Index.i32_type, fn_ty.param_types[1]);
    try testing.expectEqual(InternPool.Index.u8_type, fn_ty.return_type);
    try testing.expectEqual(@as(u32, 0), fn_ty.comptime_bits);
}

test "fn decl: comptime parameter sets comptime_bits" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns_idx, &.{
        "fn pick(a: u32, comptime b: u32) u32 { return a + b; }",
    }, &diag_buf);

    const ns = pool.namespacePtr(ns_idx);
    const nav_idx = ns.lookupNav(&pool, try pool.getOrPutString(gpa, "pick")).?;
    const fn_key = pool.indexToKey(pool.getNav(nav_idx).resolved.?.value).func;
    const fn_ty = pool.indexToKey(fn_key.ty).func_type;

    // Bit 1 set means param 1 is comptime.
    try testing.expectEqual(@as(u32, 0b10), fn_ty.comptime_bits);
    try testing.expect(!fn_ty.paramIsComptime(0));
    try testing.expect(fn_ty.paramIsComptime(1));
}

test "fn decl: dedup -- same signature reuses FuncType Index" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    _ = try evalSessionLines(gpa, &pool, ns_idx, &.{
        "fn f() void {}",
        "fn g() void {}",
    }, &diag_buf);

    const ns = pool.namespacePtr(ns_idx);
    const fn_f = pool.indexToKey(pool.getNav(ns.lookupNav(&pool, try pool.getOrPutString(gpa, "f")).?).resolved.?.value).func;
    const fn_g = pool.indexToKey(pool.getNav(ns.lookupNav(&pool, try pool.getOrPutString(gpa, "g")).?).resolved.?.value).func;

    // Same signature -> same fn_type Index.
    try testing.expectEqual(fn_f.ty, fn_g.ty);
    // Different bodies -> different Func Index.
    try testing.expect(fn_f.zir_body_inst != fn_g.zir_body_inst);
}

test "fn call: cross-line call returns the right value" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns, &.{
        "fn id(x: u32) u32 { return x; }",
        "id(42)",
    }, &diag_buf)).?;
    const key = pool.indexToKey(value.index);
    try testing.expect(key == .int);
    try testing.expectEqual(@as(u64, 42), key.int.storage.u64);
}

test "fn call: cross-line recursion (fib)" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns, &.{
        "fn fib(n: u32) u32 { return if (n < 2) n else fib(n - 1) + fib(n - 2); }",
        "fib(10)",
    }, &diag_buf)).?;
    try testing.expectEqual(@as(u64, 55), pool.indexToKey(value.index).int.storage.u64);
}

test "fn decl: cross-line retrieval round-trips the Func value" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns_idx = try pool.createNamespace(gpa, .none);

    var diag_buf: [4096]u8 = undefined;
    const value = (try evalSessionLines(gpa, &pool, ns_idx, &.{
        "fn h(a: u8) i32 { _ = a; return 0; }",
        "h",
    }, &diag_buf)).?;

    const fn_key = pool.indexToKey(value.index).func;
    const fn_ty = pool.indexToKey(fn_key.ty).func_type;
    try testing.expectEqual(@as(usize, 1), fn_ty.param_types.len);
    try testing.expectEqual(InternPool.Index.u8_type, fn_ty.param_types[0]);
    try testing.expectEqual(InternPool.Index.i32_type, fn_ty.return_type);
}

test "array_type: small variant round-trip [3]i32" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const idx_a = try pool.internArrayType(.{
        .len = 3,
        .child = .i32_type,
        .sentinel = .none,
    });
    const idx_b = try pool.internArrayType(.{
        .len = 3,
        .child = .i32_type,
        .sentinel = .none,
    });
    try testing.expectEqual(idx_a, idx_b);

    const decoded = pool.indexToKey(idx_a).array_type;
    try testing.expectEqual(@as(u64, 3), decoded.len);
    try testing.expectEqual(InternPool.Index.i32_type, decoded.child);
    try testing.expectEqual(InternPool.Index.none, decoded.sentinel);
}

test "array_type: big variant carries sentinel [3:0]u8" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const idx = try pool.internArrayType(.{
        .len = 3,
        .child = .u8_type,
        .sentinel = .zero,
    });
    const decoded = pool.indexToKey(idx).array_type;
    try testing.expectEqual(@as(u64, 3), decoded.len);
    try testing.expectEqual(InternPool.Index.u8_type, decoded.child);
    try testing.expectEqual(InternPool.Index.zero, decoded.sentinel);
}

test "array_type: big variant carries 64-bit length" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const huge: u64 = (@as(u64, 1) << 33) + 7;
    const idx = try pool.internArrayType(.{
        .len = huge,
        .child = .u8_type,
        .sentinel = .none,
    });
    const decoded = pool.indexToKey(idx).array_type;
    try testing.expectEqual(huge, decoded.len);
    try testing.expectEqual(InternPool.Index.u8_type, decoded.child);
    try testing.expectEqual(InternPool.Index.none, decoded.sentinel);
}

test "array_type: small and big differ on sentinel" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const small = try pool.internArrayType(.{
        .len = 3,
        .child = .u8_type,
        .sentinel = .none,
    });
    const big = try pool.internArrayType(.{
        .len = 3,
        .child = .u8_type,
        .sentinel = .zero,
    });
    try testing.expect(small != big);
}

test "array_type: lenIncludingSentinel adds the terminator" {
    const at_no_sent: InternPool.Key.ArrayType = .{
        .len = 3,
        .child = .u8_type,
        .sentinel = .none,
    };
    try testing.expectEqual(@as(u64, 3), at_no_sent.lenIncludingSentinel());

    const at_sent: InternPool.Key.ArrayType = .{
        .len = 3,
        .child = .u8_type,
        .sentinel = .zero,
    };
    try testing.expectEqual(@as(u64, 4), at_sent.lenIncludingSentinel());
}

test "aggregate: elems round-trip [_]i32{1, 2, 3}" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const arr_ty = try pool.internArrayType(.{
        .len = 3,
        .child = .i32_type,
        .sentinel = .none,
    });
    const one = InternPool.Index.one;
    const two = try pool.internInt(.{ .ty = .i32_type, .storage = .{ .u64 = 2 } });
    const three = try pool.internInt(.{ .ty = .i32_type, .storage = .{ .u64 = 3 } });
    const elems = [_]InternPool.Index{ one, two, three };
    const idx_a = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .elems = &elems },
    });
    const idx_b = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .elems = &elems },
    });
    try testing.expectEqual(idx_a, idx_b);

    const decoded = pool.indexToKey(idx_a).aggregate;
    try testing.expectEqual(arr_ty, decoded.ty);
    try testing.expect(decoded.storage == .elems);
    try testing.expectEqual(@as(usize, 3), decoded.storage.elems.len);
    try testing.expectEqual(one, decoded.storage.elems[0]);
    try testing.expectEqual(two, decoded.storage.elems[1]);
    try testing.expectEqual(three, decoded.storage.elems[2]);
}

test "aggregate: repeated_elem round-trip [_]u32{7, 7, 7}" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const arr_ty = try pool.internArrayType(.{
        .len = 3,
        .child = .u32_type,
        .sentinel = .none,
    });
    const seven = try pool.internInt(.{ .ty = .u32_type, .storage = .{ .u64 = 7 } });
    const idx = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .repeated_elem = seven },
    });

    const decoded = pool.indexToKey(idx).aggregate;
    try testing.expectEqual(arr_ty, decoded.ty);
    try testing.expect(decoded.storage == .repeated_elem);
    try testing.expectEqual(seven, decoded.storage.repeated_elem);
}

test "aggregate: structural eql dedups all-equal elems vs repeated_elem" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const arr_ty = try pool.internArrayType(.{
        .len = 3,
        .child = .u32_type,
        .sentinel = .none,
    });
    const seven = try pool.internInt(.{ .ty = .u32_type, .storage = .{ .u64 = 7 } });
    const elems = [_]InternPool.Index{ seven, seven, seven };

    const via_elems = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .elems = &elems },
    });
    const via_repeat = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .repeated_elem = seven },
    });
    // Compiler-faithful: hash/eql canonicalize across flavors so
    // both calls return the same Index. Storage flavor preserved
    // from the first insertion -- here `.elems`.
    try testing.expectEqual(via_elems, via_repeat);
    const decoded = pool.indexToKey(via_elems).aggregate;
    try testing.expect(decoded.storage == .elems);
}

test "aggregate: structural eql with first insertion as repeated_elem" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const arr_ty = try pool.internArrayType(.{
        .len = 3,
        .child = .u32_type,
        .sentinel = .none,
    });
    const seven = try pool.internInt(.{ .ty = .u32_type, .storage = .{ .u64 = 7 } });

    const via_repeat = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .repeated_elem = seven },
    });
    const elems = [_]InternPool.Index{ seven, seven, seven };
    const via_elems = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .elems = &elems },
    });
    try testing.expectEqual(via_repeat, via_elems);
    const decoded = pool.indexToKey(via_repeat).aggregate;
    // First-insertion-wins -- `.repeated_elem` flavor preserved.
    try testing.expect(decoded.storage == .repeated_elem);
}

test "aggregate: mixed elems stays in elems storage" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const arr_ty = try pool.internArrayType(.{
        .len = 3,
        .child = .i32_type,
        .sentinel = .none,
    });
    const one = InternPool.Index.one;
    const two = try pool.internInt(.{ .ty = .i32_type, .storage = .{ .u64 = 2 } });
    const three = try pool.internInt(.{ .ty = .i32_type, .storage = .{ .u64 = 3 } });
    const elems = [_]InternPool.Index{ one, two, three };

    const idx = try pool.internAggregate(.{
        .ty = arr_ty,
        .storage = .{ .elems = &elems },
    });
    const decoded = pool.indexToKey(idx).aggregate;
    try testing.expect(decoded.storage == .elems);
}

test "aggregate: different types do not dedup" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    const i32_arr = try pool.internArrayType(.{
        .len = 3,
        .child = .i32_type,
        .sentinel = .none,
    });
    const u32_arr = try pool.internArrayType(.{
        .len = 3,
        .child = .u32_type,
        .sentinel = .none,
    });
    const seven_i32 = try pool.internInt(.{ .ty = .i32_type, .storage = .{ .u64 = 7 } });
    const seven_u32 = try pool.internInt(.{ .ty = .u32_type, .storage = .{ .u64 = 7 } });

    const a = try pool.internAggregate(.{
        .ty = i32_arr,
        .storage = .{ .repeated_elem = seven_i32 },
    });
    const b = try pool.internAggregate(.{
        .ty = u32_arr,
        .storage = .{ .repeated_elem = seven_u32 },
    });
    try testing.expect(a != b);
}

//! Lives at src/ rather than src/sema/ so it can import from front/ and
//! sema/ both; Zig blocks cross-directory imports inside one subdir.

const std = @import("std");
const testing = std.testing;

const Pipeline = @import("front/Pipeline.zig");
const Sema = @import("sema/Sema.zig");
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

    var writer = std.Io.Writer.fixed(diag_buf);
    const maybe_value = try Sema.analyze(gpa, intern_pool, result.zir, &writer);
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
    const key = intern_pool.get(value.index);
    try testing.expect(key == .int_value);

    const decimal = try key.int_value.value.toStringAlloc(gpa, 10, .lower);
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

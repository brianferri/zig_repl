//! Runtime-only port of the compiler's `src/InternPool.zig`. Strips the
//! incremental-compilation machinery (`*_deps`, `TrackedInst`, `AnalUnit`,
//! thread sharding, `memoized_call`) and keeps the part that matters for a
//! REPL: canonical, deduplicated storage of types and values.
//!
//! Reference (compiler tip): codeberg.org/ziglang/zig/src/InternPool.zig.
//! Every Index returned from `intern` is stable for the lifetime of the pool.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const BigIntConst = std.math.big.int.Const;

const InternPool = @This();

/// Stable handle into the pool. `none` is reserved as a null sentinel.
pub const Index = enum(u32) {
    /// Reserved sentinels, statically populated by `init`. Must stay in sync
    /// with `well_known` below.
    none = std.math.maxInt(u32),
    void_type = 0,
    bool_type = 1,
    type_type = 2,
    noreturn_type = 3,
    anyopaque_type = 4,
    comptime_int_type = 5,
    comptime_float_type = 6,
    undefined_type = 7,
    null_type = 8,
    u8_type = 9,
    u16_type = 10,
    u32_type = 11,
    u64_type = 12,
    i8_type = 13,
    i16_type = 14,
    i32_type = 15,
    i64_type = 16,
    void_value = 17,
    bool_true = 18,
    bool_false = 19,
    null_value = 20,
    undefined_value = 21,
    _,
};

const first_dynamic_index: u32 = 22;

// `usize`/`isize` are intentionally absent from the well-known set: they are
// nominally distinct from u64/i64 even when bit widths match (the compiler
// uses dedicated indices that route through a different mechanism). They will
// land alongside the first handler that actually needs them, either as
// simple_type variants or a dedicated ptr_sized_int_type Key.

pub const SimpleType = enum {
    void,
    bool,
    type,
    noreturn,
    anyopaque,
    comptime_int,
    comptime_float,
    undefined,
    null,
};

pub const SimpleValue = enum {
    void,
    bool_true,
    bool_false,
    null,
    undefined,
};

pub const Key = union(enum) {
    simple_type: SimpleType,
    simple_value: SimpleValue,
    /// Concrete fixed-width integer type. Reuses `std.builtin.Type.Int` so the
    /// shape stays identical to what `@typeInfo(T).int` reports for any
    /// non-pointer-sized integer.
    int_type: std.builtin.Type.Int,
    /// An integer value tagged with its type. The `value` field is a plain
    /// `std.math.big.int.Const`; its limbs slice is borrowed from the pool's
    /// arena and is valid for the lifetime of the pool.
    int_value: Int,
    /// A value whose runtime type is `type` and whose payload is the
    /// interned type itself.
    type_value: Index,

    pub const Int = struct {
        ty: Index,
        value: BigIntConst,
    };
};

/// Tagged storage. `data` interpretation depends on `tag` per the
/// switch in `get`. Most variants fit in this 8 bytes; larger payloads
/// (currently just int_value) spill into `extra`.
const Item = struct {
    tag: Tag,
    data: u32,

    const Tag = enum(u8) {
        simple_type, // data = SimpleType ordinal
        simple_value, // data = SimpleValue ordinal
        int_type_unsigned, // data = bits
        int_type_signed, // data = bits
        int_value, // data = extra index of IntValueRepr
        type_value, // data = Index of the interned type
    };
};

/// Internal storage encoding for `Key.int_value`. Lives in `extra` because it
/// is larger than a u32 slot. Never escapes the pool — consumers see only the
/// decoded `Key.Int` with a plain `BigIntConst`.
const IntValueRepr = extern struct {
    ty: u32,
    positive: u32, // 0 or 1
    limbs_index: u32,
    limbs_len: u32,
};

gpa: Allocator,
items: std.MultiArrayList(Item),
extra: std.ArrayListUnmanaged(u32),
big_int_limbs: std.ArrayListUnmanaged(std.math.big.Limb),
/// Key → Index dedup map. Hash + equality go through `KeyAdapter`.
map: std.AutoArrayHashMapUnmanaged(void, void),

pub fn init(gpa: Allocator) Allocator.Error!InternPool {
    var pool: InternPool = .{
        .gpa = gpa,
        .items = .{},
        .extra = .empty,
        .big_int_limbs = .empty,
        .map = .empty,
    };
    errdefer pool.deinit();

    try pool.items.ensureTotalCapacity(gpa, first_dynamic_index);
    try populateWellKnown(&pool);
    assert(pool.items.len == first_dynamic_index);
    return pool;
}

pub fn deinit(pool: *InternPool) void {
    pool.items.deinit(pool.gpa);
    pool.extra.deinit(pool.gpa);
    pool.big_int_limbs.deinit(pool.gpa);
    pool.map.deinit(pool.gpa);
    pool.* = undefined;
}

fn populateWellKnown(pool: *InternPool) Allocator.Error!void {
    assert(pool.items.len == 0);

    inline for (.{
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.void) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.bool) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.type) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.noreturn) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.anyopaque) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.comptime_int) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.comptime_float) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.undefined) },
        .{ Item.Tag.simple_type, @intFromEnum(SimpleType.null) },
        .{ Item.Tag.int_type_unsigned, 8 },
        .{ Item.Tag.int_type_unsigned, 16 },
        .{ Item.Tag.int_type_unsigned, 32 },
        .{ Item.Tag.int_type_unsigned, 64 },
        .{ Item.Tag.int_type_signed, 8 },
        .{ Item.Tag.int_type_signed, 16 },
        .{ Item.Tag.int_type_signed, 32 },
        .{ Item.Tag.int_type_signed, 64 },
        .{ Item.Tag.simple_value, @intFromEnum(SimpleValue.void) },
        .{ Item.Tag.simple_value, @intFromEnum(SimpleValue.bool_true) },
        .{ Item.Tag.simple_value, @intFromEnum(SimpleValue.bool_false) },
        .{ Item.Tag.simple_value, @intFromEnum(SimpleValue.null) },
        .{ Item.Tag.simple_value, @intFromEnum(SimpleValue.undefined) },
    }) |entry| {
        pool.items.appendAssumeCapacity(.{ .tag = entry.@"0", .data = entry.@"1" });
    }
}

pub fn get(pool: *const InternPool, index: Index) Key {
    assert(index != .none);
    const i = @intFromEnum(index);
    assert(i < pool.items.len);
    const item = pool.items.get(i);
    return switch (item.tag) {
        .simple_type => .{ .simple_type = @enumFromInt(@as(u8, @intCast(item.data))) },
        .simple_value => .{ .simple_value = @enumFromInt(@as(u8, @intCast(item.data))) },
        .int_type_unsigned => .{ .int_type = .{
            .signedness = .unsigned,
            .bits = @intCast(item.data),
        } },
        .int_type_signed => .{ .int_type = .{
            .signedness = .signed,
            .bits = @intCast(item.data),
        } },
        .int_value => intValueFromExtra(pool, item.data),
        .type_value => .{ .type_value = @enumFromInt(item.data) },
    };
}

fn intValueFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = @typeInfo(IntValueRepr).@"struct".fields;
    assert(extra_index + fields.len <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields.len];

    const ty: Index = @enumFromInt(slice[0]);
    const positive = slice[1] != 0;
    const limbs_index = slice[2];
    const limbs_len = slice[3];
    assert(limbs_len > 0);
    const limbs = pool.big_int_limbs.items[limbs_index..][0..limbs_len];

    return .{ .int_value = .{
        .ty = ty,
        .value = .{ .limbs = limbs, .positive = positive },
    } };
}

/// Intern a fixed-width integer type. Returns one of the well-known indices
/// for u8/u16/u32/u64/i8/i16/i32/i64, otherwise appends a new item. Zig
/// permits `u0`..`u65535` and `i0`..`i65535`; any `bits` in that range is
/// representable because `std.builtin.Type.Int.bits` is itself `u16`.
pub fn internIntType(
    pool: *InternPool,
    signedness: std.builtin.Signedness,
    bits: u16,
) Allocator.Error!Index {
    if (wellKnownIntType(signedness, bits)) |idx| return idx;

    const tag: Item.Tag = switch (signedness) {
        .unsigned => .int_type_unsigned,
        .signed => .int_type_signed,
    };
    try pool.items.append(pool.gpa, .{ .tag = tag, .data = bits });
    return @enumFromInt(@as(u32, @intCast(pool.items.len - 1)));
}

fn wellKnownIntType(signedness: std.builtin.Signedness, bits: u16) ?Index {
    return switch (signedness) {
        .unsigned => switch (bits) {
            8 => .u8_type,
            16 => .u16_type,
            32 => .u32_type,
            64 => .u64_type,
            else => null,
        },
        .signed => switch (bits) {
            8 => .i8_type,
            16 => .i16_type,
            32 => .i32_type,
            64 => .i64_type,
            else => null,
        },
    };
}

/// Intern an integer value of the given type. `value`'s limbs are copied
/// into the pool's arena, so the caller may free its own buffer afterwards.
pub fn internIntValue(
    pool: *InternPool,
    ty: Index,
    value: BigIntConst,
) Allocator.Error!Index {
    assert(ty != .none);
    assert(value.limbs.len > 0);

    const limbs_index: u32 = @intCast(pool.big_int_limbs.items.len);
    try pool.big_int_limbs.appendSlice(pool.gpa, value.limbs);

    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.appendSlice(pool.gpa, &.{
        @intFromEnum(ty),
        @intFromBool(value.positive),
        limbs_index,
        @intCast(value.limbs.len),
    });

    try pool.items.append(pool.gpa, .{
        .tag = .int_value,
        .data = extra_index,
    });
    return @enumFromInt(@as(u32, @intCast(pool.items.len - 1)));
}

/// Convenience wrapper around `internIntValue` for comptime-typed integers.
pub fn internComptimeInt(pool: *InternPool, value: BigIntConst) Allocator.Error!Index {
    return pool.internIntValue(.comptime_int_type, value);
}

pub fn itemCount(pool: *const InternPool) u32 {
    return @intCast(pool.items.len);
}

test "well-known indices have expected keys" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(SimpleType.void, pool.get(.void_type).simple_type);
    try std.testing.expectEqual(SimpleType.bool, pool.get(.bool_type).simple_type);
    try std.testing.expectEqual(@as(u16, 32), pool.get(.u32_type).int_type.bits);
    try std.testing.expectEqual(std.builtin.Signedness.signed, pool.get(.i32_type).int_type.signedness);
    try std.testing.expectEqual(SimpleValue.bool_true, pool.get(.bool_true).simple_value);
}

test "arbitrary-width int types intern dynamically" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // Well-known widths return the reserved index without growing the pool.
    const items_before = pool.itemCount();
    const u32_idx = try pool.internIntType(.unsigned, 32);
    try std.testing.expectEqual(Index.u32_type, u32_idx);
    try std.testing.expectEqual(items_before, pool.itemCount());

    // Non-cached widths take a fresh slot and round-trip.
    const @"u17_idx" = try pool.internIntType(.unsigned, 17);
    try std.testing.expect(@"u17_idx" != .u8_type and @"u17_idx" != .u16_type and @"u17_idx" != .u32_type);
    const @"u17" = pool.get(@"u17_idx").int_type;
    try std.testing.expectEqual(std.builtin.Signedness.unsigned, @"u17".signedness);
    try std.testing.expectEqual(@as(u16, 17), @"u17".bits);

    // Zig's upper bound on integer widths is u65535 / i65535.
    const @"u65535_idx" = try pool.internIntType(.unsigned, std.math.maxInt(u16));
    const @"u65535" = pool.get(@"u65535_idx").int_type;
    try std.testing.expectEqual(@as(u16, std.math.maxInt(u16)), @"u65535".bits);

    const @"i9999_idx" = try pool.internIntType(.signed, 9999);
    const @"i9999" = pool.get(@"i9999_idx").int_type;
    try std.testing.expectEqual(std.builtin.Signedness.signed, @"i9999".signedness);
    try std.testing.expectEqual(@as(u16, 9999), @"i9999".bits);
}

test "comptime int round-trip" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    var limbs = [_]std.math.big.Limb{42};
    const value: BigIntConst = .{ .limbs = &limbs, .positive = true };
    const idx = try pool.internComptimeInt(value);

    const round = pool.get(idx).int_value;
    try std.testing.expectEqual(Index.comptime_int_type, round.ty);
    try std.testing.expectEqual(true, round.value.positive);
    try std.testing.expectEqual(@as(usize, 1), round.value.limbs.len);
    try std.testing.expectEqual(@as(std.math.big.Limb, 42), round.value.limbs[0]);
}

//! Runtime-only port of the compiler's `src/InternPool.zig`. Drops
//! incremental-compilation machinery (`*_deps`, `TrackedInst`, `AnalUnit`,
//! thread sharding, `memoized_call`) and keeps the canonical-storage core.
//!
//! Reference: src/InternPool.zig in the Zig compiler tree.
//! The well-known `Index` set, `SimpleType`/`SimpleValue` shape, and
//! `Item.Tag` naming mirror the compiler so the port reads against it
//! directly. Compiler-internal markers (`adhoc_inferred_error_set`,
//! `generic_poison`) plus the convenience pointer/slice/vector well-knowns
//! are deliberately deferred — they need Key variants (`ptr_type`,
//! `vector_type`, etc.) that land alongside their handlers.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const BigIntConst = std.math.big.int.Const;

const InternPool = @This();

/// Stable handle into the pool. The first `first_dynamic_index` slots are
/// reserved for well-known entries populated by `init`; later slots come
/// from dynamic interning. `none` is the null sentinel.
///
/// Ordering mirrors the compiler's enum so `SimpleType`/`SimpleValue` can
/// pin variant values to the corresponding Index via `@intFromEnum`.
pub const Index = enum(u32) {
    // --- Types: fixed-width integers (Key.int_type) ---
    u0_type,
    i0_type,
    u1_type,
    u8_type,
    i8_type,
    u16_type,
    i16_type,
    u29_type,
    u32_type,
    i32_type,
    u64_type,
    i64_type,
    u80_type,
    u128_type,
    i128_type,
    u256_type,

    // --- Types: target-dependent / nominal primitives (Key.simple_type) ---
    usize_type,
    isize_type,
    c_char_type,
    c_short_type,
    c_ushort_type,
    c_int_type,
    c_uint_type,
    c_long_type,
    c_ulong_type,
    c_longlong_type,
    c_ulonglong_type,
    c_longdouble_type,

    // --- Types: floats (Key.simple_type) ---
    f16_type,
    f32_type,
    f64_type,
    f80_type,
    f128_type,

    // --- Types: language primitives (Key.simple_type) ---
    anyopaque_type,
    bool_type,
    void_type,
    type_type,
    anyerror_type,
    comptime_int_type,
    comptime_float_type,
    noreturn_type,
    anyframe_type,
    null_type,
    undefined_type,
    enum_literal_type,

    // --- Values ---
    /// `undefined` (untyped)
    undef,
    /// `0` (comptime_int)
    zero,
    /// `1` (comptime_int)
    one,
    /// `-1` (comptime_int)
    negative_one,
    /// `{}`
    void_value,
    /// `unreachable` (noreturn)
    unreachable_value,
    /// `null` (untyped)
    null_value,
    /// `true`
    bool_true,
    /// `false`
    bool_false,

    /// Used by Air/Sema only.
    none = std.math.maxInt(u32),

    _,

    /// Range bounds for well-known types. Anything strictly between these
    /// (inclusive) is a type whose Key shape can be looked up via `get`
    /// without further checks. Dynamic indices fall outside this range.
    pub const first_type: Index = .u0_type;
    pub const last_type: Index = .enum_literal_type;
    pub const first_value: Index = .undef;
    pub const last_value: Index = .bool_false;

    pub fn isWellKnownType(index: Index) bool {
        const raw = @intFromEnum(index);
        return raw >= @intFromEnum(first_type) and raw <= @intFromEnum(last_type);
    }

    pub fn isWellKnownValue(index: Index) bool {
        const raw = @intFromEnum(index);
        return raw >= @intFromEnum(first_value) and raw <= @intFromEnum(last_value);
    }
};

const first_dynamic_index: u32 = @intFromEnum(Index.bool_false) + 1;

/// Mirrors compiler `InternPool.SimpleType`. Each variant's integer value is
/// the corresponding `Index`, so converting between the two is identity.
pub const SimpleType = enum(u32) {
    usize = @intFromEnum(Index.usize_type),
    isize = @intFromEnum(Index.isize_type),
    c_char = @intFromEnum(Index.c_char_type),
    c_short = @intFromEnum(Index.c_short_type),
    c_ushort = @intFromEnum(Index.c_ushort_type),
    c_int = @intFromEnum(Index.c_int_type),
    c_uint = @intFromEnum(Index.c_uint_type),
    c_long = @intFromEnum(Index.c_long_type),
    c_ulong = @intFromEnum(Index.c_ulong_type),
    c_longlong = @intFromEnum(Index.c_longlong_type),
    c_ulonglong = @intFromEnum(Index.c_ulonglong_type),
    c_longdouble = @intFromEnum(Index.c_longdouble_type),
    f16 = @intFromEnum(Index.f16_type),
    f32 = @intFromEnum(Index.f32_type),
    f64 = @intFromEnum(Index.f64_type),
    f80 = @intFromEnum(Index.f80_type),
    f128 = @intFromEnum(Index.f128_type),
    anyopaque = @intFromEnum(Index.anyopaque_type),
    bool = @intFromEnum(Index.bool_type),
    void = @intFromEnum(Index.void_type),
    type = @intFromEnum(Index.type_type),
    anyerror = @intFromEnum(Index.anyerror_type),
    comptime_int = @intFromEnum(Index.comptime_int_type),
    comptime_float = @intFromEnum(Index.comptime_float_type),
    noreturn = @intFromEnum(Index.noreturn_type),
    null = @intFromEnum(Index.null_type),
    undefined = @intFromEnum(Index.undefined_type),
    enum_literal = @intFromEnum(Index.enum_literal_type),
};

/// Mirrors compiler `InternPool.SimpleValue`. Same identity trick as `SimpleType`.
pub const SimpleValue = enum(u32) {
    void = @intFromEnum(Index.void_value),
    null = @intFromEnum(Index.null_value),
    true = @intFromEnum(Index.bool_true),
    false = @intFromEnum(Index.bool_false),
    @"unreachable" = @intFromEnum(Index.unreachable_value),
};

pub const Key = union(enum) {
    simple_type: SimpleType,
    simple_value: SimpleValue,
    /// Concrete fixed-width integer type. Shape matches `@typeInfo(T).int`.
    int_type: std.builtin.Type.Int,
    /// Payload is `.none` for untyped `anyframe`, or the child type's
    /// Index for `anyframe->T`.
    anyframe_type: Index,
    /// An integer value tagged with its type. The `value` field is a plain
    /// `std.math.big.int.Const` whose limbs are borrowed from the pool's
    /// arena and valid for the pool's lifetime.
    int_value: Int,
    /// A value whose runtime type is `type` and whose payload is the
    /// interned type itself.
    type_value: Index,

    pub const Int = struct {
        ty: Index,
        value: BigIntConst,
    };
};

/// Tagged storage. `data` interpretation depends on `tag`. Naming mirrors
/// the compiler's `Item.Tag` to keep ports legible.
const Item = struct {
    tag: Tag,
    data: u32,

    const Tag = enum(u8) {
        simple_type, // data = SimpleType ordinal == Index of the corresponding type
        simple_value, // data = SimpleValue ordinal == Index of the corresponding value
        type_int_unsigned, // data = bits
        type_int_signed, // data = bits
        type_anyframe, // data = Index of the frame's child type (or .none for untyped anyframe)
        int_value, // data = extra index of IntValueRepr
        type_value, // data = Index of the interned type
    };
};

/// Internal storage encoding for `Key.int_value`. Lives in `extra` because
/// it is larger than a u32 slot. Never escapes the pool.
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

pub fn init(gpa: Allocator) Allocator.Error!InternPool {
    var pool: InternPool = .{
        .gpa = gpa,
        .items = .{},
        .extra = .empty,
        .big_int_limbs = .empty,
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
    pool.* = undefined;
}

/// Comptime well-known table mirroring the compiler's `static_keys` array
/// in `src/InternPool.zig`. Each entry corresponds 1:1 to an `Index`
/// position; `populateWellKnown` iterates and dispatches per Key variant.
const zero_limbs = [_]std.math.big.Limb{0};
const one_limbs = [_]std.math.big.Limb{1};
const static_keys: [first_dynamic_index]Key = .{
    .{ .int_type = .{ .signedness = .unsigned, .bits = 0 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 0 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 1 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 8 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 8 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 16 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 16 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 29 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 32 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 32 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 64 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 64 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 80 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 128 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 128 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 256 } },

    .{ .simple_type = .usize },
    .{ .simple_type = .isize },
    .{ .simple_type = .c_char },
    .{ .simple_type = .c_short },
    .{ .simple_type = .c_ushort },
    .{ .simple_type = .c_int },
    .{ .simple_type = .c_uint },
    .{ .simple_type = .c_long },
    .{ .simple_type = .c_ulong },
    .{ .simple_type = .c_longlong },
    .{ .simple_type = .c_ulonglong },
    .{ .simple_type = .c_longdouble },

    .{ .simple_type = .f16 },
    .{ .simple_type = .f32 },
    .{ .simple_type = .f64 },
    .{ .simple_type = .f80 },
    .{ .simple_type = .f128 },

    .{ .simple_type = .anyopaque },
    .{ .simple_type = .bool },
    .{ .simple_type = .void },
    .{ .simple_type = .type },
    .{ .simple_type = .anyerror },
    .{ .simple_type = .comptime_int },
    .{ .simple_type = .comptime_float },
    .{ .simple_type = .noreturn },
    .{ .anyframe_type = .none },
    .{ .simple_type = .null },
    .{ .simple_type = .undefined },
    .{ .simple_type = .enum_literal },

    // Untyped `undefined`. Compiler shape is `.{ .undef = .undefined_type }`;
    // ours uses a `type_value` until the `undef` Key variant lands.
    .{ .type_value = .undefined_type },
    .{ .int_value = .{ .ty = .comptime_int_type, .value = .{ .limbs = &zero_limbs, .positive = true } } },
    .{ .int_value = .{ .ty = .comptime_int_type, .value = .{ .limbs = &one_limbs, .positive = true } } },
    .{ .int_value = .{ .ty = .comptime_int_type, .value = .{ .limbs = &one_limbs, .positive = false } } },
    .{ .simple_value = .void },
    .{ .simple_value = .@"unreachable" },
    .{ .simple_value = .null },
    .{ .simple_value = .true },
    .{ .simple_value = .false },
};

fn populateWellKnown(pool: *InternPool) Allocator.Error!void {
    assert(pool.items.len == 0);

    inline for (static_keys) |key| {
        try appendStaticKey(pool, key);
    }
}

fn appendStaticKey(pool: *InternPool, key: Key) Allocator.Error!void {
    switch (key) {
        .simple_type => |s| appendSimpleType(pool, s),
        .simple_value => |s| appendSimpleValue(pool, s),
        .int_type => |it| appendIntType(pool, it.signedness, it.bits),
        .anyframe_type => |child| appendAnyframeType(pool, child),
        .type_value => |t| pool.items.appendAssumeCapacity(.{
            .tag = .type_value,
            .data = @intFromEnum(t),
        }),
        .int_value => |iv| {
            _ = try appendIntValueAssumingSafe(pool, iv.ty, iv.value.limbs, iv.value.positive);
        },
    }
}

fn appendIntType(pool: *InternPool, signedness: std.builtin.Signedness, bits: u16) void {
    const tag: Item.Tag = switch (signedness) {
        .unsigned => .type_int_unsigned,
        .signed => .type_int_signed,
    };
    pool.items.appendAssumeCapacity(.{ .tag = tag, .data = bits });
}

fn appendSimpleType(pool: *InternPool, simple: SimpleType) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .simple_type,
        .data = @intFromEnum(simple),
    });
}

fn appendSimpleValue(pool: *InternPool, simple: SimpleValue) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .simple_value,
        .data = @intFromEnum(simple),
    });
}

fn appendAnyframeType(pool: *InternPool, child: Index) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .type_anyframe,
        .data = @intFromEnum(child),
    });
}

pub fn get(pool: *const InternPool, index: Index) Key {
    assert(index != .none);
    const i = @intFromEnum(index);
    assert(i < pool.items.len);
    const item = pool.items.get(i);
    return switch (item.tag) {
        .simple_type => .{ .simple_type = @enumFromInt(item.data) },
        .simple_value => .{ .simple_value = @enumFromInt(item.data) },
        .type_int_unsigned => .{ .int_type = .{
            .signedness = .unsigned,
            .bits = @intCast(item.data),
        } },
        .type_int_signed => .{ .int_type = .{
            .signedness = .signed,
            .bits = @intCast(item.data),
        } },
        .type_anyframe => .{ .anyframe_type = @enumFromInt(item.data) },
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
/// when `bits` matches a cached width, otherwise appends a new item. Zig
/// permits `u0`..`u65535` and `i0`..`i65535` (the language limit is the
/// `u16` width of `std.builtin.Type.Int.bits`).
pub fn internIntType(
    pool: *InternPool,
    signedness: std.builtin.Signedness,
    bits: u16,
) Allocator.Error!Index {
    if (wellKnownIntType(signedness, bits)) |idx| return idx;

    const tag: Item.Tag = switch (signedness) {
        .unsigned => .type_int_unsigned,
        .signed => .type_int_signed,
    };
    try pool.items.append(pool.gpa, .{ .tag = tag, .data = bits });
    return @enumFromInt(@as(u32, @intCast(pool.items.len - 1)));
}

fn wellKnownIntType(signedness: std.builtin.Signedness, bits: u16) ?Index {
    return switch (signedness) {
        .unsigned => switch (bits) {
            0 => .u0_type,
            1 => .u1_type,
            8 => .u8_type,
            16 => .u16_type,
            29 => .u29_type,
            32 => .u32_type,
            64 => .u64_type,
            80 => .u80_type,
            128 => .u128_type,
            256 => .u256_type,
            else => null,
        },
        .signed => switch (bits) {
            0 => .i0_type,
            8 => .i8_type,
            16 => .i16_type,
            32 => .i32_type,
            64 => .i64_type,
            128 => .i128_type,
            else => null,
        },
    };
}

/// Intern an integer value of the given type. `value`'s limbs are copied
/// into the pool's arena, so the caller may free its own buffer afterwards.
///
/// Aliasing-safe: if `value.limbs` is a borrowed view into this pool's own
/// `big_int_limbs` (for example a caller forwarding a previously-interned
/// value through a sign flip), the buffer is copied through a gpa temp
/// first. Without that guard, `appendSlice`'s ensure-capacity step could
/// reallocate `big_int_limbs` and leave `value.limbs.ptr` dangling before
/// the memcpy ran — the classic ArrayList aliasing footgun.
pub fn internIntValue(
    pool: *InternPool,
    ty: Index,
    value: BigIntConst,
) Allocator.Error!Index {
    assert(@intFromPtr(pool) != 0);
    assert(ty != .none);
    assert(value.limbs.len > 0);
    assert(value.limbs.len <= std.math.maxInt(u32));

    const items_before = pool.items.len;

    const result = if (limbsAliasPool(pool, value.limbs)) blk: {
        const copy = try pool.gpa.dupe(std.math.big.Limb, value.limbs);
        defer pool.gpa.free(copy);
        break :blk try appendIntValueAssumingSafe(pool, ty, copy, value.positive);
    } else try appendIntValueAssumingSafe(pool, ty, value.limbs, value.positive);

    assert(result != .none);
    assert(pool.items.len == items_before + 1);
    assert(@intFromEnum(result) == items_before);
    return result;
}

fn limbsAliasPool(pool: *const InternPool, limbs: []const std.math.big.Limb) bool {
    assert(@intFromPtr(pool) != 0);
    if (limbs.len == 0) return false;

    const buffer = pool.big_int_limbs.allocatedSlice();
    if (buffer.len == 0) return false;

    const buf_start = @intFromPtr(buffer.ptr);
    const buf_end = buf_start + buffer.len * @sizeOf(std.math.big.Limb);
    assert(buf_end >= buf_start); // no wraparound

    const slice_start = @intFromPtr(limbs.ptr);
    return slice_start >= buf_start and slice_start < buf_end;
}

fn appendIntValueAssumingSafe(
    pool: *InternPool,
    ty: Index,
    limbs: []const std.math.big.Limb,
    positive: bool,
) Allocator.Error!Index {
    assert(@intFromPtr(pool) != 0);
    assert(ty != .none);
    assert(limbs.len > 0);
    assert(!limbsAliasPool(pool, limbs)); // caller is responsible for dupe

    const limbs_before = pool.big_int_limbs.items.len;
    const extra_before = pool.extra.items.len;
    const items_before = pool.items.len;

    const limbs_index: u32 = @intCast(limbs_before);
    try pool.big_int_limbs.appendSlice(pool.gpa, limbs);

    const extra_index: u32 = @intCast(extra_before);
    try pool.extra.appendSlice(pool.gpa, &.{
        @intFromEnum(ty),
        @intFromBool(positive),
        limbs_index,
        @intCast(limbs.len),
    });

    try pool.items.append(pool.gpa, .{
        .tag = .int_value,
        .data = extra_index,
    });

    assert(pool.big_int_limbs.items.len == limbs_before + limbs.len);
    assert(pool.extra.items.len == extra_before + 4);
    assert(pool.items.len == items_before + 1);
    return @enumFromInt(@as(u32, @intCast(pool.items.len - 1)));
}

pub fn internComptimeInt(pool: *InternPool, value: BigIntConst) Allocator.Error!Index {
    return pool.internIntValue(.comptime_int_type, value);
}

/// Intern a value whose runtime type is `type` and whose payload is the
/// interned type identified by `ty`. This is how Sema returns "the
/// expression evaluated to a type" results (e.g. `@TypeOf(x)` or the
/// type computed by `typeof_log2_int_type`).
pub fn internTypeValue(pool: *InternPool, ty: Index) Allocator.Error!Index {
    assert(@intFromPtr(pool) != 0);
    assert(ty != .none);

    const items_before = pool.items.len;
    try pool.items.append(pool.gpa, .{ .tag = .type_value, .data = @intFromEnum(ty) });
    assert(pool.items.len == items_before + 1);
    return @enumFromInt(@as(u32, @intCast(pool.items.len - 1)));
}

pub fn itemCount(pool: *const InternPool) u32 {
    return @intCast(pool.items.len);
}

test "well-known types have expected keys" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(@as(u16, 8), pool.get(.u8_type).int_type.bits);
    try std.testing.expectEqual(@as(u16, 32), pool.get(.u32_type).int_type.bits);
    try std.testing.expectEqual(std.builtin.Signedness.signed, pool.get(.i32_type).int_type.signedness);

    try std.testing.expectEqual(SimpleType.usize, pool.get(.usize_type).simple_type);
    try std.testing.expectEqual(SimpleType.c_int, pool.get(.c_int_type).simple_type);
    try std.testing.expectEqual(SimpleType.f64, pool.get(.f64_type).simple_type);
    try std.testing.expectEqual(SimpleType.bool, pool.get(.bool_type).simple_type);
}

test "i0_type and anyframe_type slots match compiler ordering" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // i0_type lives at compiler position 1, between u0_type and u1_type.
    try std.testing.expectEqual(@as(u16, 0), pool.get(.i0_type).int_type.bits);
    try std.testing.expectEqual(std.builtin.Signedness.signed, pool.get(.i0_type).int_type.signedness);
    // internIntType for (.signed, 0) returns the well-known slot, no fresh item.
    const items_before = pool.itemCount();
    const @"i0_idx" = try pool.internIntType(.signed, 0);
    try std.testing.expectEqual(Index.i0_type, @"i0_idx");
    try std.testing.expectEqual(items_before, pool.itemCount());

    // anyframe_type with .none child (untyped anyframe) at the position
    // between noreturn_type and null_type.
    try std.testing.expectEqual(Index.none, pool.get(.anyframe_type).anyframe_type);
}

test "well-known values have expected keys" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(SimpleValue.true, pool.get(.bool_true).simple_value);
    try std.testing.expectEqual(SimpleValue.false, pool.get(.bool_false).simple_value);
    try std.testing.expectEqual(SimpleValue.void, pool.get(.void_value).simple_value);

    const zero = pool.get(.zero).int_value;
    try std.testing.expectEqual(Index.comptime_int_type, zero.ty);
    try std.testing.expectEqual(@as(std.math.big.Limb, 0), zero.value.limbs[0]);

    const negative_one = pool.get(.negative_one).int_value;
    try std.testing.expectEqual(false, negative_one.value.positive);
    try std.testing.expectEqual(@as(std.math.big.Limb, 1), negative_one.value.limbs[0]);
}

test "range markers cover the well-known sets" {
    try std.testing.expect(Index.isWellKnownType(.u0_type));
    try std.testing.expect(Index.isWellKnownType(.enum_literal_type));
    try std.testing.expect(!Index.isWellKnownType(.bool_true));
    try std.testing.expect(!Index.isWellKnownType(.none));

    try std.testing.expect(Index.isWellKnownValue(.undef));
    try std.testing.expect(Index.isWellKnownValue(.bool_false));
    try std.testing.expect(!Index.isWellKnownValue(.u8_type));
}

test "arbitrary-width int types intern dynamically" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const items_before = pool.itemCount();
    const u32_idx = try pool.internIntType(.unsigned, 32);
    try std.testing.expectEqual(Index.u32_type, u32_idx);
    try std.testing.expectEqual(items_before, pool.itemCount());

    const u17_idx = try pool.internIntType(.unsigned, 17);
    try std.testing.expect(!Index.isWellKnownType(u17_idx));
    const @"u17" = pool.get(u17_idx).int_type;
    try std.testing.expectEqual(std.builtin.Signedness.unsigned, @"u17".signedness);
    try std.testing.expectEqual(@as(u16, 17), @"u17".bits);

    const u65535_idx = try pool.internIntType(.unsigned, std.math.maxInt(u16));
    const @"u65535" = pool.get(u65535_idx).int_type;
    try std.testing.expectEqual(@as(u16, std.math.maxInt(u16)), @"u65535".bits);
}

test "internIntValue is aliasing-safe under buffer growth" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    var src = [_]std.math.big.Limb{42};
    const a_idx = try pool.internComptimeInt(.{ .limbs = &src, .positive = true });

    // Force big_int_limbs to exactly its capacity so the next append must
    // reallocate. Without the aliasing guard in internIntValue, the
    // subsequent reintern would memcpy from a stale source pointer.
    while (pool.big_int_limbs.items.len < pool.big_int_limbs.capacity) {
        try pool.big_int_limbs.append(pool.gpa, 0);
    }

    const a_view = pool.get(a_idx).int_value.value;
    const aliased: BigIntConst = .{ .limbs = a_view.limbs, .positive = false };

    const b_idx = try pool.internComptimeInt(aliased);
    const b = pool.get(b_idx).int_value;
    try std.testing.expectEqual(@as(usize, 1), b.value.limbs.len);
    try std.testing.expectEqual(@as(std.math.big.Limb, 42), b.value.limbs[0]);
    try std.testing.expectEqual(false, b.value.positive);
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

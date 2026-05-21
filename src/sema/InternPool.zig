//! Runtime-only port of the compiler's `src/InternPool.zig`. Drops
//! incremental-compilation machinery (`*_deps`, `TrackedInst`, `AnalUnit`,
//! thread sharding, `memoized_call`) and keeps the canonical-storage core.
//!
//! Reference: src/InternPool.zig in the Zig compiler tree.
//! The well-known `Index` set, `SimpleType`/`SimpleValue` shape, and
//! `Item.Tag` naming mirror the compiler so the port reads against it
//! directly. Compiler-internal markers (`adhoc_inferred_error_set`,
//! `generic_poison`) plus the convenience pointer/slice/vector well-knowns
//! are deliberately deferred -- they need Key variants (`ptr_type`,
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
    // Fixed-width integer types (Key.int_type). Slot ordering and
    // membership mirrors `std.zig.Zir.Inst.Ref` so a Zir ref's
    // integer value can be used as an `Index` directly for
    // well-known slots -- the identity in `Sema.wellKnownRefToValue`
    // depends on this 1:1 alignment.
    u0_type,
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

    // Target-dependent / nominal primitive types (Key.simple_type).
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

    // Float types (Key.simple_type).
    f16_type,
    f32_type,
    f64_type,
    f80_type,
    f128_type,

    // Language-primitive types (Key.simple_type).
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

    // Values.
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
    int_type: std.lang.Type.Int,
    /// Payload is `.none` for untyped `anyframe`, or the child type's
    /// Index for `anyframe->T`.
    anyframe_type: Index,
    /// An integer value tagged with its type. Mirrors the compiler's
    /// `Key.int`: storage holds the value as the narrowest variant that
    /// fits -- inline `u64`/`i64` for small magnitudes, `big_int` for
    /// arbitrary precision. For `big_int`, the limbs slice borrows from
    /// the pool's arena and is valid for the pool's lifetime.
    int: Int,
    /// A floating-point value tagged with its type. Mirrors the compiler's
    /// `Key.float`. The storage variant must match the type's bit width,
    /// except for `c_longdouble_type` (storage may be any width -- promoted
    /// to f128 on emit unless f80) and `comptime_float_type` (always
    /// f128).
    float: Float,
    /// `undefined` of type `Index`. Untyped `undefined` uses
    /// `.undefined_type` here; the well-known `Index.undef` slot stores
    /// exactly that shape. Mirrors the compiler's `Key.undef`.
    undef: Index,
    /// A value whose runtime type is `type` and whose payload is the
    /// interned type itself.
    type_value: Index,
    /// A pointer type (`*T`, `*const T`, `[*]T`, `[]T`, etc.). Mirrors
    /// the compiler's `Key.PtrType` -- the same shape but a subset of
    /// the flag set; we start with what Stage 2's alloc/store/load
    /// needs and widen with each stage.
    ptr_type: PtrType,
    /// A pointer value. Mirrors the compiler's `Key.Ptr`. `base_addr`
    /// today only has `.comptime_alloc` -- enough for REPL session
    /// allocations; `.nav` / `.uav` / `.int` etc. land alongside their
    /// dependent stages.
    ptr: Ptr,

    pub const Int = struct {
        ty: Index,
        storage: Storage,

        pub const Storage = union(enum) {
            u64: u64,
            i64: i64,
            big_int: BigIntConst,

            /// Materialise the value as a `BigIntConst` regardless of
            /// storage variant. The returned slice borrows from either
            /// the pool's arena (`.big_int`) or the caller-provided
            /// `BigIntSpace` (`.u64` / `.i64`).
            pub fn toBigInt(storage: Storage, space: *BigIntSpace) BigIntConst {
                return switch (storage) {
                    .big_int => |b| b,
                    inline .u64, .i64 => |v| std.math.big.int.Mutable.init(&space.limbs, v).toConst(),
                };
            }

            /// Big enough to fit any non-`big_int` storage variant. The
            /// +1 is headroom so a `Mutable` built from this buffer can
            /// be incremented or decremented once without spilling.
            /// Matches the compiler's `Key.Int.Storage.BigIntSpace`.
            pub const BigIntSpace = struct {
                limbs: [(@sizeOf(u64) / @sizeOf(std.math.big.Limb)) + 1]std.math.big.Limb,
            };
        };
    };

    pub const Float = struct {
        ty: Index,
        /// The storage variant used must match the size of the float type
        /// being represented (except for `c_longdouble_type`, see the
        /// emit dispatcher).
        storage: Storage,

        pub const Storage = union(enum) {
            f16: f16,
            f32: f32,
            f64: f64,
            f80: f80,
            f128: f128,
        };
    };

    /// Pointer type. Stage 2's minimal subset of the compiler's
    /// `Key.PtrType` -- shape matches but the flag field carries only
    /// what `alloc` / `store` / `load` need (size, is_const, address
    /// space). Sentinel and alignment will be wired alongside Stage 4
    /// aggregates.
    pub const PtrType = struct {
        child: Index,
        sentinel: Index = .none,
        flags: Flags = .{},

        pub const Flags = packed struct(u32) {
            size: Size = .one,
            is_const: bool = false,
            is_volatile: bool = false,
            is_allowzero: bool = false,
            address_space: AddressSpace = .generic,
            _reserved: u22 = 0,
        };

        // Reuse stdlib's enums verbatim -- same shape as the compiler's
        // `Key.PtrType.{Size,AddressSpace}` aliases at
        // `src/InternPool.zig:2093-2094`. Saves duplicating the variant
        // lists and stays in sync if stdlib adds CPU/GPU address spaces.
        pub const Size = std.lang.Type.Pointer.Size;
        pub const AddressSpace = std.lang.AddressSpace;
    };

    /// Pointer value. `ty` is the pointer's type (always a `ptr_type`
    /// Index). `base_addr` identifies the storage region; `byte_offset`
    /// is the offset within that region. Stage 2 ships
    /// `.comptime_alloc` only; later stages add `.nav` (declarations),
    /// `.uav` (anonymous addressable values), `.int` (`@ptrFromInt`),
    /// `.eu_payload`, `.opt_payload`, `.comptime_field`, etc. as their
    /// dependent ZIR tags land. Variant naming mirrors the compiler's
    /// `Key.Ptr.BaseAddr` (`src/InternPool.zig`).
    pub const Ptr = struct {
        ty: Index,
        base_addr: BaseAddr,
        byte_offset: u64,

        pub const BaseAddr = union(enum) {
            comptime_alloc: ComptimeAllocIndex,
        };
    };

    /// Opaque handle into `Sema.comptime_allocs`. Mirrors the compiler's
    /// `InternPool.ComptimeAllocIndex` -- the alloc's mutable state
    /// lives in Sema, not in the pool; this Index is the stable
    /// reference shared by every interned `Key.Ptr` pointing at the
    /// alloc.
    pub const ComptimeAllocIndex = enum(u32) { _ };

    /// Stable hash for dedup. `pool` is reserved for future Key variants
    /// (e.g. `struct_type`) whose canonical form requires pool lookup;
    /// today's variants ignore it. Storage variants of `int` are
    /// normalised to `BigIntConst` before hashing so that
    /// `.{ .u64 = 5 }` and `.{ .big_int = +5 }` hash identically -- the
    /// read-side compresses limbs back to inline storage so the pool's
    /// canonical form is stable, but a freshly constructed Key may
    /// arrive in any variant. Same canonicalisation in `eql`.
    pub fn hash64(key: Key, pool: *const InternPool) u64 {
        _ = pool;
        var hasher = std.hash.Wyhash.init(0);
        const Tag = @typeInfo(Key).@"union".tag_type.?;
        std.hash.autoHash(&hasher, @as(Tag, key));
        switch (key) {
            .simple_type => |s| std.hash.autoHash(&hasher, s),
            .simple_value => |s| std.hash.autoHash(&hasher, s),
            .int_type => |it| {
                std.hash.autoHash(&hasher, it.signedness);
                std.hash.autoHash(&hasher, it.bits);
            },
            .anyframe_type => |child| std.hash.autoHash(&hasher, child),
            .int => |i| {
                std.hash.autoHash(&hasher, i.ty);
                var space: Int.Storage.BigIntSpace = undefined;
                const big = i.storage.toBigInt(&space);
                std.hash.autoHash(&hasher, big.positive);
                for (big.limbs) |limb| std.hash.autoHash(&hasher, limb);
            },
            .float => |f| {
                std.hash.autoHash(&hasher, f.ty);
                switch (f.storage) {
                    inline else => |v| {
                        const Bits = @Int(.unsigned, @bitSizeOf(@TypeOf(v)));
                        std.hash.autoHash(&hasher, @as(Bits, @bitCast(v)));
                    },
                }
            },
            .undef => |ty| std.hash.autoHash(&hasher, ty),
            .type_value => |t| std.hash.autoHash(&hasher, t),
            .ptr_type => |pt| {
                std.hash.autoHash(&hasher, pt.child);
                std.hash.autoHash(&hasher, pt.sentinel);
                std.hash.autoHash(&hasher, @as(u32, @bitCast(pt.flags)));
            },
            .ptr => |p| {
                std.hash.autoHash(&hasher, p.ty);
                std.hash.autoHash(&hasher, p.byte_offset);
                const BaseTag = @typeInfo(Ptr.BaseAddr).@"union".tag_type.?;
                std.hash.autoHash(&hasher, @as(BaseTag, p.base_addr));
                switch (p.base_addr) {
                    .comptime_alloc => |slot| std.hash.autoHash(&hasher, slot),
                }
            },
        }
        return hasher.final();
    }

    /// Structural equality, paired with `hash64`. See `hash64` for the
    /// `int` canonicalisation rationale.
    pub fn eql(a: Key, b: Key, pool: *const InternPool) bool {
        _ = pool;
        const Tag = @typeInfo(Key).@"union".tag_type.?;
        if (@as(Tag, a) != @as(Tag, b)) return false;
        return switch (a) {
            .simple_type => |x| x == b.simple_type,
            .simple_value => |x| x == b.simple_value,
            .int_type => |x| x.signedness == b.int_type.signedness and
                x.bits == b.int_type.bits,
            .anyframe_type => |x| x == b.anyframe_type,
            .int => |x| blk: {
                const y = b.int;
                if (x.ty != y.ty) break :blk false;
                var sa: Int.Storage.BigIntSpace = undefined;
                var sb: Int.Storage.BigIntSpace = undefined;
                break :blk x.storage.toBigInt(&sa).eql(y.storage.toBigInt(&sb));
            },
            .float => |x| blk: {
                const y = b.float;
                if (x.ty != y.ty) break :blk false;
                // c_longdouble may be stored as any width and is promoted to
                // f128 on emit (except f80, which has its own tag). Two
                // c_longdouble Keys with different storage widths compare
                // equal iff they round-trip to the same f128 bit-pattern.
                // Mirrors the compiler's `Key.eql` branch.
                if (x.ty == .c_longdouble_type and x.storage != .f80) {
                    const a_bits: u128 = switch (x.storage) {
                        inline else => |v| @bitCast(@as(f128, @floatCast(v))),
                    };
                    const b_bits: u128 = switch (y.storage) {
                        inline else => |v| @bitCast(@as(f128, @floatCast(v))),
                    };
                    break :blk a_bits == b_bits;
                }
                const StorageTag = @typeInfo(Float.Storage).@"union".tag_type.?;
                if (@as(StorageTag, x.storage) != @as(StorageTag, y.storage)) break :blk false;
                break :blk switch (x.storage) {
                    inline else => |xv, tag| eq: {
                        const Bits = @Int(.unsigned, @bitSizeOf(@TypeOf(xv)));
                        const yv = @field(y.storage, @tagName(tag));
                        break :eq @as(Bits, @bitCast(xv)) == @as(Bits, @bitCast(yv));
                    },
                };
            },
            .undef => |x| x == b.undef,
            .type_value => |x| x == b.type_value,
            .ptr_type => |x| blk: {
                const y = b.ptr_type;
                if (x.child != y.child) break :blk false;
                if (x.sentinel != y.sentinel) break :blk false;
                break :blk @as(u32, @bitCast(x.flags)) == @as(u32, @bitCast(y.flags));
            },
            .ptr => |x| blk: {
                const y = b.ptr;
                if (x.ty != y.ty) break :blk false;
                if (x.byte_offset != y.byte_offset) break :blk false;
                const BaseTag = @typeInfo(Ptr.BaseAddr).@"union".tag_type.?;
                if (@as(BaseTag, x.base_addr) != @as(BaseTag, y.base_addr)) break :blk false;
                break :blk switch (x.base_addr) {
                    .comptime_alloc => |slot| slot == y.base_addr.comptime_alloc,
                };
            },
        };
    }
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
        // Type-specialised int storage. The tag implies the type; the value
        // is inline in `data`. Mirrors the compiler's compact encoding.
        int_u8, // ty = .u8_type;  data = the u8 value
        int_u16, // ty = .u16_type; data = the u16 value
        int_u32, // ty = .u32_type; data = the u32 value
        int_i32, // ty = .i32_type; data = the i32 value (bit-cast to u32)
        int_usize, // ty = .usize_type; data = u32 value
        int_comptime_int_u32, // ty = .comptime_int_type; data = u32 value (positive)
        int_comptime_int_i32, // ty = .comptime_int_type; data = i32 value (bit-cast)
        // Fallback for typed `u64` values whose type isn't covered by a
        // specialised tag above. data = extra index of IntSmall.
        int_small,
        // Arbitrary-precision integer. Sign is in the tag; the packed `Int`
        // header (ty + limbs_len) lives at `big_int_limbs[data]` and
        // occupies `IntBigHeader.limbs_items_len` Limb slots, with the
        // actual limbs trailing directly after. Mirrors the compiler's
        // `int_positive` / `int_negative` encoding (packed header at the
        // head of a Limb-aligned arena, limbs trailing).
        int_positive,
        int_negative,
        // Floats. Tag implies the type. For f16/f32 the bit-pattern fits in
        // `data` directly. f64/f80/f128 spill to `extra` as packed u32 pieces
        // (see Float64 / Float80 / Float128). c_longdouble has two tags
        // because the compiler stores either f80 (native x87) or f128 (every
        // other target); a runtime-only port doesn't pick the active arm but
        // mirrors the storage so the tag set matches the compiler exactly.
        // `comptime_float` is always stored as f128.
        float_f16, // ty = .f16_type;  data = @as(u16, @bitCast(f16)) inline
        float_f32, // ty = .f32_type;  data = @as(u32, @bitCast(f32)) inline
        float_f64, // ty = .f64_type;  data = extra index of Float64
        float_f80, // ty = .f80_type;  data = extra index of Float80
        float_f128, // ty = .f128_type; data = extra index of Float128
        float_c_longdouble_f80, // ty = .c_longdouble_type; storage f80, data = extra index of Float80
        float_c_longdouble_f128, // ty = .c_longdouble_type; storage f128, data = extra index of Float128
        float_comptime_float, // ty = .comptime_float_type; data = extra index of Float128
        undef, // data = Index of the value's type (`undefined_type` for untyped)
        type_value, // data = Index of the interned type
        // Pointer type. data = extra index of PtrTypeRepr (3 u32 slots:
        // child, sentinel, flags). Mirrors the compiler's
        // `Item.Tag.type_pointer`.
        type_pointer,
        // Pointer value with `BaseAddr.comptime_alloc`. data = extra
        // index of PtrComptimeAllocRepr (4 u32 slots: ty,
        // comptime_alloc index, byte_offset_lo, byte_offset_hi).
        // Mirrors the compiler's `Item.Tag.ptr_comptime_alloc`.
        ptr_comptime_alloc,
    };
};

/// Extra-arena payload for `Item.Tag.int_small`. Mirrors the compiler's
/// `IntSmall`: a typed value that fits in `u32` but whose type isn't
/// covered by the type-specialised inline tags. Stored as two
/// consecutive `u32`s in `extra`: `ty` then `value`. Values that
/// exceed `u32` skip this encoding and go straight to
/// `int_positive` / `int_negative`.
const IntSmall = extern struct {
    ty: u32,
    value: u32,
};

/// Extra-arena payload for `Item.Tag.type_pointer`. Three u32 slots:
/// child, sentinel, and the bit-packed `Key.PtrType.Flags`. Mirrors
/// the compiler's `Tag.TypePointer` storage shape (smaller because we
/// haven't ported `packed_offset` yet -- adds when Stage 4's
/// host-int-backed slice machinery needs it).
const PtrTypeRepr = extern struct {
    child: u32,
    sentinel: u32,
    flags: u32,
};

/// Extra-arena payload for `Item.Tag.ptr_comptime_alloc`. Four u32
/// slots: ty, comptime-alloc index, and the 64-bit byte_offset split
/// into lo/hi u32s. Mirrors the compiler's `Tag.PtrComptimeAlloc` --
/// allocations born in Sema rather than backed by a declaration.
const PtrComptimeAllocRepr = extern struct {
    ty: u32,
    alloc_index: u32,
    byte_offset_lo: u32,
    byte_offset_hi: u32,
};

/// Header for `Item.Tag.int_positive` / `Item.Tag.int_negative`. Lives at
/// the front of a contiguous `big_int_limbs` slice, with the actual limbs
/// trailing directly after. Sign is in the Item tag, not here. Matches the
/// compiler's packed `Int`.
const IntBigHeader = packed struct {
    ty: u32,
    limbs_len: u32,

    /// Number of Limb slots this header occupies (1 on 64-bit, 2 on 32-bit).
    const limbs_items_len = @divExact(@sizeOf(IntBigHeader), @sizeOf(std.math.big.Limb));
};

/// Extra-arena payload for `Item.Tag.float_f64`. Mirrors the compiler's
/// `Float64`: the f64 bit-pattern split into two u32 pieces so it fits
/// in the u32-typed `extra` array.
pub const Float64 = extern struct {
    piece0: u32,
    piece1: u32,

    pub fn pack(value: f64) Float64 {
        const bits: u64 = @bitCast(value);
        return .{
            .piece0 = @truncate(bits),
            .piece1 = @truncate(bits >> 32),
        };
    }

    pub fn get(self: Float64) f64 {
        const bits: u64 = @as(u64, self.piece0) | (@as(u64, self.piece1) << 32);
        return @bitCast(bits);
    }
};

/// Extra-arena payload for `Item.Tag.float_f80` and
/// `Item.Tag.float_c_longdouble_f80`. Mirrors the compiler's `Float80`:
/// the f80 bit-pattern split across two u32 pieces and one u16 piece
/// (zero-padded to a u32 slot).
pub const Float80 = extern struct {
    piece0: u32,
    piece1: u32,
    /// Low u16 carries the high 16 bits of the f80; upper u16 is zero.
    piece2: u32,

    pub fn pack(value: f80) Float80 {
        const bits: u80 = @bitCast(value);
        return .{
            .piece0 = @truncate(bits),
            .piece1 = @truncate(bits >> 32),
            .piece2 = @truncate(bits >> 64),
        };
    }

    pub fn get(self: Float80) f80 {
        const bits: u80 = @as(u80, self.piece0) |
            (@as(u80, self.piece1) << 32) |
            (@as(u80, self.piece2) << 64);
        return @bitCast(bits);
    }
};

/// Extra-arena payload for `Item.Tag.float_f128`,
/// `Item.Tag.float_c_longdouble_f128`, and
/// `Item.Tag.float_comptime_float`. Mirrors the compiler's `Float128`:
/// the f128 bit-pattern split into four u32 pieces.
pub const Float128 = extern struct {
    piece0: u32,
    piece1: u32,
    piece2: u32,
    piece3: u32,

    pub fn pack(value: f128) Float128 {
        const bits: u128 = @bitCast(value);
        return .{
            .piece0 = @truncate(bits),
            .piece1 = @truncate(bits >> 32),
            .piece2 = @truncate(bits >> 64),
            .piece3 = @truncate(bits >> 96),
        };
    }

    pub fn get(self: Float128) f128 {
        const bits: u128 = @as(u128, self.piece0) |
            (@as(u128, self.piece1) << 32) |
            (@as(u128, self.piece2) << 64) |
            (@as(u128, self.piece3) << 96);
        return @bitCast(bits);
    }
};

gpa: Allocator,
items: std.MultiArrayList(Item),
extra: std.ArrayListUnmanaged(u32),
/// Limb-aligned arena holding `int_positive` / `int_negative` payloads
/// (packed `IntBigHeader` at the head + trailing limbs).
big_int_limbs: std.ArrayListUnmanaged(std.math.big.Limb),
/// Dedup map. Entries are appended in lockstep with `items`, so the
/// map's insertion-order index is the `Item` index (and thus the
/// `Index` enum value). The key is `void` because the canonical Key is
/// reconstructed via `indexToKey`; lookup goes through `KeyAdapter`.
/// Single-shard equivalent of the compiler's sharded `getOrPutKey`.
map: std.AutoArrayHashMapUnmanaged(void, void),

/// Adapter that lets `getOrPutAdapted` hash and compare a `Key` against
/// entries stored as bare `Index`es. Mirrors the role of the compiler's
/// `KeyAdapter`.
const KeyAdapter = struct {
    pool: *const InternPool,

    pub fn hash(self: KeyAdapter, key: Key) u32 {
        return @truncate(key.hash64(self.pool));
    }

    pub fn eql(self: KeyAdapter, key: Key, _: void, b_index: usize) bool {
        const existing = self.pool.indexToKey(@enumFromInt(@as(u32, @intCast(b_index))));
        return key.eql(existing, self.pool);
    }
};

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
    try pool.map.ensureTotalCapacity(gpa, first_dynamic_index);
    try populateWellKnown(&pool);
    assert(pool.items.len == first_dynamic_index);
    assert(pool.map.count() == first_dynamic_index);
    return pool;
}

pub fn deinit(pool: *InternPool) void {
    pool.items.deinit(pool.gpa);
    pool.extra.deinit(pool.gpa);
    pool.big_int_limbs.deinit(pool.gpa);
    pool.map.deinit(pool.gpa);
    pool.* = undefined;
}

/// Comptime well-known table mirroring the compiler's `static_keys` array
/// in `src/InternPool.zig`. Each entry corresponds 1:1 to an `Index`
/// position; `populateWellKnown` iterates and dispatches per Key variant.
const static_keys: [first_dynamic_index]Key = .{
    .{ .int_type = .{ .signedness = .unsigned, .bits = 0 } },
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

    // Untyped `undefined` -- same shape as the compiler.
    .{ .undef = .undefined_type },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .u64 = 0 } } },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .u64 = 1 } } },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .i64 = -1 } } },
    .{ .simple_value = .void },
    .{ .simple_value = .@"unreachable" },
    .{ .simple_value = .null },
    .{ .simple_value = .true },
    .{ .simple_value = .false },
};

fn populateWellKnown(pool: *InternPool) Allocator.Error!void {
    assert(pool.items.len == 0);
    assert(pool.map.count() == 0);

    inline for (static_keys, 0..) |key, expected_position| {
        const index = try pool.get(key);
        // Identity of static_keys position to Index enum value is
        // load-bearing: SimpleType / SimpleValue variant values are pinned
        // via `@intFromEnum(Index.X)`, and Sema's `wellKnownRefToValue`
        // assumes positions 0..44 match `Zir.Inst.Ref`'s well-known set.
        assert(@intFromEnum(index) == expected_position);
    }
}

fn appendIntType(pool: *InternPool, signedness: std.lang.Signedness, bits: u16) void {
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

/// Intern a `Key`, returning a stable `Index`. Dedups against existing
/// entries via `getOrPutAdapted`. Single-threaded equivalent of the
/// compiler's `pub fn get(ip, gpa, io, tid, key) !Index` (the
/// `getOrPutKey` + emit dispatcher in `src/InternPool.zig`).
///
/// Invariant: `map` and `items` are appended in lockstep, so the map's
/// insertion-order `gop.index` equals the `items.len` at the time of
/// the miss (and the resulting `Item`'s position). This is what makes
/// the bare-`void` map sound -- the adapter reconstructs the existing
/// Key from the position alone via `indexToKey`.
pub fn get(pool: *InternPool, key: Key) Allocator.Error!Index {
    const adapter: KeyAdapter = .{ .pool = pool };
    const gop = try pool.map.getOrPutAdapted(pool.gpa, key, adapter);
    if (gop.found_existing) {
        const existing: u32 = @intCast(gop.index);
        assert(existing < pool.items.len);
        return @enumFromInt(existing);
    }
    assert(gop.index == pool.items.len);

    try pool.items.ensureUnusedCapacity(pool.gpa, 1);
    switch (key) {
        .simple_type => |s| appendSimpleType(pool, s),
        .simple_value => |s| appendSimpleValue(pool, s),
        .int_type => |it| appendIntType(pool, it.signedness, it.bits),
        .anyframe_type => |child| appendAnyframeType(pool, child),
        .type_value => |t| pool.items.appendAssumeCapacity(.{
            .tag = .type_value,
            .data = @intFromEnum(t),
        }),
        .undef => |ty| {
            assert(ty != .none);
            pool.items.appendAssumeCapacity(.{
                .tag = .undef,
                .data = @intFromEnum(ty),
            });
        },
        .int => |i| try emitInt(pool, i),
        .float => |f| try emitFloat(pool, f),
        .ptr_type => |pt| try emitPtrType(pool, pt),
        .ptr => |p| try emitPtr(pool, p),
    }

    assert(pool.items.len == gop.index + 1);
    return @enumFromInt(@as(u32, @intCast(gop.index)));
}

/// Look up the `Key` for an `Index`. Mirrors the compiler's
/// `indexToKey` (`src/InternPool.zig`).
pub fn indexToKey(pool: *const InternPool, index: Index) Key {
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
        .int_u8 => intKey(.u8_type, .{ .u64 = item.data }),
        .int_u16 => intKey(.u16_type, .{ .u64 = item.data }),
        .int_u32 => intKey(.u32_type, .{ .u64 = item.data }),
        .int_i32 => intKey(.i32_type, .{ .i64 = @as(i32, @bitCast(item.data)) }),
        .int_usize => intKey(.usize_type, .{ .u64 = item.data }),
        .int_comptime_int_u32 => intKey(.comptime_int_type, .{ .u64 = item.data }),
        .int_comptime_int_i32 => intKey(.comptime_int_type, .{ .i64 = @as(i32, @bitCast(item.data)) }),
        .int_small => intSmallFromExtra(pool, item.data),
        .int_positive => intBigFromArena(pool, item.data, true),
        .int_negative => intBigFromArena(pool, item.data, false),
        .float_f16 => .{ .float = .{
            .ty = .f16_type,
            .storage = .{ .f16 = @bitCast(@as(u16, @intCast(item.data))) },
        } },
        .float_f32 => .{ .float = .{
            .ty = .f32_type,
            .storage = .{ .f32 = @bitCast(item.data) },
        } },
        .float_f64 => .{ .float = .{
            .ty = .f64_type,
            .storage = .{ .f64 = floatFromExtra(pool, Float64, item.data).get() },
        } },
        .float_f80 => .{ .float = .{
            .ty = .f80_type,
            .storage = .{ .f80 = floatFromExtra(pool, Float80, item.data).get() },
        } },
        .float_f128 => .{ .float = .{
            .ty = .f128_type,
            .storage = .{ .f128 = floatFromExtra(pool, Float128, item.data).get() },
        } },
        .float_c_longdouble_f80 => .{ .float = .{
            .ty = .c_longdouble_type,
            .storage = .{ .f80 = floatFromExtra(pool, Float80, item.data).get() },
        } },
        .float_c_longdouble_f128 => .{ .float = .{
            .ty = .c_longdouble_type,
            .storage = .{ .f128 = floatFromExtra(pool, Float128, item.data).get() },
        } },
        .float_comptime_float => .{ .float = .{
            .ty = .comptime_float_type,
            .storage = .{ .f128 = floatFromExtra(pool, Float128, item.data).get() },
        } },
        .undef => .{ .undef = @enumFromInt(item.data) },
        .type_value => .{ .type_value = @enumFromInt(item.data) },
        .type_pointer => ptrTypeFromExtra(pool, item.data),
        .ptr_comptime_alloc => ptrComptimeAllocFromExtra(pool, item.data),
    };
}

fn ptrTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = comptime @divExact(@sizeOf(PtrTypeRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    const repr: PtrTypeRepr = .{ .child = slice[0], .sentinel = slice[1], .flags = slice[2] };
    return .{ .ptr_type = .{
        .child = @enumFromInt(repr.child),
        .sentinel = @enumFromInt(repr.sentinel),
        .flags = @bitCast(repr.flags),
    } };
}

fn ptrComptimeAllocFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = comptime @divExact(@sizeOf(PtrComptimeAllocRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    const byte_offset = (@as(u64, slice[3]) << 32) | @as(u64, slice[2]);
    return .{ .ptr = .{
        .ty = @enumFromInt(slice[0]),
        .base_addr = .{ .comptime_alloc = @enumFromInt(slice[1]) },
        .byte_offset = byte_offset,
    } };
}

/// Reconstruct a packed `Float64` / `Float80` / `Float128` from `extra`.
/// The struct is stored as `@sizeOf(T) / 4` consecutive u32 slots.
fn floatFromExtra(pool: *const InternPool, comptime T: type, extra_index: u32) T {
    const pieces_len = comptime @divExact(@sizeOf(T), @sizeOf(u32));
    assert(extra_index + pieces_len <= pool.extra.items.len);
    const pieces: [pieces_len]u32 = pool.extra.items[extra_index..][0..pieces_len].*;
    return @bitCast(pieces);
}

inline fn intKey(ty: Index, storage: Key.Int.Storage) Key {
    return .{ .int = .{ .ty = ty, .storage = storage } };
}

fn intSmallFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 2 <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..2];
    const ty: Index = @enumFromInt(slice[0]);
    return intKey(ty, .{ .u64 = slice[1] });
}

/// Reconstruct an `int_positive` / `int_negative` Key. Mirrors the
/// compiler's `indexToKeyBigInt` (`src/InternPool.zig`): on read, a
/// big-int whose value fits in `u64` (or `i64` when negative) is
/// re-surfaced as the matching inline storage variant so the read-side
/// shape stays symmetric with the intern-side compression. Required for
/// future dedup: hashing an inserted Key as `.u64=x` must agree with
/// hashing the reconstructed Key.
fn intBigFromArena(pool: *const InternPool, limb_index: u32, positive: bool) Key {
    const header_end = limb_index + IntBigHeader.limbs_items_len;
    assert(header_end <= pool.big_int_limbs.items.len);

    const header_slice = pool.big_int_limbs.items[limb_index..][0..IntBigHeader.limbs_items_len];
    const header: IntBigHeader = @bitCast(header_slice.*);
    const limbs_len = header.limbs_len;
    assert(limbs_len > 0);

    const limbs_end = header_end + limbs_len;
    assert(limbs_end <= pool.big_int_limbs.items.len);
    const limbs = pool.big_int_limbs.items[header_end..limbs_end];

    const big_int: BigIntConst = .{ .limbs = limbs, .positive = positive };
    const storage: Key.Int.Storage = if (big_int.toInt(u64)) |x|
        .{ .u64 = x }
    else |_| if (big_int.toInt(i64)) |x|
        .{ .i64 = x }
    else |_|
        .{ .big_int = big_int };

    return intKey(@enumFromInt(header.ty), storage);
}

/// Intern a fixed-width integer type. Well-known widths dedup to their
/// reserved well-known `Index` through the `get` map. Zig permits
/// `u0`..`u65535` / `i0`..`i65535` -- the language limit is the `u16`
/// width of `std.lang.Type.Int.bits`.
pub fn internIntType(
    pool: *InternPool,
    signedness: std.lang.Signedness,
    bits: u16,
) Allocator.Error!Index {
    return pool.get(.{ .int_type = .{ .signedness = signedness, .bits = bits } });
}

/// Emit the `Item` (and any extra / limbs) for a `Key.int`. Mirrors the
/// `.int =>` arm of the compiler's `intern` (`src/InternPool.zig`): one
/// labelled-block switch on `ty` for the type-specialised inline tags,
/// then a fallthrough switch on `storage` for `int_small` or
/// `int_positive` / `int_negative`. Callers must have ensured one item
/// of capacity -- only reachable from `get`'s miss path.
fn emitInt(pool: *InternPool, int: Key.Int) Allocator.Error!void {
    assert(isIntegerType(pool, int.ty));
    const ty = int.ty;

    b: {
        switch (ty) {
            .u8_type => switch (int.storage) {
                .big_int => |big_int| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u8,
                        .data = big_int.toInt(u8) catch unreachable,
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u8,
                        .data = @as(u8, @intCast(x)),
                    });
                    break :b;
                },
            },
            .u16_type => switch (int.storage) {
                .big_int => |big_int| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u16,
                        .data = big_int.toInt(u16) catch unreachable,
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u16,
                        .data = @as(u16, @intCast(x)),
                    });
                    break :b;
                },
            },
            .u32_type => switch (int.storage) {
                .big_int => |big_int| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u32,
                        .data = big_int.toInt(u32) catch unreachable,
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u32,
                        .data = @as(u32, @intCast(x)),
                    });
                    break :b;
                },
            },
            .i32_type => switch (int.storage) {
                .big_int => |big_int| {
                    const casted = big_int.toInt(i32) catch unreachable;
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_i32,
                        .data = @as(u32, @bitCast(casted)),
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_i32,
                        .data = @as(u32, @bitCast(@as(i32, @intCast(x)))),
                    });
                    break :b;
                },
            },
            .usize_type => switch (int.storage) {
                .big_int => |big_int| if (big_int.toInt(u32)) |casted| {
                    pool.items.appendAssumeCapacity(.{ .tag = .int_usize, .data = casted });
                    break :b;
                } else |_| {},
                inline .u64, .i64 => |x| if (std.math.cast(u32, x)) |casted| {
                    pool.items.appendAssumeCapacity(.{ .tag = .int_usize, .data = casted });
                    break :b;
                },
            },
            .comptime_int_type => switch (int.storage) {
                .big_int => |big_int| {
                    if (big_int.toInt(u32)) |casted| {
                        pool.items.appendAssumeCapacity(.{ .tag = .int_comptime_int_u32, .data = casted });
                        break :b;
                    } else |_| {}
                    if (big_int.toInt(i32)) |casted| {
                        pool.items.appendAssumeCapacity(.{
                            .tag = .int_comptime_int_i32,
                            .data = @as(u32, @bitCast(casted)),
                        });
                        break :b;
                    } else |_| {}
                },
                inline .u64, .i64 => |x| {
                    if (std.math.cast(u32, x)) |casted| {
                        pool.items.appendAssumeCapacity(.{ .tag = .int_comptime_int_u32, .data = casted });
                        break :b;
                    }
                    if (std.math.cast(i32, x)) |casted| {
                        pool.items.appendAssumeCapacity(.{
                            .tag = .int_comptime_int_i32,
                            .data = @as(u32, @bitCast(casted)),
                        });
                        break :b;
                    }
                },
            },
            else => {},
        }

        switch (int.storage) {
            .big_int => |big_int| {
                if (big_int.toInt(u32)) |casted| {
                    const extra_index: u32 = @intCast(pool.extra.items.len);
                    try pool.extra.appendSlice(pool.gpa, &.{ @intFromEnum(ty), casted });
                    pool.items.appendAssumeCapacity(.{ .tag = .int_small, .data = extra_index });
                    break :b;
                } else |_| {}
                try addBigInt(pool, ty, big_int);
            },
            inline .u64, .i64 => |x| {
                if (std.math.cast(u32, x)) |casted| {
                    const extra_index: u32 = @intCast(pool.extra.items.len);
                    try pool.extra.appendSlice(pool.gpa, &.{ @intFromEnum(ty), casted });
                    pool.items.appendAssumeCapacity(.{ .tag = .int_small, .data = extra_index });
                    break :b;
                }
                var buf: Key.Int.Storage.BigIntSpace = undefined;
                const big_int = std.math.big.int.Mutable.init(&buf.limbs, x).toConst();
                try addBigInt(pool, ty, big_int);
            },
        }
    }
}

/// Intern an integer value with any storage form.
pub fn internInt(pool: *InternPool, int: Key.Int) Allocator.Error!Index {
    return pool.get(.{ .int = int });
}

/// Emit the `Item` (and any extra) for a `Key.float`. Mirrors the
/// `.float =>` arm of the compiler's `intern` (`src/InternPool.zig`):
/// outer switch on `float.ty`; the c_longdouble arm picks a tag based
/// on storage variant (f80 -> its own tag, otherwise promoted to f128);
/// comptime_float always stores as f128. Callers must have ensured one
/// item of capacity -- only reachable from `get`'s miss path.
fn emitFloat(pool: *InternPool, float: Key.Float) Allocator.Error!void {
    assert(isFloatType(float.ty));
    switch (float.ty) {
        .f16_type => {
            assert(float.storage == .f16);
            pool.items.appendAssumeCapacity(.{
                .tag = .float_f16,
                .data = @as(u16, @bitCast(float.storage.f16)),
            });
        },
        .f32_type => {
            assert(float.storage == .f32);
            pool.items.appendAssumeCapacity(.{
                .tag = .float_f32,
                .data = @as(u32, @bitCast(float.storage.f32)),
            });
        },
        .f64_type => {
            assert(float.storage == .f64);
            const extra_index = try addFloatExtra(pool, Float64.pack(float.storage.f64));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f64, .data = extra_index });
        },
        .f80_type => {
            assert(float.storage == .f80);
            const extra_index = try addFloatExtra(pool, Float80.pack(float.storage.f80));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f80, .data = extra_index });
        },
        .f128_type => {
            assert(float.storage == .f128);
            const extra_index = try addFloatExtra(pool, Float128.pack(float.storage.f128));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f128, .data = extra_index });
        },
        .c_longdouble_type => switch (float.storage) {
            .f80 => |v| {
                const extra_index = try addFloatExtra(pool, Float80.pack(v));
                pool.items.appendAssumeCapacity(.{
                    .tag = .float_c_longdouble_f80,
                    .data = extra_index,
                });
            },
            inline .f16, .f32, .f64, .f128 => |v| {
                const extra_index = try addFloatExtra(pool, Float128.pack(@floatCast(v)));
                pool.items.appendAssumeCapacity(.{
                    .tag = .float_c_longdouble_f128,
                    .data = extra_index,
                });
            },
        },
        .comptime_float_type => {
            assert(float.storage == .f128);
            const extra_index = try addFloatExtra(pool, Float128.pack(float.storage.f128));
            pool.items.appendAssumeCapacity(.{
                .tag = .float_comptime_float,
                .data = extra_index,
            });
        },
        else => unreachable,
    }
}

/// Append a packed Float64/Float80/Float128 to `extra` and return its
/// starting u32 index. The struct is laid out as `@sizeOf(T) / 4`
/// consecutive u32 slots.
fn addFloatExtra(pool: *InternPool, value: anytype) Allocator.Error!u32 {
    const T = @TypeOf(value);
    const pieces_len = comptime @divExact(@sizeOf(T), @sizeOf(u32));
    const pieces: [pieces_len]u32 = @bitCast(value);
    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.appendSlice(pool.gpa, &pieces);
    return extra_index;
}

/// Intern a float value with any storage form.
pub fn internFloat(pool: *InternPool, float: Key.Float) Allocator.Error!Index {
    return pool.get(.{ .float = float });
}

/// Emit a `type_pointer` Item. Three u32 slots in extra:
/// child Index, sentinel Index, packed-flags as u32.
fn emitPtrType(pool: *InternPool, pt: Key.PtrType) Allocator.Error!void {
    assert(pt.child != .none);
    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.appendSlice(pool.gpa, &.{
        @intFromEnum(pt.child),
        @intFromEnum(pt.sentinel),
        @as(u32, @bitCast(pt.flags)),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_pointer, .data = extra_index });
}

/// Emit a `ptr_alloc` Item for a `Key.ptr` whose base address is an
/// `comptime_alloc`. Four u32 slots: ty, alloc_index, byte_offset
/// (lo/hi).
fn emitPtr(pool: *InternPool, p: Key.Ptr) Allocator.Error!void {
    assert(p.ty != .none);
    switch (p.base_addr) {
        .comptime_alloc => |idx| {
            const extra_index: u32 = @intCast(pool.extra.items.len);
            try pool.extra.appendSlice(pool.gpa, &.{
                @intFromEnum(p.ty),
                @intFromEnum(idx),
                @as(u32, @truncate(p.byte_offset)),
                @as(u32, @truncate(p.byte_offset >> 32)),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_comptime_alloc, .data = extra_index });
        },
    }
}

/// Intern a pointer type.
pub fn internPtrType(pool: *InternPool, pt: Key.PtrType) Allocator.Error!Index {
    return pool.get(.{ .ptr_type = pt });
}

/// Intern a pointer value.
pub fn internPtr(pool: *InternPool, p: Key.Ptr) Allocator.Error!Index {
    return pool.get(.{ .ptr = p });
}

/// True iff `ty` identifies a Zig float type. Mirrors the compiler's
/// `isFloatType`.
fn isFloatType(ty: Index) bool {
    return switch (ty) {
        .f16_type,
        .f32_type,
        .f64_type,
        .f80_type,
        .f128_type,
        .c_longdouble_type,
        .comptime_float_type,
        => true,
        else => false,
    };
}

/// True if `ty` identifies a Zig integer type: any int_type slot, any
/// fixed-width int, comptime_int, usize / isize, or the c_* family.
/// Mirrors the compiler's `isIntegerType`.
fn isIntegerType(pool: *const InternPool, ty: Index) bool {
    return switch (ty) {
        .comptime_int_type,
        .usize_type,
        .isize_type,
        .c_char_type,
        .c_short_type,
        .c_ushort_type,
        .c_int_type,
        .c_uint_type,
        .c_long_type,
        .c_ulong_type,
        .c_longlong_type,
        .c_ulonglong_type,
        => true,
        else => switch (pool.indexToKey(ty)) {
            .int_type => true,
            else => isWellKnownFixedWidthIntType(ty),
        },
    };
}

fn isWellKnownFixedWidthIntType(ty: Index) bool {
    return switch (ty) {
        .u0_type,
        .u1_type,
        .u8_type,
        .i8_type,
        .u16_type,
        .i16_type,
        .u29_type,
        .u32_type,
        .i32_type,
        .u64_type,
        .i64_type,
        .u80_type,
        .u128_type,
        .i128_type,
        .u256_type,
        => true,
        else => false,
    };
}

pub fn internIntValue(
    pool: *InternPool,
    ty: Index,
    value: BigIntConst,
) Allocator.Error!Index {
    return internInt(pool, .{ .ty = ty, .storage = .{ .big_int = value } });
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

/// Append an `int_positive` / `int_negative` item. Mirrors the compiler's
/// `addInt`: packed `IntBigHeader` at the head of a `big_int_limbs` slot,
/// limbs trailing inline. Aliasing-safe: dups through gpa if the source
/// limbs reference the arena itself.
fn addBigInt(pool: *InternPool, ty: Index, value: BigIntConst) Allocator.Error!void {
    assert(ty != .none);
    assert(value.limbs.len > 0);
    assert(value.limbs.len <= std.math.maxInt(u32));

    if (limbsAliasPool(pool, value.limbs)) {
        const copy = try pool.gpa.dupe(std.math.big.Limb, value.limbs);
        defer pool.gpa.free(copy);
        try addBigIntAssumingSafe(pool, ty, copy, value.positive);
        return;
    }
    try addBigIntAssumingSafe(pool, ty, value.limbs, value.positive);
}

fn addBigIntAssumingSafe(
    pool: *InternPool,
    ty: Index,
    limbs: []const std.math.big.Limb,
    positive: bool,
) Allocator.Error!void {
    assert(!limbsAliasPool(pool, limbs));

    const limb_index: u32 = @intCast(pool.big_int_limbs.items.len);
    try pool.big_int_limbs.ensureUnusedCapacity(pool.gpa, IntBigHeader.limbs_items_len + limbs.len);

    const header: IntBigHeader = .{ .ty = @intFromEnum(ty), .limbs_len = @intCast(limbs.len) };
    const header_words: [IntBigHeader.limbs_items_len]std.math.big.Limb = @bitCast(header);
    pool.big_int_limbs.appendSliceAssumeCapacity(&header_words);
    pool.big_int_limbs.appendSliceAssumeCapacity(limbs);

    try pool.items.append(pool.gpa, .{
        .tag = if (positive) .int_positive else .int_negative,
        .data = limb_index,
    });
}

pub fn internComptimeInt(pool: *InternPool, value: BigIntConst) Allocator.Error!Index {
    return pool.internIntValue(.comptime_int_type, value);
}

/// Intern a value whose runtime type is `type` and whose payload is the
/// interned type identified by `ty`. This is how Sema returns "the
/// expression evaluated to a type" results (e.g. `@TypeOf(x)` or the
/// type computed by `typeof_log2_int_type`).
pub fn internTypeValue(pool: *InternPool, ty: Index) Allocator.Error!Index {
    assert(ty != .none);
    return pool.get(.{ .type_value = ty });
}

pub fn itemCount(pool: *const InternPool) u32 {
    return @intCast(pool.items.len);
}

test "well-known types have expected keys" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(@as(u16, 8), pool.indexToKey(.u8_type).int_type.bits);
    try std.testing.expectEqual(@as(u16, 32), pool.indexToKey(.u32_type).int_type.bits);
    try std.testing.expectEqual(std.lang.Signedness.signed, pool.indexToKey(.i32_type).int_type.signedness);

    try std.testing.expectEqual(SimpleType.usize, pool.indexToKey(.usize_type).simple_type);
    try std.testing.expectEqual(SimpleType.c_int, pool.indexToKey(.c_int_type).simple_type);
    try std.testing.expectEqual(SimpleType.f64, pool.indexToKey(.f64_type).simple_type);
    try std.testing.expectEqual(SimpleType.bool, pool.indexToKey(.bool_type).simple_type);
}

test "i0_type and anyframe_type slots match compiler ordering" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // Zir.Inst.Ref has no i0_type slot, so our Index doesn't either.
    // `internIntType(.signed, 0)` therefore allocates a fresh dynamic
    // item rather than landing on a well-known slot.
    const items_before = pool.itemCount();
    const signed_zero_idx = try pool.internIntType(.signed, 0);
    try std.testing.expect(@intFromEnum(signed_zero_idx) >= first_dynamic_index);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());
    try std.testing.expectEqual(@as(u16, 0), pool.indexToKey(signed_zero_idx).int_type.bits);
    try std.testing.expectEqual(std.lang.Signedness.signed, pool.indexToKey(signed_zero_idx).int_type.signedness);

    // anyframe_type with .none child (untyped anyframe) at the position
    // between noreturn_type and null_type.
    try std.testing.expectEqual(Index.none, pool.indexToKey(.anyframe_type).anyframe_type);
}

test "well-known values have expected keys" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(SimpleValue.true, pool.indexToKey(.bool_true).simple_value);
    try std.testing.expectEqual(SimpleValue.false, pool.indexToKey(.bool_false).simple_value);
    try std.testing.expectEqual(SimpleValue.void, pool.indexToKey(.void_value).simple_value);

    const zero = pool.indexToKey(.zero).int;
    try std.testing.expectEqual(Index.comptime_int_type, zero.ty);
    try std.testing.expectEqual(@as(u64, 0), zero.storage.u64);

    const negative_one = pool.indexToKey(.negative_one).int;
    try std.testing.expectEqual(@as(i64, -1), negative_one.storage.i64);
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
    const @"u17" = pool.indexToKey(u17_idx).int_type;
    try std.testing.expectEqual(std.lang.Signedness.unsigned, @"u17".signedness);
    try std.testing.expectEqual(@as(u16, 17), @"u17".bits);

    const u65535_idx = try pool.internIntType(.unsigned, std.math.maxInt(u16));
    const @"u65535" = pool.indexToKey(u65535_idx).int_type;
    try std.testing.expectEqual(@as(u16, std.math.maxInt(u16)), @"u65535".bits);
}

test "internInt big-int storage is aliasing-safe under buffer growth" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // A multi-limb value forces the big-int path; the small int_u8..int_small
    // fast paths would otherwise compress 42 to an inline tag.
    var big_src = [_]std.math.big.Limb{ 0, 1 }; // 2^@bitSizeOf(Limb)
    const a_idx = try pool.internIntValue(.u128_type, .{ .limbs = &big_src, .positive = true });

    // Force `big_int_limbs` to capacity so the next append must
    // reallocate. Without the aliasing guard the subsequent reintern
    // would memcpy from a stale source pointer (the limbs slice we
    // pulled from the just-interned value lives inside the arena).
    while (pool.big_int_limbs.items.len < pool.big_int_limbs.capacity) {
        try pool.big_int_limbs.append(pool.gpa, 0);
    }

    const a_view = pool.indexToKey(a_idx).int.storage.big_int;
    const aliased: BigIntConst = .{ .limbs = a_view.limbs, .positive = false };

    const b_idx = try pool.internIntValue(.u128_type, aliased);
    const b = pool.indexToKey(b_idx).int.storage.big_int;
    try std.testing.expectEqual(@as(usize, 2), b.limbs.len);
    try std.testing.expectEqual(@as(std.math.big.Limb, 0), b.limbs[0]);
    try std.testing.expectEqual(@as(std.math.big.Limb, 1), b.limbs[1]);
    try std.testing.expectEqual(false, b.positive);
}

test "small comptime int compresses to inline tag" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    var limbs = [_]std.math.big.Limb{42};
    const value: BigIntConst = .{ .limbs = &limbs, .positive = true };
    const idx = try pool.internComptimeInt(value);

    // 42 fits in u32 so the compressor picks `int_comptime_int_u32` and
    // surfaces the value as `.storage.u64`, not `.big_int`.
    const round = pool.indexToKey(idx).int;
    try std.testing.expectEqual(Index.comptime_int_type, round.ty);
    try std.testing.expectEqual(@as(u64, 42), round.storage.u64);
}

test "float storage: per-type tags and bit-pattern round-trip" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // f32 inline tag.
    const f32_idx = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = 1.5 } });
    const f32_round = pool.indexToKey(f32_idx).float;
    try std.testing.expectEqual(Index.f32_type, f32_round.ty);
    try std.testing.expectEqual(@as(f32, 1.5), f32_round.storage.f32);

    // f64 extra-arena tag.
    const f64_idx = try pool.internFloat(.{
        .ty = .f64_type,
        .storage = .{ .f64 = 3.141592653589793 },
    });
    const f64_round = pool.indexToKey(f64_idx).float;
    try std.testing.expectEqual(Index.f64_type, f64_round.ty);
    try std.testing.expectEqual(@as(f64, 3.141592653589793), f64_round.storage.f64);

    // f128 extra-arena tag.
    const f128_idx = try pool.internFloat(.{
        .ty = .f128_type,
        .storage = .{ .f128 = 1e30 },
    });
    const f128_round = pool.indexToKey(f128_idx).float;
    try std.testing.expectEqual(Index.f128_type, f128_round.ty);
    try std.testing.expectEqual(@as(f128, 1e30), f128_round.storage.f128);
}

test "float dedup: equal values intern once; equal bit-patterns dedup; differing NaNs do not" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // Same value, same type: single Item.
    const items_before = pool.itemCount();
    const a = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = 2.5 } });
    const b = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = 2.5 } });
    try std.testing.expectEqual(a, b);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    // NaN with identical bit-pattern: dedups. (eql compares bit-patterns,
    // not float equality, so NaN==NaN at the bit level.)
    const nan_bits: u32 = 0x7fc00001;
    const nan1: f32 = @bitCast(nan_bits);
    const nan2: f32 = @bitCast(nan_bits);
    const n1 = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = nan1 } });
    const n2 = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = nan2 } });
    try std.testing.expectEqual(n1, n2);

    // NaN with a different payload bit-pattern: distinct Index.
    const other_nan: f32 = @bitCast(@as(u32, 0x7fc00002));
    const n3 = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = other_nan } });
    try std.testing.expect(n1 != n3);
}

test "undef Key variant: well-known slot and typed undef" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // The well-known `Index.undef` slot is untyped undef, i.e. undef
    // whose carrier type is `.undefined_type` -- compiler-exact shape.
    const untyped = pool.indexToKey(.undef).undef;
    try std.testing.expectEqual(Index.undefined_type, untyped);

    // Re-interning the same untyped undef must return the well-known slot,
    // not a fresh dynamic item.
    const round = try pool.get(.{ .undef = .undefined_type });
    try std.testing.expectEqual(Index.undef, round);

    // Typed undef: undef of u32 is a distinct entry and round-trips.
    const u32_undef = try pool.get(.{ .undef = .u32_type });
    try std.testing.expect(u32_undef != .undef);
    try std.testing.expectEqual(Index.u32_type, pool.indexToKey(u32_undef).undef);
}

test "interning identical keys dedups to a single Index" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // Dynamic int_type -- hits the dedup map on the second call.
    const items_before = pool.itemCount();
    const u17_a = try pool.internIntType(.unsigned, 17);
    const u17_b = try pool.internIntType(.unsigned, 17);
    try std.testing.expectEqual(u17_a, u17_b);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    // Storage normalisation: `.u64=5` and `.big_int=+5` (as a single
    // u32-fitting limb) must dedup, because `indexToKey` re-emits the
    // big-int as `.u64` and `Key.hash64` normalises inline storage to
    // BigIntConst before hashing.
    var limb = [_]std.math.big.Limb{5};
    const big5: BigIntConst = .{ .limbs = &limb, .positive = true };
    const a = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = 5 } });
    const b = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .big_int = big5 } });
    try std.testing.expectEqual(a, b);

    // Well-known slots are reached through the same map, so re-interning
    // their key returns the well-known Index (not a fresh dynamic one).
    const zero_again = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = 0 } });
    try std.testing.expectEqual(Index.zero, zero_again);
}

test "big comptime int round-trips through int_positive limbs" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // 2^@bitSizeOf(Limb) -- guaranteed multi-limb, doesn't fit in u64
    // on any host (where Limb >= u32, two limbs always exceed u64).
    var limbs = [_]std.math.big.Limb{ 0, 1 };
    const value: BigIntConst = .{ .limbs = &limbs, .positive = true };
    const idx = try pool.internIntValue(.u128_type, value);

    const round = pool.indexToKey(idx).int;
    try std.testing.expectEqual(Index.u128_type, round.ty);
    const big = round.storage.big_int;
    try std.testing.expect(big.positive);
    try std.testing.expectEqual(@as(usize, 2), big.limbs.len);
    try std.testing.expectEqual(@as(std.math.big.Limb, 0), big.limbs[0]);
    try std.testing.expectEqual(@as(std.math.big.Limb, 1), big.limbs[1]);
}

test "ptr_type round-trip and dedup" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const items_before = pool.itemCount();
    const ty_const_u8 = try pool.internPtrType(.{
        .child = .u8_type,
        .flags = .{ .size = .one, .is_const = true },
    });
    const round = pool.indexToKey(ty_const_u8).ptr_type;
    try std.testing.expectEqual(Index.u8_type, round.child);
    try std.testing.expectEqual(true, round.flags.is_const);
    try std.testing.expectEqual(Key.PtrType.Size.one, round.flags.size);

    // Same shape dedups; differing flag bits intern separately.
    const dedup = try pool.internPtrType(.{
        .child = .u8_type,
        .flags = .{ .size = .one, .is_const = true },
    });
    try std.testing.expectEqual(ty_const_u8, dedup);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    const ty_mut_u8 = try pool.internPtrType(.{
        .child = .u8_type,
        .flags = .{ .size = .one, .is_const = false },
    });
    try std.testing.expect(ty_mut_u8 != ty_const_u8);
}

test "ptr value round-trip and dedup by base_addr + offset" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ptr_ty = try pool.internPtrType(.{ .child = .u32_type });
    const items_before = pool.itemCount();

    const p0 = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(7) },
        .byte_offset = 16,
    });
    const round = pool.indexToKey(p0).ptr;
    try std.testing.expectEqual(ptr_ty, round.ty);
    try std.testing.expectEqual(@as(u64, 16), round.byte_offset);
    try std.testing.expectEqual(@as(Key.ComptimeAllocIndex, @enumFromInt(7)), round.base_addr.comptime_alloc);

    // Same {ty, slot, offset} dedups to the same Index.
    const p_dup = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(7) },
        .byte_offset = 16,
    });
    try std.testing.expectEqual(p0, p_dup);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    // Different offset (or slot) is a distinct value.
    const p_other_offset = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(7) },
        .byte_offset = 24,
    });
    try std.testing.expect(p_other_offset != p0);
}

test "ptr byte_offset survives the 32-bit boundary" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ptr_ty = try pool.internPtrType(.{ .child = .u8_type });
    const huge: u64 = (@as(u64, 1) << 40) + 0xdead;
    const p = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(0) },
        .byte_offset = huge,
    });
    try std.testing.expectEqual(huge, pool.indexToKey(p).ptr.byte_offset);
}

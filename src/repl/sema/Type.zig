//! Thin newtype over `InternPool.Index` that names "this index refers to a
//! type". The pool itself enforces shape; this wrapper only documents intent
//! and gives type-related helpers a place to live.

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");

const Type = @This();

index: InternPool.Index,

pub fn fromIndex(index: InternPool.Index) Type {
    assert(index != .none);
    return .{ .index = index };
}

pub fn toIndex(ty: Type) InternPool.Index {
    return ty.index;
}

/// Returns the `void` type. Always the same interned index.
pub const void_type: Type = .{ .index = .void_type };
pub const bool_type: Type = .{ .index = .bool_type };
pub const type_type: Type = .{ .index = .type_type };
pub const comptime_int_type: Type = .{ .index = .comptime_int_type };

/// The host target -- the one `zig run` selects with no `-target`, so the ABI
/// results below match it. The whole REPL is compiled for, and evaluates as,
/// this single target.
const target: *const std.Target = &builtin.target;

/// ABI alignment of `ty`, or `null` for a type whose layout this subset does
/// not model yet (struct / vector / optional / tuple / error / fn). Mirrors
/// the compiler's `Type.abiAlignment` (src/Type.zig) arm-for-arm over the
/// modelled Keys, delegating to the same `std.zig.target` / `std.Target`
/// rules. Comptime-only and `noreturn` types return a real alignment here (as
/// the compiler's function does); `@alignOf` guards `noreturn` separately.
pub fn abiAlignment(ty: Type, pool: *const InternPool) ?InternPool.Alignment {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => |it| if (it.bits == 0)
            .@"1"
        else
            .fromByteUnits(std.zig.target.intAlignment(target, it.bits)),
        .ptr_type, .anyframe_type => ptrAbiAlignment(),
        .array_type => |at| abiAlignment(fromIndex(at.child), pool),
        .simple_type => |t| switch (t) {
            .bool, .void, .noreturn, .anyopaque, .type, .comptime_int, .comptime_float, .null, .undefined, .enum_literal => .@"1",
            .anyerror => null, // error-set ABI not modelled yet
            .usize, .isize => .fromByteUnits(std.zig.target.intAlignment(target, target.ptrBitWidth())),
            .c_char => cTypeAlign(.char),
            .c_short => cTypeAlign(.short),
            .c_ushort => cTypeAlign(.ushort),
            .c_int => cTypeAlign(.int),
            .c_uint => cTypeAlign(.uint),
            .c_long => cTypeAlign(.long),
            .c_ulong => cTypeAlign(.ulong),
            .c_longlong => cTypeAlign(.longlong),
            .c_ulonglong => cTypeAlign(.ulonglong),
            .c_longdouble => cTypeAlign(.longdouble),
            .f16 => .@"2",
            .f32 => cTypeAlign(.float),
            .f64 => if (target.cTypeBitSize(.double) == 64) cTypeAlign(.double) else .@"8",
            .f80 => if (target.cTypeBitSize(.longdouble) == 80) cTypeAlign(.longdouble) else .fromByteUnits(std.zig.target.intAlignment(target, 80)),
            .f128 => if (target.cTypeBitSize(.longdouble) == 128) cTypeAlign(.longdouble) else .@"16",
            // An internal generic-return marker, never a real `@alignOf` operand.
            .generic_poison => unreachable,
        },
        else => null,
    };
}

/// ABI byte size of `ty`, or `null` for an unmodelled layout (same set as
/// `abiAlignment`). Mirrors the compiler's `Type.abiSize` over the modelled
/// Keys. Comptime-only and uninstantiable simple types return `0` here as the
/// compiler's function does; `@sizeOf` rejects them before calling.
pub fn abiSize(ty: Type, pool: *const InternPool) ?u64 {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => |it| std.zig.target.intByteSize(target, it.bits),
        .ptr_type => |pt| switch (pt.flags.size) {
            .slice => ptrByteSize() * 2,
            .one, .many, .c => ptrByteSize(),
        },
        .anyframe_type => ptrByteSize(),
        .array_type => |at| blk: {
            const child = abiSize(fromIndex(at.child), pool) orelse break :blk null;
            break :blk at.lenIncludingSentinel() * child;
        },
        .simple_type => |t| switch (t) {
            .void, .noreturn, .anyopaque, .type, .comptime_int, .comptime_float, .null, .undefined, .enum_literal => 0,
            .anyerror => null,
            .bool => 1,
            .usize, .isize => ptrByteSize(),
            .c_char => target.cTypeByteSize(.char),
            .c_short => target.cTypeByteSize(.short),
            .c_ushort => target.cTypeByteSize(.ushort),
            .c_int => target.cTypeByteSize(.int),
            .c_uint => target.cTypeByteSize(.uint),
            .c_long => target.cTypeByteSize(.long),
            .c_ulong => target.cTypeByteSize(.ulong),
            .c_longlong => target.cTypeByteSize(.longlong),
            .c_ulonglong => target.cTypeByteSize(.ulonglong),
            .c_longdouble => target.cTypeByteSize(.longdouble),
            .f16 => 2,
            .f32 => 4,
            .f64 => 8,
            .f80 => if (target.cTypeBitSize(.longdouble) == 80) target.cTypeByteSize(.longdouble) else std.zig.target.intByteSize(target, 80),
            .f128 => 16,
            .generic_poison => unreachable,
        },
        else => null,
    };
}

/// `Alignment.fromByteUnits(target.cTypeAlignment(c))` -- the compiler's
/// `cTypeAlign` helper, inlined for the two `abi*` switches.
fn cTypeAlign(c: std.Target.CType) InternPool.Alignment {
    return .fromByteUnits(target.cTypeAlignment(c));
}

/// Pointer ABI alignment/size for the host: the pointer's byte width. Mirrors
/// the compiler's `ptrAbiAlignment` / `ptrAbiSize`, which (off the eZ80, whose
/// 24-bit pointers we never host) is exactly the pointer's byte width.
fn ptrAbiAlignment() InternPool.Alignment {
    return .fromByteUnits(ptrByteSize());
}
fn ptrByteSize() u64 {
    return @divExact(target.ptrBitWidth(), 8);
}

/// Errors writing a type name: I/O, plus the allocation the `error{...}` name
/// sort needs (it dupes the names slice to order them alphabetically).
pub const PrintError = std.Io.Writer.Error || std.mem.Allocator.Error;

/// Write `ty`'s Zig surface-syntax name with no trailing newline (`*const u8`,
/// `error{A,B}!u32`, `fn (u8) void`), recursing on container children. The
/// single type-name printer, the analogue of the compiler's `Type.print`
/// (src/Type.zig). Pointer sentinels and `align(N)` are printed; pointer
/// `address_space` / `vector_index` / `bit_range` prefixes are not yet covered.
pub fn print(ty: Type, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    assert(ty.index != .none);
    switch (pool.indexToKey(ty.index)) {
        // Most simple types print as their tag name; the three literal types
        // have surface-syntax names that differ from the tag, matching the
        // compiler's Type.print (src/Type.zig).
        .simple_type => |st| switch (st) {
            .null => try writer.writeAll("@TypeOf(null)"),
            .undefined => try writer.writeAll("@TypeOf(undefined)"),
            .enum_literal => try writer.writeAll("@EnumLiteral()"),
            else => try writer.print("{s}", .{@tagName(st)}),
        },
        .int_type => |it| try writer.print("{c}{d}", .{
            @as(u8, switch (it.signedness) {
                .signed => 'i',
                .unsigned => 'u',
            }),
            it.bits,
        }),
        .anyframe_type => |child| if (child == .none)
            try writer.writeAll("anyframe")
        else {
            try writer.writeAll("anyframe->");
            try print(fromIndex(child), pool, writer);
        },
        .ptr_type => |pt| try printPtr(pt, pool, writer),
        .error_set_type => |es| try printErrorSet(es, pool, writer),
        .error_union_type => |eu| try printErrorUnion(eu, pool, writer),
        .func_type => |ft| try printFunc(ft, pool, writer),
        .array_type => |at| try printArray(at, pool, writer),
        .vector_type => |vt| try printVector(vt, pool, writer),
        .opt_type => |child| {
            try writer.writeAll("?");
            try print(fromIndex(child), pool, writer);
        },
        .tuple_type => |tt| try printTuple(tt, pool, writer),
        // Nominal types print their fully-qualified `name`, baked at creation.
        .struct_type => |st| try writer.writeAll(pool.stringSlice(st.name)),
        .enum_type => |et| try writer.writeAll(pool.stringSlice(et.name)),
        .union_type => |ut| try writer.writeAll(pool.stringSlice(ut.name)),
        // Unhandled *type* Keys (opaque, ...) aren't rendered yet. A value Key
        // reaching a type printer is a bug, so assert it's a type.
        else => |other| {
            assert(other.isType());
            try writer.writeAll("<type>");
        },
    }
}

/// Whether two values of this type can be compared with each other -- `==`/`!=`
/// when `is_equality_cmp`, `<`/`>`/... otherwise. Verbatim port of the compiler's
/// `Type.isSelfComparable` (src/Type.zig), keyed on the pool Key in place of
/// `zigTypeTag`. The REPL models no `packed`/`opaque`/`frame`/`anyframe` values,
/// so those fold to the same `false`/`is_equality_cmp` result the compiler gives.
/// Used by the array-sentinel type check (`checkSentinelType`).
pub fn isSelfComparable(ty: Type, pool: *const InternPool, is_equality_cmp: bool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => true,
        .simple_type => |s| switch (s) {
            .usize, .isize, .c_char, .c_short, .c_ushort, .c_int, .c_uint, .c_long, .c_ulong, .c_longlong, .c_ulonglong, .comptime_int, // .int / .comptime_int
            .f16, .f32, .f64, .f80, .f128, .c_longdouble, .comptime_float, // .float / .comptime_float
            => true,
            .bool, .type, .void, .anyerror, .enum_literal, .anyopaque => is_equality_cmp,
            .noreturn, .undefined, .null, .generic_poison => false,
        },
        .vector_type => |vt| fromIndex(vt.child).isSelfComparable(pool, is_equality_cmp),
        .enum_type, .error_set_type, .func_type, .anyframe_type => is_equality_cmp,
        .error_union_type, .array_type => false,
        // The REPL has only auto-layout aggregates; a non-packed struct/union is
        // not self-comparable (the compiler allows `packed` only).
        .struct_type, .union_type, .tuple_type => false,
        .ptr_type => |pt| pt.flags.size != .slice and (is_equality_cmp or pt.flags.size == .c),
        .opt_type => |child| is_equality_cmp and fromIndex(child).isSelfComparable(pool, is_equality_cmp),
        else => false,
    };
}

fn printPtr(pt: InternPool.Key.PtrType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    assert(pt.child != .none);
    try writer.writeAll(switch (pt.flags.size) {
        .one => "*",
        .many => "[*]",
        .slice => "[]",
        .c => "[*c]",
    });
    if (pt.flags.is_allowzero and pt.flags.size != .c) try writer.writeAll("allowzero ");
    // An explicit alignment prints `align(N)`; natural alignment (`.none`)
    // is omitted, matching the compiler's pointer printer.
    if (pt.flags.alignment.toByteUnits()) |bytes| try writer.print("align({d}) ", .{bytes});
    if (pt.flags.is_const) try writer.writeAll("const ");
    if (pt.flags.is_volatile) try writer.writeAll("volatile ");
    try print(fromIndex(pt.child), pool, writer);
}

/// `[N]T` or `[N:s]T`. The sentinel prints via its integer literal text for
/// the current numeric subset; other sentinel kinds fall back to `?`.
fn printArray(at: InternPool.Key.ArrayType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try writer.print("[{d}", .{at.len});
    if (at.sentinel != .none) {
        try writer.writeAll(":");
        switch (pool.indexToKey(at.sentinel)) {
            .int => |iv| {
                var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                try writer.print("{f}", .{iv.storage.toBigInt(&space)});
            },
            else => try writer.writeAll("?"),
        }
    }
    try writer.writeAll("]");
    try print(fromIndex(at.child), pool, writer);
}

/// `struct { T0, T1, ... }`; an empty tuple is `struct {}` (matching `@typeName`).
fn printTuple(tt: InternPool.Key.TupleType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    if (tt.types.len == 0) {
        try writer.writeAll("struct {}");
        return;
    }
    try writer.writeAll("struct { ");
    for (tt.types, 0..) |field_ty, i| {
        if (i != 0) try writer.writeAll(", ");
        try print(fromIndex(field_ty), pool, writer);
    }
    try writer.writeAll(" }");
}

/// `@Vector(N, T)`.
fn printVector(vt: InternPool.Key.VectorType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try writer.print("@Vector({d}, ", .{vt.len});
    try print(fromIndex(vt.child), pool, writer);
    try writer.writeAll(")");
}

/// `[noinline] fn ([comptime|noalias] P0, ...[, ...]) [callconv(.@"name")] R`.
/// CC is omitted when `.auto`. Per-param `comptime`/`noalias` come from the
/// FuncType bitmasks (first 32 params).
fn printFunc(ft: InternPool.Key.FuncType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    if (ft.is_noinline) try writer.writeAll("noinline ");
    try writer.writeAll("fn (");
    for (ft.param_types, 0..) |p, i| {
        if (i != 0) try writer.writeAll(", ");
        // Only the first 32 params have flag bits; std.math.cast succeeds IFF
        // `i` fits the u5 index `paramIsComptime`/`paramIsNoalias` take.
        if (std.math.cast(u5, i)) |idx| {
            if (ft.paramIsComptime(idx)) try writer.writeAll("comptime ");
            if (ft.paramIsNoalias(idx)) try writer.writeAll("noalias ");
        }
        try print(fromIndex(p), pool, writer);
    }
    if (ft.is_var_args) {
        try writer.writeAll(if (ft.param_types.len > 0) ", ..." else "...");
    }
    try writer.writeAll(") ");
    const cc_tag: std.lang.CallingConvention.Tag = ft.cc;
    if (cc_tag != .auto) {
        const name = @tagName(cc_tag);
        // Escape only names that are Zig keywords (`.@"async"`), as the
        // value-printer does, so render output stays byte-equal with `zig run`.
        if (std.zig.Token.getKeyword(name) != null) {
            try writer.print("callconv(.@\"{s}\") ", .{name});
        } else {
            try writer.print("callconv(.{s}) ", .{name});
        }
    }
    try print(fromIndex(ft.return_type), pool, writer);
}

fn printErrorUnion(eu: InternPool.Key.ErrorUnionType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try print(fromIndex(eu.error_set_type), pool, writer);
    try writer.writeAll("!");
    try print(fromIndex(eu.payload_type), pool, writer);
}

fn printErrorSet(es: InternPool.Key.ErrorSetType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    // Display wants the members byte-sorted, but the pool stores them id-sorted,
    // so a sortable copy is needed. A stack buffer holds the common small set
    // (0-alloc); only an unusually large error set falls back to the heap.
    var stack_buf: [32]InternPool.NullTerminatedString = undefined;
    const on_heap = es.names.len > stack_buf.len;
    const sorted = if (on_heap)
        try pool.gpa.dupe(InternPool.NullTerminatedString, es.names)
    else sorted: {
        @memcpy(stack_buf[0..es.names.len], es.names);
        break :sorted stack_buf[0..es.names.len];
    };
    defer if (on_heap) pool.gpa.free(sorted);
    std.mem.sortUnstable(InternPool.NullTerminatedString, sorted, pool, lessThanByBytes);

    try writer.writeAll("error{");
    for (sorted, 0..) |name, i| {
        if (i != 0) try writer.writeAll(",");
        try writer.writeAll(pool.stringSlice(name));
    }
    try writer.writeAll("}");
}

fn lessThanByBytes(
    pool: *const InternPool,
    a: InternPool.NullTerminatedString,
    b: InternPool.NullTerminatedString,
) bool {
    return std.mem.lessThan(u8, pool.stringSlice(a), pool.stringSlice(b));
}

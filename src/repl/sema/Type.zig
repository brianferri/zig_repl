//! Thin newtype over `InternPool.Index` that names "this index refers to a
//! type". The pool itself enforces shape; this wrapper only documents intent
//! and gives type-related helpers a place to live.

const std = @import("std");
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

/// Errors writing a type name: I/O, plus the allocation the `error{...}` name
/// sort needs (it dupes the names slice to order them alphabetically).
pub const PrintError = std.Io.Writer.Error || std.mem.Allocator.Error;

/// Write `ty`'s Zig surface-syntax name with no trailing newline (`*const u8`,
/// `error{A,B}!u32`, `fn (u8) void`), recursing on container children. The
/// single type-name printer, the analogue of the compiler's `Type.print`
/// (src/Type.zig); covers the supported cases (no sentinel / align /
/// address_space / vector_index / bit_range prefixes).
pub fn print(ty: Type, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    assert(ty.index != .none);
    switch (pool.indexToKey(ty.index)) {
        .simple_type => |st| try writer.print("{s}", .{@tagName(st)}),
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
        // `name` is the fully-qualified name baked at creation, printed verbatim.
        .struct_type => |st| try writer.writeAll(pool.stringSlice(st.name)),
        // Unhandled *type* Keys (enum/union/opaque, ...) aren't rendered yet.
        // A value Key reaching a type printer is a bug, so assert it's a type.
        else => |other| {
            assert(other.isType());
            try writer.writeAll("<type>");
        },
    }
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

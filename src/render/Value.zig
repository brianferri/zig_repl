//! Writes a Sema-produced Value to a writer in REPL display form. Initial
//! coverage is integers (via std.math.big.int.Const.format) and the
//! simple values void/true/false/null/undefined/unreachable. As Key
//! variants land, add their renderers here.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("../sema/InternPool.zig");
const Value = @import("../sema/Value.zig");

/// Error union for renderers. Includes Writer.Error for the I/O
/// path plus Allocator.Error for renderers that need a scratch
/// buffer (currently only `writeErrorSetTypeName`, which dupes the
/// names slice for an alphabetical sort).
pub const Error = std.Io.Writer.Error || std.mem.Allocator.Error;

pub fn render(
    value: Value,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    assert(value.index != .none);

    const key = pool.indexToKey(value.index);
    return switch (key) {
        .int => |iv| {
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const big = iv.storage.toBigInt(&space);
            return writer.print("{f}\n", .{big});
        },
        .float => |fv| renderFloat(fv, writer),
        .simple_value => |sv| writer.print("{s}\n", .{simpleValueText(sv)}),
        .undef => writer.writeAll("undefined\n"),
        .type_value => |ty_idx| renderTypeRef(ty_idx, pool, writer),
        // A bare type Key viewed as a value identifies the type itself
        // (Sema's value-of-type-type convention; see Value.typeOf).
        .simple_type,
        .int_type,
        .anyframe_type,
        .ptr_type,
        .error_set_type,
        .error_union_type,
        => renderTypeRef(value.index, pool, writer),
        .ptr => |p| writer.print("ptr@{d}+{d}\n", .{ @intFromEnum(p.ty), p.byte_offset }),
        .err => |e| writer.print("error.{s}\n", .{pool.stringSlice(e.name)}),
        .error_union => |eu| renderErrorUnion(eu, pool, writer),
    };
}

fn renderErrorUnion(
    eu: InternPool.Key.ErrorUnion,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    switch (eu.val) {
        .err_name => |name| try writer.print("error.{s}\n", .{pool.stringSlice(name)}),
        .payload => |idx| try render(.{ .index = idx }, pool, writer),
    }
}

fn simpleValueText(sv: InternPool.SimpleValue) []const u8 {
    return switch (sv) {
        .void => "{}",
        .null => "null",
        .true => "true",
        .false => "false",
        .@"unreachable" => "unreachable",
    };
}

/// Render a type Index as its Zig surface-syntax name with a trailing
/// newline (the REPL-line terminator). Used both by the top-level
/// `render` for type-valued results and as a recursion entry point;
/// the inner `writeTypeName` writes without the newline so it can
/// nest inside container-type names (`*const u8`, etc.) without
/// emitting embedded newlines.
fn renderTypeRef(
    type_index: InternPool.Index,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    try writeTypeName(type_index, pool, writer);
    try writer.writeAll("\n");
}

/// Write a type Index's Zig surface-syntax name (no trailing newline).
/// Recurses on pointer / anyframe children. Matches the canonical
/// print form used by the compiler's `Type.print` for the cases
/// Stage 2 ships (no sentinel, no align, no address_space prefix,
/// no vector_index, no bit_range).
pub fn writeTypeName(
    type_index: InternPool.Index,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    assert(type_index != .none);
    switch (pool.indexToKey(type_index)) {
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
            try writeTypeName(child, pool, writer);
        },
        .ptr_type => |pt| try writePtrTypeName(pt, pool, writer),
        .error_set_type => |es| try writeErrorSetTypeName(es, pool, writer),
        .error_union_type => |eu| try writeErrorUnionTypeName(eu, pool, writer),
        else => try writer.writeAll("<type>"),
    }
}

fn writeErrorUnionTypeName(
    eu: InternPool.Key.ErrorUnionType,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    try writeTypeName(eu.error_set_type, pool, writer);
    try writer.writeAll("!");
    try writeTypeName(eu.payload_type, pool, writer);
}

fn writeErrorSetTypeName(
    es: InternPool.Key.ErrorSetType,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    const sorted = try pool.gpa.dupe(InternPool.NullTerminatedString, es.names);
    defer pool.gpa.free(sorted);
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

fn writePtrTypeName(
    pt: InternPool.Key.PtrType,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
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
    try writeTypeName(pt.child, pool, writer);
}

/// Print each float-storage variant in its native precision. f80 has no
/// dedicated `std.fmt` formatter, so we widen to f128 for display only;
/// the stored value keeps its precision.
///
/// `std.fmt`'s `{d}` strips the trailing decimal for integral values
/// (`4.0` -> "4"), which is ambiguous next to integers in REPL output.
/// We restore the `.0` when the printed form has no decimal exponent or
/// dot -- but leave NaN / inf / -inf untouched.
fn renderFloat(
    float: InternPool.Key.Float,
    writer: *std.Io.Writer,
) Error!void {
    var buf: [128]u8 = undefined;
    const text = switch (float.storage) {
        .f16 => |v| std.fmt.bufPrint(&buf, "{d}", .{v}) catch unreachable,
        .f32 => |v| std.fmt.bufPrint(&buf, "{d}", .{v}) catch unreachable,
        .f64 => |v| std.fmt.bufPrint(&buf, "{d}", .{v}) catch unreachable,
        .f80 => |v| std.fmt.bufPrint(&buf, "{d}", .{@as(f128, @floatCast(v))}) catch unreachable,
        .f128 => |v| std.fmt.bufPrint(&buf, "{d}", .{v}) catch unreachable,
    };
    try writer.writeAll(text);
    if (needsTrailingDecimal(text)) try writer.writeAll(".0");
    try writer.writeAll("\n");
}

/// True IFF `text` is a finite-magnitude float printed without a decimal
/// point or exponent (e.g. "4", "-7") -- in which case appending ".0"
/// keeps the value visually distinct from an integer. NaN / inf / -inf
/// start with a non-digit and are left alone.
fn needsTrailingDecimal(text: []const u8) bool {
    if (text.len == 0) return false;
    if (std.mem.indexOfAny(u8, text, ".eE") != null) return false;
    const start: usize = if (text[0] == '-' or text[0] == '+') 1 else 0;
    if (start >= text.len) return false;
    return std.ascii.isDigit(text[start]);
}

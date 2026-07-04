//! Writes a Sema-produced Value to a writer in REPL display form. Initial
//! coverage is integers (via std.math.big.int.Const.format) and the
//! simple values void/true/false/null/undefined/unreachable. As Key
//! variants land, add their renderers here.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("../sema/InternPool.zig");
const Value = @import("../sema/Value.zig");
const Type = @import("../sema/Type.zig");

/// Error union for renderers: `Writer.Error` for the I/O path, plus
/// `Allocator.Error` because the type-name path (`Type.print`) allocates to
/// sort `error{...}` member names.
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
        .float => |fv| {
            try renderFloat(fv, writer);
            try writer.writeByte('\n');
        },
        .simple_value => |sv| writer.print("{s}\n", .{simpleValueText(sv)}),
        .undef => writer.writeAll("undefined\n"),
        .opt => |o| if (o.val == .none)
            writer.writeAll("null\n")
        else
            render(.{ .index = o.val }, pool, writer),
        .ptr => |p| writer.print("ptr@{d}+{d}\n", .{ @intFromEnum(p.ty), p.byte_offset }),
        .err => |e| writer.print("error.{s}\n", .{pool.stringSlice(e.name)}),
        .error_union => |eu| renderErrorUnion(eu, pool, writer),
        .func => |f| writer.print("fn@{d}\n", .{@intFromEnum(f.zir_body_inst)}),
        .aggregate => |agg| renderAggregate(agg, pool, writer),
        // The tag name lives in the enum's ZIR, which the renderer cannot reach
        // (same limit as struct field names). Render the underlying integer tag --
        // what `@intFromEnum` yields -- until a ZIR-aware rendering path exists.
        .enum_tag => |et| render(.{ .index = et.int }, pool, writer),
        // A bare type Key viewed as a value identifies the type itself
        // (Sema's value-of-type-type convention; see Value.typeOf). The
        // value Keys above are exhaustive, so the assert turns a future
        // unclassified one into a crash rather than a mis-render as a type.
        else => blk: {
            assert(key.isType());
            break :blk renderTypeRef(value.index, pool, writer);
        },
    };
}

/// Render an aggregate as `{ e0, e1, e2, ... }`. Each element is
/// printed inline without the trailing newline that the top-level
/// `render` would add -- the brace-list is itself one value.
fn renderAggregate(
    agg: InternPool.Key.Aggregate,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    // Tuples print with a leading dot (`.{ ... }`); arrays don't.
    if (pool.indexToKey(agg.ty) == .tuple_type) try writer.writeByte('.');
    try writer.writeAll("{ ");
    // Element count from storage: `.elems` is its own length (structs, whose
    // type carries no field count, always use this); only `.repeated_elem`
    // needs the type's count.
    const count: u64 = switch (agg.storage) {
        .elems => |es| es.len,
        .repeated_elem => pool.aggregateElementCount(agg.ty),
    };
    var i: u64 = 0;
    while (i < count) : (i += 1) {
        if (i > 0) try writer.writeAll(", ");
        const elem_idx: InternPool.Index = switch (agg.storage) {
            .repeated_elem => |e| e,
            .elems => |es| es[@intCast(i)],
        };
        try renderElemInline(elem_idx, pool, writer);
    }
    try writer.writeAll(" }\n");
}

/// Inline-print a value: same as `render` but without the trailing
/// newline. Used by `renderAggregate` so element values compose
/// into the parent brace-list. The current subset is int /
/// simple_value / undef. Unsupported keys render as `<elem>` rather
/// than recurse.
fn renderElemInline(
    elem_idx: InternPool.Index,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    const key = pool.indexToKey(elem_idx);
    switch (key) {
        .int => |iv| {
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const big = iv.storage.toBigInt(&space);
            try writer.print("{f}", .{big});
        },
        .float => |fv| try renderFloat(fv, writer),
        .simple_value => |sv| try writer.writeAll(simpleValueText(sv)),
        .undef => try writer.writeAll("undefined"),
        else => try writer.writeAll("<elem>"),
    }
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
        .void => "void",
        .null => "null",
        .true => "true",
        .false => "false",
        .@"unreachable" => "unreachable",
    };
}

/// Render a type Index as its Zig surface-syntax name with a trailing newline
/// (the REPL-line terminator). The name itself is produced by `Type.print`,
/// the shared type-name printer.
fn renderTypeRef(
    type_index: InternPool.Index,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) Error!void {
    try Type.print(Type.fromIndex(type_index), pool, writer);
    try writer.writeAll("\n");
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
        // f80 has no dedicated {d} formatter; widen to f128 for
        // display only (stored value keeps its precision).
        .f80 => |v| std.fmt.bufPrint(&buf, "{d}", .{@as(f128, @floatCast(v))}) catch unreachable,
        inline else => |v| std.fmt.bufPrint(&buf, "{d}", .{v}) catch unreachable,
    };
    try writer.writeAll(text);
    if (needsTrailingDecimal(text)) try writer.writeAll(".0");
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

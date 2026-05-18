//! Writes a Sema-produced Value to a writer in REPL display form. Initial
//! coverage is integers (via std.math.big.int.Const.format) and the
//! simple values void/true/false/null/undefined/unreachable. As Key
//! variants land, add their renderers here.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("../sema/InternPool.zig");
const Value = @import("../sema/Value.zig");

pub fn render(
    value: Value,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) std.Io.Writer.Error!void {
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
        .simple_type, .int_type, .anyframe_type => renderTypeRef(value.index, pool, writer),
    };
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

fn renderTypeRef(
    type_index: InternPool.Index,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) std.Io.Writer.Error!void {
    const key = pool.indexToKey(type_index);
    return switch (key) {
        .simple_type => |st| writer.print("{s}\n", .{@tagName(st)}),
        .int_type => |it| writer.print("{c}{d}\n", .{
            @as(u8, switch (it.signedness) {
                .signed => 'i',
                .unsigned => 'u',
            }),
            it.bits,
        }),
        .anyframe_type => |child| if (child == .none)
            writer.writeAll("anyframe\n")
        else
            renderAnyframeChild(child, pool, writer),
        else => writer.writeAll("<type>\n"),
    };
}

/// Print each float-storage variant in its native precision. f80 has no
/// dedicated `std.fmt` formatter, so we widen to f128 for display only;
/// the stored value keeps its precision.
///
/// `std.fmt`'s `{d}` strips the trailing decimal for integral values
/// (`4.0` -> "4"), which is ambiguous next to integers in REPL output.
/// We restore the `.0` when the printed form has no decimal exponent or
/// dot — but leave NaN / inf / -inf untouched.
fn renderFloat(
    float: InternPool.Key.Float,
    writer: *std.Io.Writer,
) std.Io.Writer.Error!void {
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

/// True iff `text` is a finite-magnitude float printed without a decimal
/// point or exponent (e.g. "4", "-7") — in which case appending ".0"
/// keeps the value visually distinct from an integer. NaN / inf / -inf
/// start with a non-digit and are left alone.
fn needsTrailingDecimal(text: []const u8) bool {
    if (text.len == 0) return false;
    if (std.mem.indexOfAny(u8, text, ".eE") != null) return false;
    const start: usize = if (text[0] == '-' or text[0] == '+') 1 else 0;
    if (start >= text.len) return false;
    return std.ascii.isDigit(text[start]);
}

fn renderAnyframeChild(
    child: InternPool.Index,
    pool: *const InternPool,
    writer: *std.Io.Writer,
) std.Io.Writer.Error!void {
    try writer.writeAll("anyframe->");
    try renderTypeRef(child, pool, writer);
}

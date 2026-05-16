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

    const key = pool.get(value.index);
    return switch (key) {
        .int_value => |iv| writer.print("{f}\n", .{iv.value}),
        .simple_value => |sv| writer.print("{s}\n", .{simpleValueText(sv)}),
        .type_value => |ty_idx| renderTypeRef(ty_idx, pool, writer),
        .simple_type, .int_type => unreachable, // not values
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
    const key = pool.get(type_index);
    return switch (key) {
        .simple_type => |st| writer.print("{s}\n", .{@tagName(st)}),
        .int_type => |it| writer.print("{c}{d}\n", .{
            @as(u8, switch (it.signedness) {
                .signed => 'i',
                .unsigned => 'u',
            }),
            it.bits,
        }),
        else => writer.writeAll("<type>\n"),
    };
}

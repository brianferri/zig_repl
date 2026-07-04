//! Thin newtype over `InternPool.Index` that names "this index refers to a
//! value". Mirror of `Type` on the value side.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Type = @import("Type.zig");

const Value = @This();

index: InternPool.Index,
/// Whether this value is comptime-known. The evaluator always has a concrete
/// `index` (it substitutes a call's args to evaluate the body), so this is a
/// *provenance* bit: a value built from literals and consts is comptime-known;
/// one derived from a non-`comptime` parameter is not. Coercion needs it -- a
/// comptime-known value coerces value-based (the value must fit), a runtime
/// value type-based (the source *type* must coerce) -- so the body of
/// `fn (a: u32) i32 { return a; }` is rejected as the compiler rejects it.
///
/// The compiler reads this structurally (a comptime value interns, a runtime
/// one is an Air instruction with no constant: `resolveValue(ref) != null`).
/// This evaluator has no Air, so it carries the bit. Seeded from the
/// parameter's `comptime`-ness (`Block.Param.is_comptime` / FuncType
/// `comptime_bits`) and ANDed through each operation that builds a value.
is_comptime: bool = true,

pub fn fromIndex(index: InternPool.Index) Value {
    assert(index != .none);
    return .{ .index = index };
}

pub fn toIndex(val: Value) InternPool.Index {
    return val.index;
}

/// Returns the type of the value, looked up through `pool`.
pub fn typeOf(val: Value, pool: *const InternPool) Type {
    const key = pool.indexToKey(val.index);
    return switch (key) {
        .simple_value => |sv| switch (sv) {
            .void => .void_type,
            .true, .false => .bool_type,
            .null => .{ .index = .null_type },
            .@"unreachable" => .{ .index = .noreturn_type },
        },
        .int => |iv| .{ .index = iv.ty },
        .float => |fv| .{ .index = fv.ty },
        .undef => |ty| .{ .index = ty },
        .ptr => |p| .{ .index = p.ty },
        .err => |e| .{ .index = e.ty },
        .error_union => |eu| .{ .index = eu.ty },
        .func => |f| .{ .index = f.ty },
        .opt => |o| .{ .index = o.ty },
        .aggregate => |agg| .{ .index = agg.ty },
        .enum_tag => |et| .{ .index = et.ty },
        // Every remaining Key is a type used as a value, whose own type is
        // `type`. The value Keys above are exhaustive, so anything reaching
        // here is a type -- the assert turns a future unclassified value Key
        // into a loud crash rather than a silent `.type_type`.
        else => blk: {
            assert(key.isType());
            break :blk .type_type;
        },
    };
}

pub const void_value: Value = .{ .index = .void_value };
pub const bool_true: Value = .{ .index = .bool_true };
pub const bool_false: Value = .{ .index = .bool_false };

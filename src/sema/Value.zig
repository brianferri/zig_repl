//! Thin newtype over `InternPool.Index` that names "this index refers to a
//! value". Mirror of `Type` on the value side.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Type = @import("Type.zig");

const Value = @This();

index: InternPool.Index,

pub fn fromIndex(index: InternPool.Index) Value {
    assert(index != .none);
    return .{ .index = index };
}

pub fn toIndex(val: Value) InternPool.Index {
    return val.index;
}

/// Returns the type of the value, looked up through `pool`.
pub fn typeOf(val: Value, pool: *const InternPool) Type {
    const key = pool.get(val.index);
    return switch (key) {
        .simple_value => |sv| switch (sv) {
            .void => .void_type,
            .bool_true, .bool_false => .bool_type,
            .null => .{ .index = .null_type },
            .undefined => .{ .index = .undefined_type },
        },
        .int_value => |iv| .{ .index = iv.ty },
        .type_value => .type_type,
        .simple_type, .int_type => unreachable, // these are types, not values
    };
}

pub const void_value: Value = .{ .index = .void_value };
pub const bool_true: Value = .{ .index = .bool_true };
pub const bool_false: Value = .{ .index = .bool_false };

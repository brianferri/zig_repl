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

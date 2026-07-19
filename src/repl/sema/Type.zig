const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Sema = @import("Sema.zig");
const Value = @import("Value.zig");

const Type = @This();

index: InternPool.Index,

pub fn minInt(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const pool = sema.intern_pool;
    const scalar = try minIntScalar(ty.scalarType(pool), sema, dest_ty.scalarType(pool));
    return if (ty.zigTypeTag(pool) == .vector) sema.aggregateSplatValue(dest_ty, scalar) else scalar;
}

pub fn minIntScalar(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const info = ty.intInfo(sema.intern_pool);
    if (info.signedness == .unsigned) return sema.intValue_u64(dest_ty, 0);
    if (std.math.cast(u6, info.bits - 1)) |shift| {
        const n = @as(i64, std.math.minInt(i64)) >> (63 - shift);
        return sema.intValue_i64(dest_ty, n);
    }
    var res = try std.math.big.int.Managed.init(sema.gpa);
    defer res.deinit();
    try res.setTwosCompIntLimit(.min, info.signedness, info.bits);
    return sema.intValue_big(dest_ty, res.toConst());
}

pub fn maxInt(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const pool = sema.intern_pool;
    const scalar = try maxIntScalar(ty.scalarType(pool), sema, dest_ty.scalarType(pool));
    return if (ty.zigTypeTag(pool) == .vector) sema.aggregateSplatValue(dest_ty, scalar) else scalar;
}

pub fn maxIntScalar(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const info = ty.intInfo(sema.intern_pool);
    switch (info.bits) {
        0 => return sema.intValue_u64(dest_ty, 0),
        1 => return switch (info.signedness) {
            .signed => sema.intValue_u64(dest_ty, 0),
            .unsigned => sema.intValue_u64(dest_ty, 1),
        },
        else => {},
    }
    if (std.math.cast(u6, info.bits - 1)) |shift| switch (info.signedness) {
        .signed => {
            const n = @as(i64, std.math.maxInt(i64)) >> (63 - shift);
            return sema.intValue_i64(dest_ty, n);
        },
        .unsigned => {
            const n = @as(u64, std.math.maxInt(u64)) >> (63 - shift);
            return sema.intValue_u64(dest_ty, n);
        },
    };
    var res = try std.math.big.int.Managed.init(sema.gpa);
    defer res.deinit();
    try res.setTwosCompIntLimit(.max, info.signedness, info.bits);
    return sema.intValue_big(dest_ty, res.toConst());
}

pub fn onePossibleValue(ty: Type, sema: *Sema) Sema.Error!?Value {
    const ip = sema.intern_pool;
    try sema.ensureLayoutResolved(ty.index);
    return switch (ip.indexToKey(ty.index)) {
        .ptr_type,
        .error_union_type,
        .func_type,
        .anyframe_type,
        .error_set_type,
        .opaque_type,
        => null,

        .simple_type => |t| switch (t) {
            .f16,
            .f32,
            .f64,
            .f80,
            .f128,
            .usize,
            .isize,
            .c_char,
            .c_short,
            .c_ushort,
            .c_int,
            .c_uint,
            .c_long,
            .c_ulong,
            .c_longlong,
            .c_ulonglong,
            .c_longdouble,
            .anyopaque,
            .bool,
            .type,
            .anyerror,
            .comptime_int,
            .comptime_float,
            .enum_literal,
            .adhoc_inferred_error_set,
            .null,
            .undefined,
            .noreturn,
            => null,

            .void => Value.void_value,

            .generic_poison => unreachable,
        },
        .int_type => |int_type| if (int_type.bits == 0) try sema.intValue_u64(ty, 0) else null,
        .array_type => |arr| {
            const has_sentinel = arr.sentinel != .none;
            if (arr.len + @intFromBool(has_sentinel) == 0) return try sema.aggregateValue(ty, &.{});
            if (try Type.fromIndex(arr.child).onePossibleValue(sema)) |opv| return try sema.aggregateSplatValue(ty, opv);
            return null;
        },
        .vector_type => |vec| {
            if (vec.len == 0) return try sema.aggregateValue(ty, &.{});
            if (try Type.fromIndex(vec.child).onePossibleValue(sema)) |opv| return try sema.aggregateSplatValue(ty, opv);
            return null;
        },
        .opt_type => |child| if (try sema.isNoPossibleValue(child))
            .{ .index = try ip.internOpt(.{ .ty = ty.index, .val = .none }) }
        else
            null,
        .enum_type => if (try Type.fromIndex(try sema.enumIntTagTypeOf(ty.index)).onePossibleValue(sema)) |int_tag_opv|
            .{ .index = try ip.internEnumTag(.{ .ty = ty.index, .int = int_tag_opv.index }) }
        else
            null,
        .tuple_type => |tuple| {
            if (ty.classify(ip) != .one_possible_value) return null;
            const field_vals = try sema.arena.dupe(InternPool.Index, tuple.values);
            for (field_vals, tuple.types) |*field_val, field_ty| {
                if (field_val.* != .none) continue;
                field_val.* = (try Type.fromIndex(field_ty).onePossibleValue(sema)).?.index;
            }
            return try sema.aggregateValue(ty, field_vals);
        },
        .struct_type => {
            const struct_obj = ip.loadStructType(ty.index);
            switch (struct_obj.layout) {
                .auto, .@"extern" => {},
                .@"packed" => {
                    const backing_ty: Type = .fromIndex(struct_obj.packed_backing_int_type);
                    const backing_val = try backing_ty.onePossibleValue(sema) orelse return null;
                    return try sema.bitpackValue(ty, backing_val);
                },
            }
            if (ty.classify(ip) != .one_possible_value) return null;
            const field_vals = try sema.arena.alloc(InternPool.Index, struct_obj.field_types.len);
            for (field_vals, 0..) |*field_val, i| {
                if (ty.structFieldIsComptime(i, ip)) {
                    field_val.* = struct_obj.field_defaults[i];
                    assert(field_val.* != .none);
                    continue;
                }
                field_val.* = (try Type.fromIndex(struct_obj.field_types[i]).onePossibleValue(sema)).?.index;
            }
            return try sema.aggregateValue(ty, field_vals);
        },
        .union_type => {
            const union_obj = ip.unionFields(ty.index);
            if (union_obj.layout == .@"packed") {
                const backing_ty: Type = .fromIndex(union_obj.packed_backing_int_type);
                const backing_val = try backing_ty.onePossibleValue(sema) orelse return null;
                return try sema.bitpackValue(ty, backing_val);
            }
            if (ty.classify(ip) != .one_possible_value) return null;
            for (union_obj.field_types, 0..) |field_ty_ip, field_index| {
                const field_ty: Type = .fromIndex(field_ty_ip);
                switch (field_ty.classify(ip)) {
                    .no_possible_value => continue,
                    .one_possible_value => {},
                    else => unreachable,
                }
                const tag_val = (try sema.enumValueFieldIndex(union_obj.enum_tag_type, @intCast(field_index))).?;
                const payload = (try field_ty.onePossibleValue(sema)).?;
                return .{ .index = try ip.internUnion(.{ .ty = ty.index, .tag = tag_val.index, .val = payload.index }) };
            } else unreachable;
        },

        .simple_value,
        .enum_literal,
        .int,
        .float,
        .undef,
        .ptr,
        .slice,
        .err,
        .error_union,
        .func,
        .opt,
        .aggregate,
        .enum_tag,
        .un,
        .bitpack,
        => unreachable,
    };
}

pub fn classify(start_ty: Type, pool: *const InternPool) InternPool.TypeClass {
    var extra_states: enum { none, one, many } = .none;
    var cur_ty = start_ty;
    const base: InternPool.TypeClass = while (true) break switch (pool.indexToKey(cur_ty.index)) {
        .simple_type => |t| switch (t) {
            .f16,
            .f32,
            .f64,
            .f80,
            .f128,
            .usize,
            .isize,
            .c_char,
            .c_short,
            .c_ushort,
            .c_int,
            .c_uint,
            .c_long,
            .c_ulong,
            .c_longlong,
            .c_ulonglong,
            .c_longdouble,
            .bool,
            .anyerror,
            .adhoc_inferred_error_set,
            => .runtime,

            .anyopaque => .no_possible_value,

            .type,
            .comptime_int,
            .comptime_float,
            .enum_literal,
            .null,
            .undefined,
            => .fully_comptime,

            .void => .one_possible_value,
            .noreturn => .no_possible_value,

            .generic_poison => unreachable,
        },

        .error_set_type,
        .ptr_type,
        .anyframe_type,
        => .runtime,

        .func_type => .fully_comptime,

        .opaque_type => .no_possible_value,

        .error_union_type => |eu| {
            extra_states = .many;
            cur_ty = fromIndex(eu.payload_type);
            continue;
        },

        .int_type => |int| switch (int.bits) {
            0 => .one_possible_value,
            else => .runtime,
        },
        .array_type => |arr| {
            if (arr.len == 0 and arr.sentinel == .none) break .one_possible_value;
            cur_ty = fromIndex(arr.child);
            continue;
        },
        .vector_type => |vec| {
            if (vec.len == 0) break .one_possible_value;
            cur_ty = fromIndex(vec.child);
            continue;
        },
        .opt_type => |child_ty| {
            extra_states = switch (extra_states) {
                .none => .one,
                .one, .many => .many,
            };
            cur_ty = fromIndex(child_ty);
            continue;
        },
        .tuple_type => |tuple| break classifyTuple(tuple.types, tuple.values, pool),
        .struct_type => {
            const struct_obj = pool.loadStructType(cur_ty.index);
            switch (struct_obj.layout) {
                .auto, .@"extern" => break struct_obj.class,
                .@"packed" => {
                    cur_ty = fromIndex(struct_obj.packed_backing_int_type);
                    continue;
                },
            }
        },
        .union_type => {
            const union_obj = pool.unionFields(cur_ty.index);
            switch (union_obj.layout) {
                .auto, .@"extern" => break union_obj.class,
                .@"packed" => {
                    cur_ty = fromIndex(union_obj.packed_backing_int_type);
                    continue;
                },
            }
        },
        .enum_type => {
            cur_ty = fromIndex(pool.loadEnumType(cur_ty.index).int_tag_type);
            continue;
        },

        .simple_value,
        .enum_literal,
        .int,
        .float,
        .undef,
        .ptr,
        .slice,
        .err,
        .error_union,
        .func,
        .opt,
        .aggregate,
        .enum_tag,
        .un,
        .bitpack,
        => unreachable,
    };

    return switch (base) {
        .runtime => .runtime,
        .partially_comptime => .partially_comptime,
        .fully_comptime => .fully_comptime,
        .no_possible_value => switch (extra_states) {
            .none => .no_possible_value,
            .one => .one_possible_value,
            .many => .runtime,
        },
        .one_possible_value => switch (extra_states) {
            .none => .one_possible_value,
            .one, .many => .runtime,
        },
    };
}

fn classifyTuple(types: []const InternPool.Index, values: []const InternPool.Index, pool: *const InternPool) InternPool.TypeClass {
    var has_runtime_state = false;
    var has_comptime_state = false;
    for (types, values) |field_ty, field_comptime_val| {
        if (field_comptime_val != .none) continue;
        switch (fromIndex(field_ty).classify(pool)) {
            .no_possible_value => return .no_possible_value,
            .one_possible_value => {},
            .runtime => has_runtime_state = true,
            .fully_comptime => has_comptime_state = true,
            .partially_comptime => {
                has_runtime_state = true;
                has_comptime_state = true;
            },
        }
    }
    if (has_comptime_state) {
        return if (has_runtime_state) .partially_comptime else .fully_comptime;
    } else {
        return if (has_runtime_state) .runtime else .one_possible_value;
    }
}

pub fn containerLayout(ty: Type, pool: *const InternPool) std.lang.Type.ContainerLayout {
    return switch (pool.indexToKey(ty.index)) {
        .tuple_type => .auto,
        .struct_type => pool.loadStructType(ty.index).layout,
        .union_type => pool.unionFields(ty.index).layout,
        else => unreachable,
    };
}

pub fn bitpackBackingInt(ty: Type, pool: *const InternPool) Type {
    return switch (pool.indexToKey(ty.index)) {
        .struct_type => .fromIndex(pool.loadStructType(ty.index).packed_backing_int_type),
        .union_type => .fromIndex(pool.unionFields(ty.index).packed_backing_int_type),
        else => unreachable,
    };
}

pub fn hasRuntimeBits(ty: Type, pool: *const InternPool) bool {
    return switch (ty.classify(pool)) {
        .no_possible_value, .one_possible_value, .fully_comptime => false,
        .runtime, .partially_comptime => true,
    };
}

pub fn isNoReturn(ty: Type, pool: *const InternPool) bool {
    return ty.classify(pool) == .no_possible_value;
}

pub const UnionLayout = struct {
    abi_size: u64,
    abi_align: InternPool.Alignment,
    most_aligned_field: u32,
    most_aligned_field_size: u64,
    biggest_field: u32,
    payload_size: u64,
    payload_align: InternPool.Alignment,
    tag_align: InternPool.Alignment,
    tag_size: u64,
    padding: u32,
};

pub fn getUnionLayout(loaded_union: InternPool.UnionFields, pool: *const InternPool) UnionLayout {
    assert(loaded_union.layout != .@"packed");
    var most_aligned_field: u32 = 0;
    var most_aligned_field_align: InternPool.Alignment = .@"1";
    var most_aligned_field_size: u64 = 0;
    var biggest_field: u32 = 0;
    var payload_size: u64 = 0;
    var payload_align: InternPool.Alignment = .@"1";
    for (loaded_union.field_types, 0..) |field_ty_ip_index, field_index| {
        const field_ty: Type = .fromIndex(field_ty_ip_index);
        if (field_ty.isNoReturn(pool)) continue;

        const field_align: InternPool.Alignment = a: {
            const explicit = loaded_union.field_aligns.getOrNone(field_index);
            if (explicit != .none) break :a explicit;
            break :a field_ty.abiAlignment(pool);
        };
        if (field_ty.hasRuntimeBits(pool)) {
            const field_size = field_ty.abiSize(pool);
            if (field_size > payload_size) {
                payload_size = field_size;
                biggest_field = @intCast(field_index);
            }
            if (field_size > 0 and field_align.compare(.gte, most_aligned_field_align)) {
                most_aligned_field = @intCast(field_index);
                most_aligned_field_align = field_align;
                most_aligned_field_size = field_size;
            }
        }
        payload_align = payload_align.max(field_align);
    }
    if (!loaded_union.has_runtime_tag or
        !Type.fromIndex(loaded_union.enum_tag_type).hasRuntimeBits(pool))
    {
        return .{
            .abi_size = payload_align.forward(payload_size),
            .abi_align = payload_align,
            .most_aligned_field = most_aligned_field,
            .most_aligned_field_size = most_aligned_field_size,
            .biggest_field = biggest_field,
            .payload_size = payload_size,
            .payload_align = payload_align,
            .tag_align = .none,
            .tag_size = 0,
            .padding = 0,
        };
    }

    const tag_size = Type.fromIndex(loaded_union.enum_tag_type).abiSize(pool);
    const tag_align = Type.fromIndex(loaded_union.enum_tag_type).abiAlignment(pool).max(.@"1");
    const abi_size: u64 = loaded_union.size;
    return .{
        .abi_size = abi_size,
        .abi_align = tag_align.max(payload_align),
        .most_aligned_field = most_aligned_field,
        .most_aligned_field_size = most_aligned_field_size,
        .biggest_field = biggest_field,
        .payload_size = payload_size,
        .payload_align = payload_align,
        .tag_align = tag_align,
        .tag_size = tag_size,
        .padding = @intCast(abi_size - tag_size - payload_size),
    };
}

pub fn structFieldOffset(ty: Type, pool: *const InternPool, index: usize) u64 {
    switch (pool.indexToKey(ty.index)) {
        .struct_type => {
            const struct_type = pool.loadStructType(ty.index);
            assert(struct_type.layout != .@"packed");
            return struct_type.field_offsets[index];
        },
        .tuple_type => |tuple| {
            var offset: u64 = 0;
            var big_align: InternPool.Alignment = .none;
            for (tuple.types, tuple.values, 0..) |field_ty, field_val, i| {
                if (field_val != .none or !fromIndex(field_ty).hasRuntimeBits(pool)) {
                    if (i == index) return 0;
                    continue;
                }
                const field_align = fromIndex(field_ty).abiAlignment(pool);
                big_align = big_align.max(field_align);
                offset = field_align.forward(offset);
                if (i == index) return offset;
                offset += fromIndex(field_ty).abiSize(pool);
            }
            offset = big_align.max(.@"1").forward(offset);
            return offset;
        },
        .union_type => {
            const union_type = pool.unionFields(ty.index);
            if (!union_type.has_runtime_tag) return 0;
            const layout = getUnionLayout(union_type, pool);
            if (layout.tag_align.compare(.gte, layout.payload_align)) {
                return layout.payload_align.forward(layout.tag_size);
            } else {
                return 0;
            }
        },
        else => unreachable,
    }
}

pub fn fromIndex(index: InternPool.Index) Type {
    assert(index != .none);
    return .{ .index = index };
}

pub fn toIndex(ty: Type) InternPool.Index {
    assert(ty.index != .none);
    return ty.index;
}

/// Returns the field type. Supports tuples, structs, and unions.
pub fn fieldType(ty: Type, index: usize, pool: *const InternPool) Type {
    const types = switch (pool.indexToKey(ty.index)) {
        .struct_type => types: {
            pool.assertLayoutResolved(ty.index);
            break :types pool.loadStructType(ty.index).field_types;
        },
        .union_type => types: {
            pool.assertLayoutResolved(ty.index);
            break :types pool.unionFields(ty.index).field_types;
        },
        .tuple_type => |tuple| tuple.types,
        else => unreachable,
    };
    return .fromIndex(types[index]);
}

/// If an alignment was explicitly specified for the given field of the struct or union type `ty`,
/// returns that. Otherwise, returns `.none`. This function also supports tuples, for which it
/// always returns `.none`.
pub fn explicitFieldAlignment(ty: Type, index: usize, pool: *const InternPool) InternPool.Alignment {
    return switch (pool.indexToKey(ty.index)) {
        .tuple_type => .none,
        .struct_type => {
            pool.assertLayoutResolved(ty.index);
            const struct_obj = pool.loadStructType(ty.index);
            assert(struct_obj.layout != .@"packed");
            return struct_obj.field_aligns.getOrNone(index);
        },
        .union_type => {
            pool.assertLayoutResolved(ty.index);
            const union_obj = pool.unionFields(ty.index);
            assert(union_obj.layout != .@"packed");
            return union_obj.field_aligns.getOrNone(index);
        },
        else => unreachable,
    };
}

pub fn fieldPtrType(ptr_ty: Type, field_index: u32, pool: *InternPool) std.mem.Allocator.Error!Type {
    const ptr_info = pool.indexToKey(ptr_ty.index).ptr_type;
    assert(ptr_info.flags.size == .one or ptr_info.flags.size == .c);
    const aggregate_ty: Type = .fromIndex(ptr_info.child);
    pool.assertLayoutResolved(aggregate_ty.index);
    const field_ty: Type, const field_align: InternPool.Alignment = switch (aggregate_ty.zigTypeTag(pool)) {
        .@"struct" => switch (aggregate_ty.containerLayout(pool)) {
            .auto => field: {
                if (aggregate_ty.isTuple(pool)) {
                    break :field .{ aggregate_ty.fieldType(field_index, pool), .none };
                }
                const struct_obj = pool.loadStructType(aggregate_ty.index);
                break :field .{
                    .fromIndex(struct_obj.field_types[field_index]),
                    struct_obj.field_aligns.getOrNone(field_index),
                };
            },
            .@"extern" => {
                const extern_field_ty = aggregate_ty.fieldType(field_index, pool);
                const field_offset = aggregate_ty.structFieldOffset(pool, field_index);
                const parent_align = switch (ptr_info.flags.alignment) {
                    .none => aggregate_ty.abiAlignment(pool),
                    else => |a| a,
                };
                const actual_field_align = switch (field_offset) {
                    0 => parent_align,
                    else => parent_align.minStrict(.fromLog2Units(@ctz(field_offset))),
                };
                const field_ptr_align: InternPool.Alignment = a: {
                    if (ptr_info.flags.alignment == .none and
                        aggregate_ty.explicitFieldAlignment(field_index, pool) == .none and
                        actual_field_align == extern_field_ty.abiAlignment(pool))
                    {
                        break :a .none;
                    }
                    break :a actual_field_align;
                };
                var field_ptr_info = ptr_info;
                field_ptr_info.child = extern_field_ty.index;
                field_ptr_info.flags.alignment = field_ptr_align;
                return .fromIndex(try pool.internPtrType(field_ptr_info));
            },
            // A packed field pointer needs the bit-offset info (`packed_offset`) the REPL's pointer flags omit;
            // the REPL instead reads packed fields through the backing integer, so this is a plain pointer.
            .@"packed" => {
                var field_ptr_info = ptr_info;
                field_ptr_info.child = aggregate_ty.fieldType(field_index, pool).index;
                return .fromIndex(try pool.internPtrType(field_ptr_info));
            },
        },
        .@"union" => switch (aggregate_ty.containerLayout(pool)) {
            .auto => field: {
                const union_obj = pool.unionFields(aggregate_ty.index);
                break :field .{
                    .fromIndex(union_obj.field_types[field_index]),
                    union_obj.field_aligns.getOrNone(field_index),
                };
            },
            .@"extern" => {
                const extern_field_ty = aggregate_ty.fieldType(field_index, pool);
                var field_ptr_info = ptr_info;
                field_ptr_info.child = extern_field_ty.index;
                if (field_ptr_info.flags.alignment == .none and
                    InternPool.Alignment.compareStrict(extern_field_ty.abiAlignment(pool), .neq, aggregate_ty.abiAlignment(pool)))
                {
                    field_ptr_info.flags.alignment = aggregate_ty.abiAlignment(pool);
                }
                return .fromIndex(try pool.internPtrType(field_ptr_info));
            },
            .@"packed" => {
                var field_ptr_info = ptr_info;
                field_ptr_info.child = aggregate_ty.fieldType(field_index, pool).index;
                return .fromIndex(try pool.internPtrType(field_ptr_info));
            },
        },
        else => unreachable,
    };
    const field_ptr_align: InternPool.Alignment = a: {
        if (aggregate_ty.zigTypeTag(pool) == .@"struct" and aggregate_ty.structFieldIsComptime(field_index, pool)) {
            break :a field_align;
        }
        const actual_field_align = switch (field_align) {
            .none => switch (pool.indexToKey(aggregate_ty.index)) {
                .tuple_type, .union_type => field_ty.abiAlignment(pool),
                .struct_type => field_ty.defaultStructFieldAlignment(.auto, pool),
                else => unreachable,
            },
            else => |a| a,
        };
        const actual_aggregate_align = switch (ptr_info.flags.alignment) {
            .none => aggregate_ty.abiAlignment(pool),
            else => |a| a,
        };
        if (actual_aggregate_align.compareStrict(.lt, actual_field_align)) {
            assert(ptr_info.flags.alignment != .none);
            break :a actual_aggregate_align;
        }
        if (field_align == .none and actual_field_align == field_ty.abiAlignment(pool)) {
            break :a .none;
        }
        break :a actual_field_align;
    };
    var field_ptr_info = ptr_info;
    field_ptr_info.flags.alignment = field_ptr_align;
    field_ptr_info.child = field_ty.index;
    return .fromIndex(try pool.internPtrType(field_ptr_info));
}

pub fn structFieldIsComptime(ty: Type, index: usize, pool: *const InternPool) bool {
    switch (pool.indexToKey(ty.index)) {
        .struct_type => {
            pool.assertLayoutResolved(ty.index);
            const bits = pool.loadStructType(ty.index).field_is_comptime_bits;
            if (bits.len == 0) return false;
            return bits[index / 32] >> @intCast(index % 32) & 1 != 0;
        },
        .tuple_type => |tuple| return tuple.values[index] != .none,
        else => unreachable,
    }
}

pub fn structFieldDefaultValue(ty: Type, index: usize, pool: *const InternPool) ?Value {
    switch (pool.indexToKey(ty.index)) {
        .struct_type => {
            const field_defaults = pool.loadStructType(ty.index).field_defaults;
            if (field_defaults.len == 0) return null;
            if (field_defaults[index] == .none) return null;
            return .fromIndex(field_defaults[index]);
        },
        .tuple_type => |tuple| {
            const val = tuple.values[index];
            if (val == .none) return null;
            return .fromIndex(val);
        },
        else => unreachable,
    }
}

/// The comptime-known value of struct/tuple field `index`, if the field is comptime or its type has
/// one possible value; null for a runtime field. Mirrors the compiler's Type.structFieldValueComptime.
pub fn structFieldValueComptime(ty: Type, sema: *Sema, index: usize) Sema.Error!?Value {
    const pool = sema.intern_pool;
    switch (pool.indexToKey(ty.index)) {
        .struct_type => {
            if (ty.structFieldIsComptime(index, pool)) {
                return .fromIndex(pool.loadStructType(ty.index).field_defaults[index]);
            } else {
                return try Type.fromIndex(pool.loadStructType(ty.index).field_types[index]).onePossibleValue(sema);
            }
        },
        .tuple_type => |tuple| {
            const val = tuple.values[index];
            if (val == .none) {
                return try Type.fromIndex(tuple.types[index]).onePossibleValue(sema);
            } else {
                return .fromIndex(val);
            }
        },
        else => unreachable,
    }
}

pub fn isAbiInt(ty: Type, pool: *const InternPool) bool {
    return switch (ty.zigTypeTag(pool)) {
        .int, .@"enum", .error_set => true,
        .@"struct", .@"union" => ty.containerLayout(pool) == .@"packed",
        else => false,
    };
}

pub fn defaultStructFieldAlignment(field_ty: Type, layout: std.lang.Type.ContainerLayout, pool: *const InternPool) InternPool.Alignment {
    const overalign_big_int = switch (layout) {
        .@"packed" => unreachable,
        .auto => target.ofmt == .c,
        .@"extern" => true,
    };
    const abi_align = field_ty.abiAlignment(pool);
    assert(abi_align != .none);
    if (overalign_big_int and
        ((field_ty.isAbiInt(pool) and field_ty.intInfo(pool).bits > 64) or
            (field_ty.index == .f80_type and target.cTypeBitSize(.longdouble) != 80)))
    {
        return abi_align.maxStrict(if (target.cpu.arch == .s390x) .@"8" else .@"16");
    }
    return abi_align;
}

pub const void_type: Type = .{ .index = .void_type };
pub const bool_type: Type = .{ .index = .bool_type };
pub const type_type: Type = .{ .index = .type_type };
pub const comptime_int_type: Type = .{ .index = .comptime_int_type };

const target: *const std.Target = &builtin.target;

pub fn abiAlignment(ty: Type, pool: *const InternPool) InternPool.Alignment {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => |int_type| {
            if (int_type.bits == 0) return .@"1";
            return .fromByteUnits(std.zig.target.intAlignment(target, int_type.bits));
        },
        .ptr_type, .anyframe_type => ptrAbiAlignment(),
        .array_type => |array_type| abiAlignment(fromIndex(array_type.child), pool),
        .vector_type => |vector_type| {
            if (vector_type.len == 0) return .@"1";
            if (vector_type.child == .bool_type) {
                if (vector_type.len > 256 and target.cpu.has(.x86, .avx512f)) return .@"64";
                if (vector_type.len > 128 and target.cpu.has(.x86, .avx)) return .@"32";
                if (vector_type.len > 64) return .@"16";
                const bytes = std.math.divCeil(u32, vector_type.len, 8) catch unreachable;
                return .fromByteUnits(std.math.ceilPowerOfTwoAssert(u32, bytes));
            }
            const elem_bytes: u32 = @intCast(abiSize(fromIndex(vector_type.child), pool));
            if (elem_bytes == 0) return .@"1";
            const bytes = elem_bytes * vector_type.len;
            if (bytes > 32 and target.cpu.has(.x86, .avx512f)) return .@"64";
            if (bytes > 16 and target.cpu.has(.x86, .avx)) return .@"32";
            return .@"16";
        },

        .opt_type => |child| abiAlignment(fromIndex(child), pool),
        .error_union_type => |eu| InternPool.Alignment.maxStrict(
            abiAlignment(fromIndex(eu.payload_type), pool),
            errorAbiAlignment(pool),
        ),

        .error_set_type => errorAbiAlignment(pool),

        .func_type => minFunctionAlignment(target),

        .simple_type => |t| switch (t) {
            .bool,
            .void,
            .noreturn,
            .anyopaque,
            .type,
            .comptime_int,
            .comptime_float,
            .null,
            .undefined,
            .enum_literal,
            => .@"1",

            .anyerror, .adhoc_inferred_error_set => errorAbiAlignment(pool),
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
            .f80 => if (target.cTypeBitSize(.longdouble) == 80) cTypeAlign(.longdouble) else abiAlignment(fromIndex(.u80_type), pool),
            .f128 => if (target.cTypeBitSize(.longdouble) == 128) cTypeAlign(.longdouble) else .@"16",

            .generic_poison => unreachable,
        },
        .tuple_type => |tuple| {
            var big_align: InternPool.Alignment = .@"1";
            for (tuple.types) |field_ty| {
                const field_align = abiAlignment(fromIndex(field_ty), pool);
                big_align = big_align.maxStrict(field_align);
            }
            return big_align;
        },
        .struct_type => {
            const struct_obj = pool.loadStructType(ty.index);
            switch (struct_obj.layout) {
                .@"packed" => return abiAlignment(fromIndex(struct_obj.packed_backing_int_type), pool),
                .auto, .@"extern" => return struct_obj.alignment,
            }
        },
        .union_type => {
            const union_obj = pool.unionFields(ty.index);
            switch (union_obj.layout) {
                .@"packed" => return abiAlignment(fromIndex(union_obj.packed_backing_int_type), pool),
                .auto, .@"extern" => return union_obj.alignment,
            }
        },
        .enum_type => abiAlignment(fromIndex(pool.loadEnumType(ty.index).int_tag_type), pool),
        .opaque_type => .@"1",

        .simple_value,
        .enum_literal,
        .int,
        .float,
        .undef,
        .ptr,
        .slice,
        .err,
        .error_union,
        .func,
        .opt,
        .aggregate,
        .enum_tag,
        .un,
        .bitpack,
        => unreachable,
    };
}

fn errorAbiAlignment(pool: *const InternPool) InternPool.Alignment {
    return .fromNonzeroByteUnits(std.zig.target.intAlignment(target, pool.errorSetBits()));
}

fn errorAbiSize(pool: *const InternPool) u64 {
    return std.zig.target.intByteSize(target, pool.errorSetBits());
}

fn minFunctionAlignment(t: *const std.Target) InternPool.Alignment {
    return switch (t.cpu.arch) {
        .riscv32,
        .riscv32be,
        .riscv64,
        .riscv64be,
        => if (t.cpu.hasAny(.riscv, &.{ .c, .zca })) .@"2" else .@"4",
        .thumb,
        .thumbeb,
        .csky,
        .m68k,
        .msp430,
        .sh,
        .sheb,
        .s390x,
        .xcore,
        => .@"2",
        .aarch64,
        .aarch64_be,
        .alpha,
        .arc,
        .arceb,
        .arm,
        .armeb,
        .hexagon,
        .hppa,
        .hppa64,
        .lanai,
        .loongarch32,
        .loongarch64,
        .microblaze,
        .microblazeel,
        .mips,
        .mipsel,
        .powerpc,
        .powerpcle,
        .powerpc64,
        .powerpc64le,
        .sparc,
        .sparc64,
        .xtensa,
        .xtensaeb,
        => .@"4",
        .bpfeb,
        .bpfel,
        .kvx,
        .mips64,
        .mips64el,
        => .@"8",
        .ve,
        => .@"16",
        else => .@"1",
    };
}

pub fn optionalReprIsPayload(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .opt_type => |child| child == .anyerror_type or switch (pool.indexToKey(child)) {
            .ptr_type => |pt| pt.flags.size != .c and !pt.flags.is_allowzero,
            .error_set_type => true,
            else => false,
        },
        .ptr_type => |pt| pt.flags.size == .c,
        else => false,
    };
}

pub fn abiSize(ty: Type, pool: *const InternPool) u64 {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => |int_type| std.zig.target.intByteSize(target, int_type.bits),
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            .slice => ptrByteSize() * 2,
            .one, .many, .c => ptrByteSize(),
        },
        .anyframe_type => ptrByteSize(),
        .array_type => |arr| arr.lenIncludingSentinel() * abiSize(fromIndex(arr.child), pool),
        .vector_type => |vec| {
            const elem_ty = fromIndex(vec.child);
            const bytes = switch (elem_ty.index) {
                .bool_type => std.math.divCeil(u64, vec.len, 8) catch unreachable,
                else => vec.len * abiSize(elem_ty, pool),
            };
            return abiAlignment(ty, pool).forward(bytes);
        },
        .opt_type => |child_ip| {
            const child = fromIndex(child_ip);
            switch (child.classify(pool)) {
                .no_possible_value => return 0,
                .fully_comptime => return 0,
                .one_possible_value, .partially_comptime, .runtime => {
                    if (optionalReprIsPayload(ty, pool)) return abiSize(child, pool);
                    return abiSize(child, pool) + abiAlignment(child, pool).toByteUnits().?;
                },
            }
        },
        .error_set_type => errorAbiSize(pool),
        .error_union_type => |error_union| {
            const payload_ty = fromIndex(error_union.payload_type);
            switch (payload_ty.classify(pool)) {
                .fully_comptime => return 0,
                .no_possible_value, .one_possible_value, .partially_comptime, .runtime => {},
            }
            const big_align = errorAbiAlignment(pool).maxStrict(payload_ty.abiAlignment(pool));
            return big_align.forward(errorAbiSize(pool) + payload_ty.abiSize(pool));
        },
        .func_type => 0,
        .simple_type => |t| switch (t) {
            .void, .noreturn, .type, .comptime_int, .comptime_float, .null, .undefined, .enum_literal => 0,
            .bool => 1,
            .anyerror, .adhoc_inferred_error_set => errorAbiSize(pool),
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
            .f80 => if (target.cTypeBitSize(.longdouble) == 80) target.cTypeByteSize(.longdouble) else abiSize(fromIndex(.u80_type), pool),
            .f128 => 16,
            .anyopaque => unreachable,
            .generic_poison => unreachable,
        },
        .tuple_type => |tuple| switch (ty.classify(pool)) {
            .no_possible_value => 0,
            else => ty.structFieldOffset(pool, tuple.types.len),
        },
        .struct_type => {
            const struct_obj = pool.loadStructType(ty.index);
            switch (struct_obj.layout) {
                .@"packed" => return abiSize(fromIndex(struct_obj.packed_backing_int_type), pool),
                .auto, .@"extern" => return struct_obj.size,
            }
        },
        .union_type => {
            const union_obj = pool.unionFields(ty.index);
            switch (union_obj.layout) {
                .@"packed" => return abiSize(fromIndex(union_obj.packed_backing_int_type), pool),
                .auto, .@"extern" => return union_obj.size,
            }
        },
        .enum_type => abiSize(fromIndex(pool.loadEnumType(ty.index).int_tag_type), pool),
        .opaque_type => unreachable,

        .simple_value,
        .enum_literal,
        .int,
        .float,
        .undef,
        .ptr,
        .slice,
        .err,
        .error_union,
        .func,
        .opt,
        .aggregate,
        .enum_tag,
        .un,
        .bitpack,
        => unreachable,
    };
}

pub fn bitSize(ty: Type, pool: *const InternPool) u64 {
    return switch (ty.zigTypeTag(pool)) {
        .void => 0,
        .bool => 1,
        .float => ty.floatBits(),
        .pointer, .optional => {
            assert(ty.isPtrAtRuntime(pool));
            return target.ptrBitWidth();
        },
        .array, .vector => ty.arrayLenIncludingSentinel(pool) * ty.childType(pool).bitSize(pool),
        else => ty.intInfo(pool).bits,
    };
}

pub fn intInfo(starting_ty: Type, pool: *const InternPool) std.lang.Type.Int {
    var ty = starting_ty;
    while (true) switch (ty.index) {
        .anyerror_type, .adhoc_inferred_error_set_type => return .{ .signedness = .unsigned, .bits = pool.errorSetBits() },
        .usize_type => return .{ .signedness = .unsigned, .bits = target.ptrBitWidth() },
        .isize_type => return .{ .signedness = .signed, .bits = target.ptrBitWidth() },
        .c_char_type => return .{ .signedness = target.cCharSignedness(), .bits = target.cTypeBitSize(.char) },
        .c_short_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.short) },
        .c_ushort_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.ushort) },
        .c_int_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.int) },
        .c_uint_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.uint) },
        .c_long_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.long) },
        .c_ulong_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.ulong) },
        .c_longlong_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.longlong) },
        .c_ulonglong_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.ulonglong) },
        else => switch (pool.indexToKey(ty.index)) {
            .int_type => |int_type| return int_type,
            .struct_type => {
                const struct_obj = pool.loadStructType(ty.index);
                assert(struct_obj.layout == .@"packed");
                ty = .fromIndex(struct_obj.packed_backing_int_type);
            },
            .union_type => {
                const union_obj = pool.unionFields(ty.index);
                assert(union_obj.layout == .@"packed");
                ty = .fromIndex(union_obj.packed_backing_int_type);
            },
            .enum_type => ty = .fromIndex(pool.loadEnumType(ty.index).int_tag_type),
            .vector_type => |vector_type| ty = .fromIndex(vector_type.child),

            .error_set_type => return .{ .signedness = .unsigned, .bits = pool.errorSetBits() },

            .tuple_type,
            .ptr_type,
            .anyframe_type,
            .array_type,
            .opt_type,
            .error_union_type,
            .func_type,
            .simple_type,
            .opaque_type,

            .undef,
            .simple_value,
            .enum_literal,
            .func,
            .int,
            .err,
            .error_union,
            .enum_tag,
            .float,
            .ptr,
            .slice,
            .opt,
            .aggregate,
            .un,
            .bitpack,
            => unreachable,
        },
    };
}

pub fn toUnsigned(ty: Type, pool: *InternPool) std.mem.Allocator.Error!Type {
    return switch (ty.index) {
        .usize_type, .isize_type => .fromIndex(.usize_type),
        .c_ushort_type, .c_short_type => .fromIndex(.c_ushort_type),
        .c_uint_type, .c_int_type => .fromIndex(.c_uint_type),
        .c_ulong_type, .c_long_type => .fromIndex(.c_ulong_type),
        .c_ulonglong_type, .c_longlong_type => .fromIndex(.c_ulonglong_type),
        else => switch (ty.zigTypeTag(pool)) {
            .int => .fromIndex(try pool.internIntType(.unsigned, ty.intInfo(pool).bits)),
            .vector => .fromIndex(try pool.internVectorType(.{
                .len = ty.vectorLen(pool),
                .child = (try ty.childType(pool).toUnsigned(pool)).index,
            })),
            else => unreachable,
        },
    };
}

pub fn zigTypeTag(ty: Type, pool: *const InternPool) std.lang.TypeId {
    return pool.zigTypeTag(ty.index);
}

pub fn childType(ty: Type, pool: *const InternPool) Type {
    return .fromIndex(pool.childType(ty.index));
}

pub fn smallestUnsignedBits(max: u64) u16 {
    return switch (max) {
        0 => 0,
        else => @as(u16, 1) + std.math.log2_int(u64, max),
    };
}

pub fn floatBits(ty: Type) u16 {
    return switch (ty.index) {
        .f16_type => 16,
        .f32_type => 32,
        .f64_type => 64,
        .f80_type => 80,
        .f128_type, .comptime_float_type => 128,
        .c_longdouble_type => target.cTypeBitSize(.longdouble),
        else => unreachable,
    };
}

pub fn isArrayOrVector(ty: Type, pool: *const InternPool) bool {
    return switch (ty.zigTypeTag(pool)) {
        .array, .vector => true,
        else => false,
    };
}

pub fn floatSignificandBits(ty: Type) u16 {
    return switch (ty.floatBits()) {
        16 => 11,
        32 => 24,
        64 => 53,
        80 => 64,
        128 => 113,
        else => unreachable,
    };
}

pub fn unionTagTypeHypothetical(ty: Type, pool: *const InternPool) Type {
    pool.assertLayoutResolved(ty.index);
    return .fromIndex(pool.unionFields(ty.index).enum_tag_type);
}

pub fn isPtrAtRuntime(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            .slice => false,
            .one, .many, .c => true,
        },
        .opt_type => |child| switch (pool.indexToKey(child)) {
            .ptr_type => |p| switch (p.flags.size) {
                .slice, .c => false,
                .many, .one => !p.flags.is_allowzero,
            },
            else => false,
        },
        else => false,
    };
}

pub fn isSlice(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.size == .slice,
        else => false,
    };
}

pub fn isSinglePointer(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |info| info.flags.size == .one,
        else => false,
    };
}

pub fn isConstPtr(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.is_const,
        else => false,
    };
}

pub fn isVolatilePtr(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.is_volatile,
        else => false,
    };
}

pub fn isPtrLikeOptional(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.size == .c,
        .opt_type => |child| switch (pool.indexToKey(child)) {
            .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
                .slice, .c => false,
                .many, .one => !ptr_type.flags.is_allowzero,
            },
            else => false,
        },
        else => false,
    };
}

pub fn ptrAllowsZero(ty: Type, pool: *const InternPool) bool {
    return ty.isPtrLikeOptional(pool) or ty.ptrInfo(pool).flags.is_allowzero;
}

pub fn optionalChild(ty: Type, pool: *const InternPool) Type {
    return switch (pool.indexToKey(ty.index)) {
        .opt_type => |child| .fromIndex(child),
        .ptr_type => |ptr_type| blk: {
            assert(ptr_type.flags.size == .c);
            break :blk ty;
        },
        else => unreachable,
    };
}

pub const ArrayInfo = struct { len: u64, sentinel: ?InternPool.Index, elem_type: Type };
pub fn arrayInfo(ty: Type, pool: *const InternPool) ArrayInfo {
    const at = pool.indexToKey(ty.index).array_type;
    return .{
        .len = at.len,
        .sentinel = if (at.sentinel == .none) null else at.sentinel,
        .elem_type = .fromIndex(at.child),
    };
}

pub fn vectorLen(ty: Type, pool: *const InternPool) u32 {
    return switch (pool.indexToKey(ty.index)) {
        .vector_type => |vector_type| vector_type.len,
        .tuple_type => |tuple| @intCast(tuple.types.len),
        else => unreachable,
    };
}

pub fn arrayLen(ty: Type, pool: *const InternPool) u64 {
    return pool.aggregateTypeLen(ty.index);
}

pub fn arrayLenIncludingSentinel(ty: Type, pool: *const InternPool) u64 {
    return pool.aggregateTypeLenIncludingSentinel(ty.index);
}

pub fn sentinel(ty: Type, pool: *const InternPool) ?Value {
    return switch (pool.indexToKey(ty.index)) {
        .vector_type, .struct_type, .tuple_type => null,
        .array_type => |t| if (t.sentinel != .none) .fromIndex(t.sentinel) else null,
        .ptr_type => |t| if (t.sentinel != .none) .fromIndex(t.sentinel) else null,
        else => unreachable,
    };
}

pub fn scalarType(ty: Type, pool: *const InternPool) Type {
    return switch (ty.zigTypeTag(pool)) {
        .vector => ty.childType(pool),
        else => ty,
    };
}

pub fn errorUnionPayload(ty: Type, pool: *const InternPool) Type {
    return .fromIndex(pool.indexToKey(ty.index).error_union_type.payload_type);
}

pub fn errorUnionSet(ty: Type, pool: *const InternPool) Type {
    return .fromIndex(pool.indexToKey(ty.index).error_union_type.error_set_type);
}

pub fn errorSetIsEmpty(ty: Type, pool: *const InternPool) bool {
    return switch (ty.index) {
        .anyerror_type, .adhoc_inferred_error_set_type => false,
        else => switch (pool.indexToKey(ty.index)) {
            .error_set_type => |error_set_type| error_set_type.names.len == 0,
            else => unreachable,
        },
    };
}

pub fn isAnyError(ty: Type, pool: *const InternPool) bool {
    _ = pool;
    return switch (ty.index) {
        .anyerror_type => true,
        .adhoc_inferred_error_set_type => false,
        else => false,
    };
}

pub fn errorSetNames(ty: Type, pool: *const InternPool) []const InternPool.NullTerminatedString {
    return switch (pool.indexToKey(ty.index)) {
        .error_set_type => |x| x.names,
        else => unreachable,
    };
}

pub fn errorSetHasField(ty: Type, name: InternPool.NullTerminatedString, pool: *const InternPool) bool {
    return switch (ty.index) {
        .anyerror_type => true,
        else => switch (pool.indexToKey(ty.index)) {
            .error_set_type => |error_set_type| error_set_type.nameIndex(pool, name) != null,
            else => unreachable,
        },
    };
}

pub fn optEuBaseType(ty: Type, pool: *const InternPool) Type {
    var cur = ty;
    while (true) switch (cur.zigTypeTag(pool)) {
        .optional => cur = cur.optionalChild(pool),
        .error_union => cur = cur.errorUnionPayload(pool),
        else => return cur,
    };
}

pub fn isTuple(ty: Type, pool: *const InternPool) bool {
    return pool.indexToKey(ty.index) == .tuple_type;
}

pub fn indexableElem(ty: Type, pool: *const InternPool) Type {
    return switch (pool.indexToKey(ty.index)) {
        inline .array_type, .vector_type => |arr| .fromIndex(arr.child),
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            .many, .slice, .c => .fromIndex(ptr_type.child),
            .one => switch (pool.indexToKey(ptr_type.child)) {
                inline .array_type, .vector_type => |arr| .fromIndex(arr.child),
                else => unreachable,
            },
        },
        else => unreachable,
    };
}

pub fn ptrInfo(ty: Type, pool: *const InternPool) InternPool.Key.PtrType {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |p| p,
        .opt_type => |child| pool.indexToKey(child).ptr_type,
        else => unreachable,
    };
}

pub fn ptrAlignment(ptr_ty: Type, pool: *const InternPool) InternPool.Alignment {
    const ptr_key = ptr_ty.ptrInfo(pool);
    if (ptr_key.flags.alignment != .none) return ptr_key.flags.alignment;
    return Type.fromIndex(ptr_key.child).abiAlignment(pool);
}

pub fn nullablePtrElem(ty: Type, pool: *const InternPool) Type {
    switch (ty.zigTypeTag(pool)) {
        .pointer => return ty.childType(pool),
        .optional => {
            const ptr_ty = ty.childType(pool);
            const ptr_info = pool.indexToKey(ptr_ty.index).ptr_type;
            assert(ptr_info.flags.size != .c);
            assert(!ptr_info.flags.is_allowzero);
            return .fromIndex(ptr_info.child);
        },
        else => unreachable,
    }
}

pub fn comptimeOnly(ty: Type, pool: *const InternPool) bool {
    if (ty.index == .generic_poison_type) return false;
    if (ty.zigTypeTag(pool) == .error_union and ty.errorUnionPayload(pool).index == .generic_poison_type) return false;
    return switch (ty.classify(pool)) {
        .no_possible_value, .one_possible_value, .runtime => false,
        .partially_comptime, .fully_comptime => true,
    };
}

pub fn hasBitRepresentation(ty: Type, pool: *const InternPool) bool {
    return switch (ty.zigTypeTag(pool)) {
        .@"fn",
        .noreturn,
        .undefined,
        .null,
        .@"opaque",
        .spirv,
        .type,
        .enum_literal,
        .comptime_float,
        .comptime_int,
        .error_set,
        .error_union,
        .frame,
        .@"anyframe",
        => false,

        .void,
        .bool,
        .int,
        .float,
        => true,

        .@"enum" => pool.loadEnumType(ty.index).int_tag_mode == .explicit,
        .pointer, .optional => ty.isPtrAtRuntime(pool),
        .@"struct", .@"union" => ty.containerLayout(pool) == .@"packed",

        .array, .vector => ty.childType(pool).hasBitRepresentation(pool),
    };
}

fn cTypeAlign(c: std.Target.CType) InternPool.Alignment {
    return .fromByteUnits(target.cTypeAlignment(c));
}

fn ptrAbiAlignment() InternPool.Alignment {
    if (target.cpu.arch == .ez80) return .@"1";
    return .fromNonzeroByteUnits(ptrByteSize());
}
fn ptrByteSize() u64 {
    return @divExact(target.ptrBitWidth(), 8);
}

pub const PrintError = std.Io.Writer.Error || std.mem.Allocator.Error;

pub const Formatter = struct {
    ty: Type,
    pool: *const InternPool,
    pub fn format(self: Formatter, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        self.ty.print(self.pool, writer) catch |err| switch (err) {
            error.WriteFailed => return error.WriteFailed,
            else => try writer.writeAll("<type>"),
        };
    }
};

pub fn fmt(ty: Type, pool: *const InternPool) Formatter {
    return .{ .ty = ty, .pool = pool };
}

pub fn print(ty: Type, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    assert(ty.index != .none);
    switch (pool.indexToKey(ty.index)) {
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
        .struct_type, .enum_type, .union_type, .opaque_type => try writer.writeAll(pool.stringSlice(pool.typeName(ty.index))),
        .undef => try writer.writeAll("@as(type, undefined)"),
        else => |other| {
            assert(other.isType());
            try writer.writeAll("<type>");
        },
    }
}

pub fn isSelfComparable(ty: Type, pool: *const InternPool, is_equality_cmp: bool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => true,
        .simple_type => |s| switch (s) {
            .usize,
            .isize,
            .c_char,
            .c_short,
            .c_ushort,
            .c_int,
            .c_uint,
            .c_long,
            .c_ulong,
            .c_longlong,
            .c_ulonglong,
            .comptime_int,
            .f16,
            .f32,
            .f64,
            .f80,
            .f128,
            .c_longdouble,
            .comptime_float,
            => true,
            .bool, .type, .void, .anyerror, .adhoc_inferred_error_set, .enum_literal, .anyopaque => is_equality_cmp,
            .noreturn, .undefined, .null, .generic_poison => false,
        },
        .vector_type => |vt| fromIndex(vt.child).isSelfComparable(pool, is_equality_cmp),
        .enum_type, .error_set_type, .func_type, .anyframe_type, .opaque_type => is_equality_cmp,
        .error_union_type, .array_type => false,
        .struct_type, .union_type, .tuple_type => is_equality_cmp and ty.containerLayout(pool) == .@"packed",
        .ptr_type => |pt| pt.flags.size != .slice and (is_equality_cmp or pt.flags.size == .c),
        .opt_type => |child| is_equality_cmp and fromIndex(child).isSelfComparable(pool, is_equality_cmp),
        else => false,
    };
}

fn printPtr(pt: InternPool.Key.PtrType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    assert(pt.child != .none);
    if (pt.sentinel != .none) {
        try writer.writeAll(switch (pt.flags.size) {
            .many => "[*:",
            .slice => "[:",
            .one, .c => unreachable,
        });
        try Value.print(.fromIndex(pt.sentinel), pool, writer);
        try writer.writeAll("]");
    } else try writer.writeAll(switch (pt.flags.size) {
        .one => "*",
        .many => "[*]",
        .slice => "[]",
        .c => "[*c]",
    });
    if (pt.flags.is_allowzero and pt.flags.size != .c) try writer.writeAll("allowzero ");
    if (pt.flags.alignment.toByteUnits()) |bytes| try writer.print("align({d}) ", .{bytes});
    if (pt.flags.is_const) try writer.writeAll("const ");
    if (pt.flags.is_volatile) try writer.writeAll("volatile ");
    try print(fromIndex(pt.child), pool, writer);
}

fn printArray(at: InternPool.Key.ArrayType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try writer.print("[{d}", .{at.len});
    if (at.sentinel != .none) {
        try writer.writeAll(":");
        try Value.print(.fromIndex(at.sentinel), pool, writer);
    }
    try writer.writeAll("]");
    try print(fromIndex(at.child), pool, writer);
}

fn printTuple(tt: InternPool.Key.TupleType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    if (tt.types.len == 0) {
        try writer.writeAll("@TypeOf(.{})");
        return;
    }
    try writer.writeAll("struct { ");
    for (tt.types, tt.values, 0..) |field_ty, val, i| {
        if (i != 0) try writer.writeAll(", ");
        if (val != .none) try writer.writeAll("comptime ");
        try print(fromIndex(field_ty), pool, writer);
        if (val != .none) {
            try writer.writeAll(" = ");
            try Value.print(.fromIndex(val), pool, writer);
        }
    }
    try writer.writeAll(" }");
}

fn printVector(vt: InternPool.Key.VectorType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try writer.print("@Vector({d}, ", .{vt.len});
    try print(fromIndex(vt.child), pool, writer);
    try writer.writeAll(")");
}

fn printFunc(ft: InternPool.Key.FuncType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    if (ft.is_noinline) try writer.writeAll("noinline ");
    try writer.writeAll("fn (");
    for (ft.param_types, 0..) |p, i| {
        if (i != 0) try writer.writeAll(", ");
        if (std.math.cast(u5, i)) |idx| {
            if (ft.paramIsComptime(idx)) try writer.writeAll("comptime ");
            if (ft.paramIsNoalias(idx)) try writer.writeAll("noalias ");
        }
        if (p == .generic_poison_type) try writer.writeAll("anytype") else try print(fromIndex(p), pool, writer);
    }
    if (ft.is_var_args) {
        try writer.writeAll(if (ft.param_types.len > 0) ", ..." else "...");
    }
    try writer.writeAll(") ");
    const cc_tag: std.lang.CallingConvention.Tag = ft.cc;
    if (cc_tag != .auto) {
        const name = @tagName(cc_tag);
        if (std.zig.Token.getKeyword(name) != null) {
            try writer.print("callconv(.@\"{s}\") ", .{name});
        } else {
            try writer.print("callconv(.{s}) ", .{name});
        }
    }
    if (ft.return_type == .generic_poison_type) try writer.writeAll("anytype") else try print(fromIndex(ft.return_type), pool, writer);
}

fn printErrorUnion(eu: InternPool.Key.ErrorUnionType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try print(fromIndex(eu.error_set_type), pool, writer);
    try writer.writeAll("!");
    if (eu.payload_type == .generic_poison_type) try writer.writeAll("anytype") else try print(fromIndex(eu.payload_type), pool, writer);
}

fn printErrorSet(es: InternPool.Key.ErrorSetType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
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

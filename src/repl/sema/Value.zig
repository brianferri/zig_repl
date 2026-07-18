const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Type = @import("Type.zig");

const Value = @This();

index: InternPool.Index,
is_comptime: bool = true,

pub fn fromIndex(index: InternPool.Index) Value {
    assert(index != .none);
    return .{ .index = index };
}

pub fn toIndex(val: Value) InternPool.Index {
    return val.index;
}

pub fn getOffsetPtr(ptr_val: Value, byte_off: u64, new_ty: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (ptr_val.isUndef(pool)) return ptr_val;
    var ptr = pool.indexToKey(ptr_val.index).ptr;
    ptr.ty = new_ty.index;
    ptr.byte_offset += byte_off;
    return .fromIndex(try pool.internPtr(ptr));
}

fn canonicalizeBasePtr(base_ptr: Value, want_size: InternPool.Key.PtrType.Size, want_child: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const ptr_info = base_ptr.typeOf(pool).ptrInfo(pool);
    if (ptr_info.flags.size == want_size and
        ptr_info.child == want_child.index and
        !ptr_info.flags.is_const and
        !ptr_info.flags.is_volatile and
        !ptr_info.flags.is_allowzero and
        ptr_info.sentinel == .none and
        ptr_info.flags.alignment == .none)
    {
        return base_ptr;
    }
    const new_ty = try pool.internPtrType(.{
        .child = want_child.index,
        .sentinel = .none,
        .flags = .{
            .size = want_size,
            .alignment = .none,
            .is_const = false,
            .is_volatile = false,
            .is_allowzero = false,
            .address_space = ptr_info.flags.address_space,
        },
    });
    return base_ptr.getOffsetPtr(0, .fromIndex(new_ty), pool);
}

pub fn ptrField(parent_ptr: Value, field_idx: u32, pool: *InternPool) std.mem.Allocator.Error!Value {
    const parent_ptr_ty = parent_ptr.typeOf(pool);
    const aggregate_ty = parent_ptr_ty.childType(pool);
    pool.assertLayoutResolved(aggregate_ty.index);

    const parent_ptr_info = parent_ptr_ty.ptrInfo(pool);
    assert(parent_ptr_info.flags.size == .one or parent_ptr_info.flags.size == .c);

    const field_ptr_ty = try parent_ptr_ty.fieldPtrType(field_idx, pool);

    switch (aggregate_ty.zigTypeTag(pool)) {
        .pointer => assert(aggregate_ty.isSlice(pool)),
        // A packed field has no `packed_offset` in the REPL's pointer flags; it is read through a `.field`
        // pointer over the backing integer (the bitpack load/store path), so it uses the `.auto` form below.
        .@"struct" => switch (aggregate_ty.containerLayout(pool)) {
            .auto, .@"packed" => {},
            .@"extern" => return parent_ptr.getOffsetPtr(aggregate_ty.structFieldOffset(pool, field_idx), field_ptr_ty, pool),
        },
        .@"union" => switch (aggregate_ty.containerLayout(pool)) {
            .auto, .@"packed" => {},
            .@"extern" => return parent_ptr.getOffsetPtr(0, field_ptr_ty, pool),
        },
        else => unreachable,
    }

    // The aggregate has no well-defined layout, so use the `.field` comptime pointer representation.
    if (parent_ptr.isUndef(pool)) return .fromIndex(try pool.get(.{ .undef = field_ptr_ty.index }));

    const base_ptr = try parent_ptr.canonicalizeBasePtr(.one, aggregate_ty, pool);
    return .fromIndex(try pool.internPtr(.{
        .ty = field_ptr_ty.index,
        .base_addr = .{ .field = .{ .base = base_ptr.index, .index = field_idx } },
        .byte_offset = 0,
    }));
}

pub fn writeToPackedMemory(val: Value, pool: *const InternPool, buffer: []u8, bit_offset: usize) void {
    const endian = builtin.target.cpu.arch.endian();
    const ty = val.typeOf(pool);
    if (val.isUndef(pool)) {
        const bit_size: usize = @intCast(ty.bitSize(pool));
        if (bit_size != 0) std.mem.writeVarPackedInt(buffer, bit_offset, bit_size, @as(u1, 0), endian);
        return;
    }
    switch (ty.zigTypeTag(pool)) {
        .void => {},
        .bool => {
            const byte_index = bit_offset / 8;
            if (pool.indexToKey(val.index).simple_value == .true) {
                buffer[byte_index] |= (@as(u8, 1) << @as(u3, @intCast(bit_offset % 8)));
            } else {
                buffer[byte_index] &= ~(@as(u8, 1) << @as(u3, @intCast(bit_offset % 8)));
            }
        },
        .@"enum" => {
            const int_val: Value = .fromIndex(pool.indexToKey(val.index).enum_tag.int);
            int_val.writeToPackedMemory(pool, buffer, bit_offset);
        },
        .int => {
            const bits = ty.intInfo(pool).bits;
            if (bits == 0 or buffer.len == 0) return;
            switch (pool.indexToKey(val.index).int.storage) {
                inline .u64, .i64 => |int| std.mem.writeVarPackedInt(buffer, bit_offset, bits, int, endian),
                .big_int => |bigint| bigint.writePackedTwosComplement(buffer, bit_offset, bits, endian),
            }
        },
        .float => switch (ty.floatBits()) {
            16 => std.mem.writePackedInt(u16, buffer, bit_offset, @bitCast(val.toFloat(f16, pool)), endian),
            32 => std.mem.writePackedInt(u32, buffer, bit_offset, @bitCast(val.toFloat(f32, pool)), endian),
            64 => std.mem.writePackedInt(u64, buffer, bit_offset, @bitCast(val.toFloat(f64, pool)), endian),
            80 => std.mem.writePackedInt(u80, buffer, bit_offset, @bitCast(val.toFloat(f80, pool)), endian),
            128 => std.mem.writePackedInt(u128, buffer, bit_offset, @bitCast(val.toFloat(f128, pool)), endian),
            else => unreachable,
        },
        .@"struct", .@"union" => {
            const int_val: Value = .fromIndex(pool.indexToKey(val.index).bitpack.backing_int_val);
            int_val.writeToPackedMemory(pool, buffer, bit_offset);
        },
        .array, .vector => {
            const elem_bits: usize = @intCast(ty.childType(pool).bitSize(pool));
            const len: usize = @intCast(ty.arrayLen(pool));
            var elem_bit_off: usize = bit_offset;
            switch (pool.indexToKey(val.index).aggregate.storage) {
                .repeated_elem => |elem_val_ip| {
                    const elem_val: Value = .fromIndex(elem_val_ip);
                    for (0..len) |_| {
                        elem_val.writeToPackedMemory(pool, buffer, elem_bit_off);
                        elem_bit_off += elem_bits;
                    }
                },
                .elems => |elems| for (elems[0..len]) |elem_val_ip| {
                    const elem_val: Value = .fromIndex(elem_val_ip);
                    elem_val.writeToPackedMemory(pool, buffer, elem_bit_off);
                    elem_bit_off += elem_bits;
                },
            }
            if (ty.sentinel(pool)) |sentinel_val| {
                sentinel_val.writeToPackedMemory(pool, buffer, elem_bit_off);
            }
        },
        else => unreachable,
    }
}

pub fn readFromPackedMemory(ty: Type, pool: *InternPool, buffer: []const u8, bit_offset: usize) std.mem.Allocator.Error!Value {
    const endian = builtin.target.cpu.arch.endian();
    switch (ty.zigTypeTag(pool)) {
        .void => return void_value,
        .bool => {
            const byte = buffer[bit_offset / 8];
            const bit_set = ((byte >> @as(u3, @intCast(bit_offset % 8))) & 1) != 0;
            return .fromIndex(try pool.get(.{ .simple_value = if (bit_set) .true else .false }));
        },
        .int => {
            if (buffer.len == 0 or ty.index == .u0_type) return .fromIndex(try pool.internInt(.{ .ty = ty.index, .storage = .{ .u64 = 0 } }));
            const int_info = ty.intInfo(pool);
            const bits = int_info.bits;
            if (bits <= 64) return switch (int_info.signedness) {
                .unsigned => .fromIndex(try pool.internInt(.{ .ty = ty.index, .storage = .{ .u64 = std.mem.readVarPackedInt(u64, buffer, bit_offset, bits, endian, .unsigned) } })),
                .signed => .fromIndex(try pool.internInt(.{ .ty = ty.index, .storage = .{ .i64 = std.mem.readVarPackedInt(i64, buffer, bit_offset, bits, endian, .signed) } })),
            };
            const abi_size: usize = @intCast(ty.abiSize(pool));
            const limb_count = (abi_size + @sizeOf(std.math.big.Limb) - 1) / @sizeOf(std.math.big.Limb);
            const limbs = try pool.gpa.alloc(std.math.big.Limb, limb_count);
            defer pool.gpa.free(limbs);
            var bigint = std.math.big.int.Mutable.init(limbs, 0);
            bigint.readPackedTwosComplement(buffer, bit_offset, bits, endian, int_info.signedness);
            return .fromIndex(try pool.internIntValue(ty.index, bigint.toConst()));
        },
        .float => return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = switch (ty.floatBits()) {
            16 => .{ .f16 = @bitCast(std.mem.readPackedInt(u16, buffer, bit_offset, endian)) },
            32 => .{ .f32 = @bitCast(std.mem.readPackedInt(u32, buffer, bit_offset, endian)) },
            64 => .{ .f64 = @bitCast(std.mem.readPackedInt(u64, buffer, bit_offset, endian)) },
            80 => .{ .f80 = @bitCast(std.mem.readPackedInt(u80, buffer, bit_offset, endian)) },
            128 => .{ .f128 = @bitCast(std.mem.readPackedInt(u128, buffer, bit_offset, endian)) },
            else => unreachable,
        } })),
        .@"enum" => {
            const int_ty = pool.loadEnumType(ty.index).int_tag_type;
            const int_val = try readFromPackedMemory(.fromIndex(int_ty), pool, buffer, bit_offset);
            return .fromIndex(try pool.internEnumTag(.{ .ty = ty.index, .int = int_val.index }));
        },
        .@"struct", .@"union" => {
            const int_val = try readFromPackedMemory(ty.bitpackBackingInt(pool), pool, buffer, bit_offset);
            return .fromIndex(try pool.internBitpack(.{ .ty = ty.index, .backing_int_val = int_val.index }));
        },
        .array, .vector => {
            const elem_ty = ty.childType(pool);
            const elem_bits: usize = @intCast(elem_ty.bitSize(pool));
            const elems_buf = try pool.gpa.alloc(InternPool.Index, @intCast(ty.arrayLen(pool)));
            defer pool.gpa.free(elems_buf);
            var elem_bit_off: usize = bit_offset;
            for (elems_buf) |*elem| {
                const elem_val = try readFromPackedMemory(elem_ty, pool, buffer, elem_bit_off);
                elem.* = elem_val.index;
                elem_bit_off += elem_bits;
            }
            return .fromIndex(try pool.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = elems_buf } }));
        },
        else => unreachable,
    }
}

pub fn print(val: Value, pool: *const InternPool, writer: *std.Io.Writer) std.Io.Writer.Error!void {
    switch (pool.indexToKey(val.index)) {
        .int => |iv| {
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            try writer.print("{f}", .{iv.storage.toBigInt(&space)});
        },
        .enum_tag => |et| {
            const f = pool.loadEnumType(et.ty);
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const tag = pool.indexToKey(et.int).int.storage.toBigInt(&space).toInt(i64) catch {
                return print(.fromIndex(et.int), pool, writer);
            };
            if (f.field_values.len == 0) {
                if (tag >= 0 and tag < f.field_names.len) {
                    return writer.print(".{s}", .{pool.stringSlice(f.field_names[@intCast(tag)])});
                }
            } else for (f.field_values, 0..) |v, pos| {
                var value_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                const field_val = pool.indexToKey(v).int.storage.toBigInt(&value_space).toInt(i64) catch continue;
                if (field_val == tag) return writer.print(".{s}", .{pool.stringSlice(f.field_names[pos])});
            }
            return print(.fromIndex(et.int), pool, writer);
        },
        .simple_value => |sv| try writer.writeAll(switch (sv) {
            .void => "void",
            .null => "null",
            .true => "true",
            .false => "false",
            .@"unreachable" => "unreachable",
        }),
        .err => |e| try writer.print("error.{s}", .{pool.stringSlice(e.name)}),
        else => try writer.writeAll("?"),
    }
}

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
        .slice => |s| .{ .index = s.ty },
        .err => |e| .{ .index = e.ty },
        .error_union => |eu| .{ .index = eu.ty },
        .func => |f| .{ .index = f.ty },
        .opt => |o| .{ .index = o.ty },
        .aggregate => |agg| .{ .index = agg.ty },
        .enum_tag => |et| .{ .index = et.ty },
        .enum_literal => .{ .index = .enum_literal_type },
        .un => |uv| .{ .index = uv.ty },
        .bitpack => |bp| .{ .index = bp.ty },
        else => blk: {
            assert(key.isType());
            break :blk .type_type;
        },
    };
}

pub fn toFloat(val: Value, comptime T: type, pool: *const InternPool) T {
    return switch (pool.indexToKey(val.index)) {
        .int => |int| switch (int.storage) {
            .big_int => |big_int| big_int.toFloat(T, .nearest_even)[0],
            inline .u64, .i64 => |x| {
                if (T == f80) {
                    @panic("TODO we can't lower this properly on non-x86 llvm backend yet");
                }
                return @floatFromInt(x);
            },
        },
        .float => |float| switch (float.storage) {
            inline else => |x| @floatCast(x),
        },
        else => unreachable,
    };
}

pub fn elemValue(val: Value, pool: *InternPool, index: usize) std.mem.Allocator.Error!Value {
    switch (pool.indexToKey(val.index)) {
        .undef => |ty| return .fromIndex(try pool.get(.{ .undef = Type.fromIndex(ty).childType(pool).index })),
        .aggregate => |aggregate| return .fromIndex(InternPool.aggregateElementAt(aggregate, index)),
        else => unreachable,
    }
}

pub fn mulAdd(
    float_type: Type,
    mulend1: Value,
    mulend2: Value,
    addend: Value,
    arena: std.mem.Allocator,
    pool: *InternPool,
) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const mulend1_elem = try mulend1.elemValue(pool, i);
            const mulend2_elem = try mulend2.elemValue(pool, i);
            const addend_elem = try addend.elemValue(pool, i);
            scalar.* = (try mulAddScalar(scalar_ty, mulend1_elem, mulend2_elem, addend_elem, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return mulAddScalar(float_type, mulend1, mulend2, addend, pool);
}

pub fn mulAddScalar(
    float_type: Type,
    mulend1: Value,
    mulend2: Value,
    addend: Value,
    pool: *InternPool,
) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @mulAdd(f16, mulend1.toFloat(f16, pool), mulend2.toFloat(f16, pool), addend.toFloat(f16, pool)) },
        32 => .{ .f32 = @mulAdd(f32, mulend1.toFloat(f32, pool), mulend2.toFloat(f32, pool), addend.toFloat(f32, pool)) },
        64 => .{ .f64 = @mulAdd(f64, mulend1.toFloat(f64, pool), mulend2.toFloat(f64, pool), addend.toFloat(f64, pool)) },
        80 => .{ .f80 = @mulAdd(f80, mulend1.toFloat(f80, pool), mulend2.toFloat(f80, pool), addend.toFloat(f80, pool)) },
        128 => .{ .f128 = @mulAdd(f128, mulend1.toFloat(f128, pool), mulend2.toFloat(f128, pool), addend.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn abs(val: Value, ty: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (ty.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, ty.vectorLen(pool));
        const scalar_ty = ty.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try absScalar(elem_val, scalar_ty, pool, arena)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = result_data } }));
    }
    return absScalar(val, ty, pool, arena);
}

pub fn absScalar(val: Value, ty: Type, pool: *InternPool, arena: std.mem.Allocator) std.mem.Allocator.Error!Value {
    switch (ty.zigTypeTag(pool)) {
        .int => {
            var buffer: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            var operand_bigint = try pool.indexToKey(val.index).int.storage.toBigInt(&buffer).toManaged(arena);
            operand_bigint.abs();
            return .fromIndex(try pool.internIntValue((try ty.toUnsigned(pool)).index, operand_bigint.toConst()));
        },
        .comptime_int => {
            var buffer: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            var operand_bigint = try pool.indexToKey(val.index).int.storage.toBigInt(&buffer).toManaged(arena);
            operand_bigint.abs();
            return .fromIndex(try pool.internComptimeInt(operand_bigint.toConst()));
        },
        .comptime_float, .float => {
            const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
                16 => .{ .f16 = @abs(val.toFloat(f16, pool)) },
                32 => .{ .f32 = @abs(val.toFloat(f32, pool)) },
                64 => .{ .f64 = @abs(val.toFloat(f64, pool)) },
                80 => .{ .f80 = @abs(val.toFloat(f80, pool)) },
                128 => .{ .f128 = @abs(val.toFloat(f128, pool)) },
                else => unreachable,
            };
            return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
        },
        else => unreachable,
    }
}

pub fn sqrt(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try sqrtScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return sqrtScalar(val, float_type, pool);
}

pub fn sqrtScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @sqrt(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @sqrt(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @sqrt(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @sqrt(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @sqrt(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn sin(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try sinScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return sinScalar(val, float_type, pool);
}

pub fn sinScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @sin(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @sin(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @sin(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @sin(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @sin(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn cos(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try cosScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return cosScalar(val, float_type, pool);
}

pub fn cosScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @cos(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @cos(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @cos(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @cos(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @cos(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn tan(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try tanScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return tanScalar(val, float_type, pool);
}

pub fn tanScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @tan(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @tan(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @tan(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @tan(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @tan(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn exp(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try expScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return expScalar(val, float_type, pool);
}

pub fn expScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @exp(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @exp(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @exp(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @exp(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @exp(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn exp2(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try exp2Scalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return exp2Scalar(val, float_type, pool);
}

pub fn exp2Scalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @exp2(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @exp2(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @exp2(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @exp2(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @exp2(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn log(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try logScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return logScalar(val, float_type, pool);
}

pub fn logScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @log(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @log(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @log(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @log(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @log(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn log2(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try log2Scalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return log2Scalar(val, float_type, pool);
}

pub fn log2Scalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @log2(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @log2(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @log2(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @log2(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @log2(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn log10(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try log10Scalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return log10Scalar(val, float_type, pool);
}

pub fn log10Scalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @log10(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @log10(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @log10(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @log10(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @log10(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn floor(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try floorScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return floorScalar(val, float_type, pool);
}

pub fn floorScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @floor(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @floor(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @floor(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @floor(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @floor(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn ceil(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try ceilScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return ceilScalar(val, float_type, pool);
}

pub fn ceilScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @ceil(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @ceil(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @ceil(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @ceil(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @ceil(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn round(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try roundScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return roundScalar(val, float_type, pool);
}

pub fn roundScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @round(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @round(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @round(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @round(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @round(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn trunc(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try truncScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return truncScalar(val, float_type, pool);
}

pub fn truncScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @trunc(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @trunc(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @trunc(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @trunc(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @trunc(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn toBigInt(val: Value, space: *InternPool.Key.Int.Storage.BigIntSpace, pool: *const InternPool) std.math.big.int.Const {
    return pool.indexToKey(val.index).int.storage.toBigInt(space);
}

pub fn clz(val: Value, ty: Type, pool: *const InternPool) u64 {
    var bigint_buf: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const bigint = val.toBigInt(&bigint_buf, pool);
    return bigint.clz(ty.intInfo(pool).bits);
}

pub fn ctz(val: Value, ty: Type, pool: *const InternPool) u64 {
    var bigint_buf: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const bigint = val.toBigInt(&bigint_buf, pool);
    return bigint.ctz(ty.intInfo(pool).bits);
}

pub fn popCount(val: Value, ty: Type, pool: *const InternPool) u64 {
    var bigint_buf: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const bigint = val.toBigInt(&bigint_buf, pool);
    return @intCast(bigint.popCount(ty.intInfo(pool).bits));
}

pub const undef: Value = .{ .index = .undef };

pub fn isUndef(val: Value, pool: *const InternPool) bool {
    return pool.indexToKey(val.index) == .undef;
}

pub fn isFloat(self: Value, pool: *const InternPool) bool {
    return switch (pool.indexToKey(self.index)) {
        .undef => unreachable,
        .float => true,
        else => false,
    };
}

pub fn isNan(val: Value, pool: *const InternPool) bool {
    return switch (pool.indexToKey(val.index)) {
        .float => |float| switch (float.storage) {
            inline else => |x| std.math.isNan(x),
        },
        else => false,
    };
}

pub fn order(lhs: Value, rhs: Value, pool: *const InternPool) std.math.Order {
    if (lhs.isFloat(pool) or rhs.isFloat(pool)) {
        const lhs_f128 = lhs.toFloat(f128, pool);
        const rhs_f128 = rhs.toFloat(f128, pool);
        return std.math.order(lhs_f128, rhs_f128);
    }
    var lhs_bigint_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_bigint_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_bigint_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_bigint_space, pool);
    return lhs_bigint.order(rhs_bigint);
}

pub fn compareHetero(lhs: Value, op: std.math.CompareOperator, rhs: Value, pool: *const InternPool) bool {
    if (lhs.isNan(pool) or rhs.isNan(pool)) return op == .neq;
    return order(lhs, rhs, pool).compare(op);
}

pub fn numberMin(lhs: Value, rhs: Value, pool: *const InternPool) Value {
    if (lhs.isUndef(pool) or rhs.isUndef(pool)) return undef;
    if (lhs.isNan(pool)) return rhs;
    if (rhs.isNan(pool)) return lhs;
    if (compareHetero(lhs, .lt, rhs, pool)) {
        return lhs;
    } else {
        return rhs;
    }
}

pub fn numberMax(lhs: Value, rhs: Value, pool: *const InternPool) Value {
    if (lhs.isUndef(pool) or rhs.isUndef(pool)) return undef;
    if (lhs.isNan(pool)) return rhs;
    if (rhs.isNan(pool)) return lhs;
    if (compareHetero(lhs, .gt, rhs, pool)) {
        return lhs;
    } else {
        return rhs;
    }
}

pub const OverflowArithmeticResult = struct {
    overflow_bit: Value,
    wrapped_result: Value,
};

pub fn toBool(val: Value) bool {
    return switch (val.index) {
        .bool_true => true,
        .bool_false => false,
        else => unreachable,
    };
}

pub fn makeBool(x: bool) Value {
    return if (x) bool_true else bool_false;
}

pub fn toUnsignedInt(val: Value, pool: *const InternPool) u64 {
    return getUnsignedInt(val, pool).?;
}

pub fn getUnsignedInt(val: Value, pool: *const InternPool) ?u64 {
    return switch (val.index) {
        .undef => unreachable,
        .null_value => 0,
        .bool_false => 0,
        .bool_true => 1,
        else => switch (pool.indexToKey(val.index)) {
            .undef => unreachable,
            .int => |int| switch (int.storage) {
                .big_int => |big_int| big_int.toInt(u64) catch null,
                .u64 => |x| x,
                .i64 => |x| std.math.cast(u64, x),
            },
            else => null,
        },
    };
}

pub fn eqlScalarNum(lhs: Value, rhs: Value, pool: *const InternPool) bool {
    if (lhs.isUndef(pool)) return false;
    if (rhs.isUndef(pool)) return false;
    if (lhs.isFloat(pool) or rhs.isFloat(pool)) {
        const lhs_f128 = lhs.toFloat(f128, pool);
        const rhs_f128 = rhs.toFloat(f128, pool);
        return lhs_f128 == rhs_f128;
    }
    var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    return lhs.toBigInt(&lhs_space, pool).eql(rhs.toBigInt(&rhs_space, pool));
}

pub fn compareAllWithZero(lhs: Value, op: std.math.CompareOperator, pool: *const InternPool) bool {
    return switch (pool.indexToKey(lhs.index)) {
        .float => |float| switch (float.storage) {
            inline else => |x| std.math.compare(x, op, 0),
        },
        .aggregate => |aggregate| {
            const len = pool.indexToKey(aggregate.ty).vector_type.len;
            var i: u64 = 0;
            return while (i < len) : (i += 1) {
                const elem = Value.fromIndex(InternPool.aggregateElementAt(aggregate, i));
                if (!elem.compareAllWithZero(op, pool)) break false;
            } else true;
        },
        else => {
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            return lhs.toBigInt(&space, pool).orderAgainstScalar(0).compare(op);
        },
    };
}

pub const void_value: Value = .{ .index = .void_value };
pub const bool_true: Value = .{ .index = .bool_true };
pub const bool_false: Value = .{ .index = .bool_false };
pub const zero_comptime_int: Value = .{ .index = .zero };
pub const one_comptime_int: Value = .{ .index = .one };
pub const zero_u1: Value = .{ .index = .zero_u1 };
pub const undef_u1: Value = .{ .index = .undef_u1 };

const testing = std.testing;

fn testInt(pool: *InternPool, x: i64) !Value {
    return .{ .index = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .i64 = x } }) };
}

fn testFloat(pool: *InternPool, x: f128) !Value {
    return .{ .index = try pool.internFloat(.{ .ty = .comptime_float_type, .storage = .{ .f128 = x } }) };
}

test "compareHetero: covers the six operators on ints" {
    var pool = try InternPool.init(testing.allocator);
    defer pool.deinit();
    const two = try testInt(&pool, 2);
    const five = try testInt(&pool, 5);
    try testing.expect(compareHetero(two, .lt, five, &pool));
    try testing.expect(compareHetero(two, .lte, five, &pool));
    try testing.expect(compareHetero(two, .neq, five, &pool));
    try testing.expect(compareHetero(five, .gt, two, &pool));
    try testing.expect(compareHetero(five, .gte, two, &pool));
    try testing.expect(!compareHetero(two, .eq, five, &pool));
}

test "compareHetero: equal ints" {
    var pool = try InternPool.init(testing.allocator);
    defer pool.deinit();
    const a = try testInt(&pool, 7);
    const b = try testInt(&pool, 7);
    try testing.expect(compareHetero(a, .eq, b, &pool));
    try testing.expect(compareHetero(a, .lte, b, &pool));
    try testing.expect(compareHetero(a, .gte, b, &pool));
    try testing.expect(!compareHetero(a, .neq, b, &pool));
}

test "compareHetero: sign is decisive" {
    var pool = try InternPool.init(testing.allocator);
    defer pool.deinit();
    const neg = try testInt(&pool, -5);
    const pos = try testInt(&pool, 2);
    try testing.expect(compareHetero(neg, .lt, pos, &pool));
    try testing.expect(!compareHetero(neg, .gt, pos, &pool));
}

test "compareHetero: a mixed int/float pair orders by value" {
    var pool = try InternPool.init(testing.allocator);
    defer pool.deinit();
    const five = try testInt(&pool, 5);
    const one = try testInt(&pool, 1);
    const one_point_five = try testFloat(&pool, 1.5);
    try testing.expect(compareHetero(five, .gt, one_point_five, &pool));
    try testing.expect(compareHetero(one, .lt, one_point_five, &pool));
}

test "compareHetero: float pair" {
    var pool = try InternPool.init(testing.allocator);
    defer pool.deinit();
    const a = try testFloat(&pool, 1.5);
    const b = try testFloat(&pool, 2.5);
    try testing.expect(compareHetero(a, .lt, b, &pool));
    try testing.expect(!compareHetero(a, .gte, b, &pool));
}

test "compareHetero: NaN is unordered, only != holds" {
    var pool = try InternPool.init(testing.allocator);
    defer pool.deinit();
    const nan = try testFloat(&pool, std.math.nan(f128));
    const one = try testFloat(&pool, 1.0);
    try testing.expect(!compareHetero(nan, .eq, one, &pool));
    try testing.expect(!compareHetero(nan, .lt, one, &pool));
    try testing.expect(!compareHetero(nan, .gt, one, &pool));
    try testing.expect(compareHetero(nan, .neq, one, &pool));
    try testing.expect(!compareHetero(nan, .eq, nan, &pool));
    try testing.expect(compareHetero(nan, .neq, nan, &pool));
}

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Type = @import("Type.zig");
const Sema = @import("Sema.zig");

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

pub const slice_ptr_index = 0;
pub const slice_len_index = 1;

pub fn getOffsetPtr(ptr_val: Value, byte_off: u64, new_ty: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (ptr_val.isUndef(pool)) return ptr_val;
    var ptr = pool.indexToKey(ptr_val.index).ptr;
    ptr.ty = new_ty.index;
    ptr.byte_offset += byte_off;
    return .fromIndex(try pool.internPtr(ptr));
}

pub fn doPointersOverlap(ptr_val_a: Value, ptr_val_b: Value, elem_count: u64, pool: *const InternPool) bool {
    const ip = pool;

    const a_elem_ty = ptr_val_a.typeOf(pool).indexableElem(pool);
    const b_elem_ty = ptr_val_b.typeOf(pool).indexableElem(pool);

    const a_ptr = ip.indexToKey(ptr_val_a.index).ptr;
    const b_ptr = ip.indexToKey(ptr_val_b.index).ptr;

    // If `a_elem_ty` is not comptime-only, then overlapping pointers have identical
    // `base_addr`, and we just need to look at the byte offset. If it *is* comptime-only,
    // then `base_addr` may be an `arr_elem`, and we'll have to consider the element index.
    if (a_elem_ty.comptimeOnly(pool)) {
        assert(a_elem_ty.index == b_elem_ty.index); // IMC comptime-only types are equivalent

        const a_base_addr: InternPool.Key.Ptr.BaseAddr, const a_idx: u64 = switch (a_ptr.base_addr) {
            else => .{ a_ptr.base_addr, 0 },
            .arr_elem => |arr_elem| a: {
                const base_ptr: Value = .fromIndex(arr_elem.base);
                const base_child_ty = base_ptr.typeOf(pool).childType(pool);
                if (base_child_ty.index == a_elem_ty.index) {
                    // This `arr_elem` is indexing into the element type we want.
                    const base_ptr_info = ip.indexToKey(base_ptr.index).ptr;
                    if (base_ptr_info.byte_offset != 0) {
                        return false; // this pointer is invalid, just let the access fail
                    }
                    break :a .{ base_ptr_info.base_addr, arr_elem.index };
                }
                break :a .{ a_ptr.base_addr, 0 };
            },
        };
        const b_base_addr: InternPool.Key.Ptr.BaseAddr, const b_idx: u64 = switch (a_ptr.base_addr) {
            else => .{ b_ptr.base_addr, 0 },
            .arr_elem => |arr_elem| b: {
                const base_ptr: Value = .fromIndex(arr_elem.base);
                const base_child_ty = base_ptr.typeOf(pool).childType(pool);
                if (base_child_ty.index == b_elem_ty.index) {
                    // This `arr_elem` is indexing into the element type we want.
                    const base_ptr_info = ip.indexToKey(base_ptr.index).ptr;
                    if (base_ptr_info.byte_offset != 0) {
                        return false; // this pointer is invalid, just let the access fail
                    }
                    break :b .{ base_ptr_info.base_addr, arr_elem.index };
                }
                break :b .{ b_ptr.base_addr, 0 };
            },
        };
        if (!std.meta.eql(a_base_addr, b_base_addr)) return false;
        const diff = if (a_idx >= b_idx) a_idx - b_idx else b_idx - a_idx;
        return diff < elem_count;
    } else {
        assert(a_elem_ty.abiSize(pool) == b_elem_ty.abiSize(pool));

        if (!std.meta.eql(a_ptr.base_addr, b_ptr.base_addr)) return false;

        const bytes_diff = if (a_ptr.byte_offset >= b_ptr.byte_offset)
            a_ptr.byte_offset - b_ptr.byte_offset
        else
            b_ptr.byte_offset - a_ptr.byte_offset;

        const need_bytes_diff = elem_count * a_elem_ty.abiSize(pool);
        return bytes_diff < need_bytes_diff;
    }
}

pub fn slicePtr(val: Value, pool: *const InternPool) Value {
    return .fromIndex(pool.indexToKey(val.index).slice.ptr);
}

pub fn ptrElem(orig_parent_ptr: Value, field_idx: u64, pool: *InternPool) std.mem.Allocator.Error!Value {
    const parent_ptr = switch (orig_parent_ptr.typeOf(pool).ptrInfo(pool).flags.size) {
        .one, .many, .c => orig_parent_ptr,
        .slice => orig_parent_ptr.slicePtr(pool),
    };

    const parent_ptr_ty = parent_ptr.typeOf(pool);
    const result_ty = try parent_ptr_ty.elemPtrType(field_idx, pool);
    const elem_ty = result_ty.childType(pool);

    if (parent_ptr.isUndef(pool)) return .fromIndex(try pool.get(.{ .undef = result_ty.index }));

    if (!elem_ty.comptimeOnly(pool)) {
        const byte_offset = field_idx * elem_ty.abiSize(pool);
        return parent_ptr.getOffsetPtr(byte_offset, result_ty, pool);
    }

    // Comptime-only element type.

    if (field_idx == 0) {
        return .fromIndex(try pool.getCoerced(parent_ptr.index, result_ty.index));
    }

    const arr_base_ty, const arr_base_len = elem_ty.arrayBase(pool);
    const base_idx = arr_base_len * field_idx;
    const parent_info = pool.indexToKey(parent_ptr.index).ptr;
    switch (parent_info.base_addr) {
        .arr_elem => |arr_elem| {
            if (Value.fromIndex(arr_elem.base).typeOf(pool).childType(pool).index == arr_base_ty.index) {
                // We already have a pointer to an element of an array of this type.
                // Just modify the index.
                return .fromIndex(try pool.internPtr(ptr: {
                    var new = parent_info;
                    new.base_addr.arr_elem.index += base_idx;
                    new.ty = result_ty.index;
                    break :ptr new;
                }));
            }
        },
        else => {},
    }
    const base_ptr = try parent_ptr.canonicalizeBasePtr(.many, arr_base_ty, pool);
    return .fromIndex(try pool.internPtr(.{
        .ty = result_ty.index,
        .base_addr = .{ .arr_elem = .{
            .base = base_ptr.index,
            .index = base_idx,
        } },
        .byte_offset = 0,
    }));
}

pub fn canonicalizeBasePtr(base_ptr: Value, want_size: InternPool.Key.PtrType.Size, want_child: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
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
        .@"struct" => switch (aggregate_ty.containerLayout(pool)) {
            .auto => {},
            .@"extern" => return parent_ptr.getOffsetPtr(aggregate_ty.structFieldOffset(pool, field_idx), field_ptr_ty, pool),
            .@"packed" => return .fromIndex(try pool.getCoerced(parent_ptr.index, field_ptr_ty.index)),
        },
        .@"union" => switch (aggregate_ty.containerLayout(pool)) {
            .auto => {},
            .@"packed", .@"extern" => return .fromIndex(try pool.getCoerced(parent_ptr.index, field_ptr_ty.index)),
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

/// The backing integer of an enum tag or a packed aggregate value, for `@backingInt`.
pub fn backingInt(val: Value, pool: *const InternPool) Value {
    return switch (pool.indexToKey(val.index)) {
        .enum_tag => |enum_tag| .fromIndex(enum_tag.int),
        .bitpack => |bitpack| .fromIndex(bitpack.backing_int_val),
        else => unreachable,
    };
}

pub fn unionTag(val: Value, pool: *const InternPool) ?Value {
    return switch (pool.indexToKey(val.index)) {
        .undef, .enum_tag => val,
        .un => |un| if (un.tag != .none) .fromIndex(un.tag) else null,
        else => unreachable,
    };
}

pub fn unionPayload(val: Value, pool: *const InternPool) Value {
    return switch (pool.indexToKey(val.index)) {
        .un => |un| .fromIndex(un.val),
        else => unreachable,
    };
}

pub fn optionalValue(val: Value, pool: *const InternPool) ?Value {
    return switch (pool.indexToKey(val.index)) {
        .opt => |opt| switch (opt.val) {
            .none => null,
            else => |payload| .fromIndex(payload),
        },
        .ptr => val,
        else => unreachable,
    };
}

/// Byte-oriented (ABI-layout) serialization of a value to memory. Ported from the compiler's
/// `Value.writeToMemory`; the REPL evaluates for the native target, so endianness comes from `builtin`.
pub fn writeToMemory(val: Value, pool: *const InternPool, buffer: []u8) error{
    ReinterpretDeclRef,
    IllDefinedMemoryLayout,
    OutOfMemory,
}!void {
    const endian = builtin.target.cpu.arch.endian();
    const ty = val.typeOf(pool);
    if (val.isUndef(pool)) {
        const size: usize = @intCast(ty.abiSize(pool));
        @memset(buffer[0..size], 0xAA);
        return;
    }
    tag: switch (ty.zigTypeTag(pool)) {
        .type,
        .comptime_float,
        .comptime_int,
        .undefined,
        .null,
        .error_union,
        .enum_literal,
        .@"fn",
        .spirv,
        => return error.IllDefinedMemoryLayout,
        .@"opaque", .frame, .@"anyframe", .noreturn => unreachable,
        .void => {},
        .bool => {
            buffer[0] = @intFromBool(val.toBool());
        },
        .pointer => {
            if (ty.isSlice(pool)) return error.IllDefinedMemoryLayout;
            if (pool.getBackingAddrTag(val.index).? != .int) return error.ReinterpretDeclRef;
            continue :tag .int;
        },
        .int, .@"enum", .error_set => {
            var bigint_buffer: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const bigint = val.toBigInt(&bigint_buffer, pool);
            bigint.writeTwosComplement(buffer[0..@intCast(ty.abiSize(pool))], endian);
        },
        .float => {
            const float_bits = ty.floatBits();
            switch (float_bits) {
                16 => std.mem.writeInt(u16, buffer[0..2], @bitCast(val.toFloat(f16, pool)), endian),
                32 => std.mem.writeInt(u32, buffer[0..4], @bitCast(val.toFloat(f32, pool)), endian),
                64 => std.mem.writeInt(u64, buffer[0..8], @bitCast(val.toFloat(f64, pool)), endian),
                80 => std.mem.writeInt(u80, buffer[0..10], @bitCast(val.toFloat(f80, pool)), endian),
                128 => std.mem.writeInt(u128, buffer[0..16], @bitCast(val.toFloat(f128, pool)), endian),
                else => unreachable,
            }
            const float_bytes = @divExact(float_bits, 8);
            const total_bytes: usize = @intCast(ty.abiSize(pool));
            @memset(buffer[float_bytes..total_bytes], 0); // padding
        },
        .array => {
            const aggregate = pool.indexToKey(val.index).aggregate;
            const len = ty.arrayLen(pool);
            const elem_ty = ty.childType(pool);
            const elem_size: usize = @intCast(elem_ty.abiSize(pool));
            var elem_i: usize = 0;
            var buf_off: usize = 0;
            while (elem_i < len) : (elem_i += 1) {
                switch (aggregate.storage) {
                    .bytes => |bytes| buffer[buf_off] = bytes.at(elem_i, pool),
                    .elems => |elems| try Value.fromIndex(elems[elem_i]).writeToMemory(pool, buffer[buf_off..]),
                    .repeated_elem => |elem| try Value.fromIndex(elem).writeToMemory(pool, buffer[buf_off..]),
                }
                buf_off += elem_size;
            }
            if (ty.sentinel(pool)) |sentinel_val| {
                try sentinel_val.writeToMemory(pool, buffer[buf_off..]);
            }
        },
        .vector => return error.IllDefinedMemoryLayout,
        .@"struct" => {
            const struct_type = pool.typeToStruct(ty.index) orelse return error.IllDefinedMemoryLayout;
            switch (struct_type.layout) {
                .auto => return error.IllDefinedMemoryLayout,
                .@"extern" => {
                    var last_off: usize = 0;
                    for (struct_type.field_types, 0..) |field_ty_ip, field_index| {
                        const off: usize = @intCast(ty.structFieldOffset(pool, field_index));
                        @memset(buffer[last_off..off], 0xAA);
                        const field_val: Value = .fromIndex(switch (pool.indexToKey(val.index).aggregate.storage) {
                            .bytes => |bytes| {
                                buffer[off] = bytes.at(field_index, pool);
                                continue;
                            },
                            .elems => |elems| elems[field_index],
                            .repeated_elem => |elem| elem,
                        });
                        try writeToMemory(field_val, pool, buffer[off..]);
                        last_off = @intCast(off + Type.fromIndex(field_ty_ip).abiSize(pool));
                    }
                    const struct_size: usize = @intCast(ty.abiSize(pool));
                    @memset(buffer[last_off..struct_size], 0xAA);
                },
                .@"packed" => {
                    const int_index = pool.indexToKey(val.index).bitpack.backing_int_val;
                    return Value.fromIndex(int_index).writeToMemory(pool, buffer);
                },
            }
        },
        .@"union" => switch (ty.containerLayout(pool)) {
            .auto => return error.IllDefinedMemoryLayout, // Sema is supposed to have emitted a compile error already
            .@"extern" => {
                const payload_val = val.unionPayload(pool);
                const payload_size: usize = @intCast(payload_val.typeOf(pool).abiSize(pool));
                const union_size: usize = @intCast(ty.abiSize(pool));
                @memset(buffer[payload_size..union_size], 0xAA);
                return writeToMemory(payload_val, pool, buffer);
            },
            .@"packed" => {
                const int_val: Value = .fromIndex(pool.indexToKey(val.index).bitpack.backing_int_val);
                return writeToMemory(int_val, pool, buffer);
            },
        },
        .optional => {
            if (!ty.isPtrLikeOptional(pool)) return error.IllDefinedMemoryLayout;
            const opt_val = val.optionalValue(pool);
            if (opt_val) |some| {
                return some.writeToMemory(pool, buffer);
            } else {
                const byte_count = Type.fromIndex(.usize_type).abiSize(pool);
                @memset(buffer[0..@intCast(byte_count)], 0); // null pointer
            }
        },
    }
}

/// Read an integer of type `ty` from a byte buffer. Ported from the compiler's `Value.readIntFromMemory`.
pub fn readIntFromMemory(ty: Type, pool: *InternPool, buffer: []const u8, arena: std.mem.Allocator) std.mem.Allocator.Error!Value {
    const endian = builtin.target.cpu.arch.endian();
    const int = ty.intInfo(pool);
    const abi_size: usize = @intCast(ty.abiSize(pool));
    const exact_buf = buffer[0..abi_size];

    if (abi_size <= 8) {
        const shift: u6 = @intCast(64 - int.bits);
        switch (int.signedness) {
            .unsigned => {
                const x = std.mem.readVarInt(u64, exact_buf, endian);
                return .fromIndex(try pool.internInt(.{ .ty = ty.index, .storage = .{ .u64 = (x << shift) >> shift } }));
            },
            .signed => {
                const x = std.mem.readVarInt(i64, exact_buf, endian);
                return .fromIndex(try pool.internInt(.{ .ty = ty.index, .storage = .{ .i64 = (x << shift) >> shift } }));
            },
        }
    } else {
        const limb_count = std.math.big.int.calcTwosCompLimbCount(int.bits);
        const limbs_buffer = try arena.alloc(std.math.big.Limb, limb_count);
        var bigint: std.math.big.int.Mutable = .init(limbs_buffer, 0);
        bigint.readTwosComplement(exact_buf, int.bits, endian, int.signedness);
        return .fromIndex(try pool.internIntValue(ty.index, bigint.toConst()));
    }
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
                .bytes => |bytes| for (0..len) |i| {
                    std.mem.writeVarPackedInt(buffer, elem_bit_off, elem_bits, bytes.at(i, pool), endian);
                    elem_bit_off += elem_bits;
                },
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
    return .fromIndex(pool.typeOf(val.index));
}

pub fn errorUnionIsPayload(val: Value, pool: *const InternPool) bool {
    return pool.indexToKey(val.index).error_union.val == .payload;
}

pub fn canMutateComptimeVarState(val: Value, pool: *const InternPool) bool {
    return switch (pool.indexToKey(val.index)) {
        .error_union => |error_union| switch (error_union.val) {
            .err_name => false,
            .payload => |payload| Value.fromIndex(payload).canMutateComptimeVarState(pool),
        },
        .ptr => |ptr| switch (ptr.base_addr) {
            .nav => false, // The value of a Nav can never reference a comptime alloc.
            .int => false,
            .comptime_alloc => true, // A comptime alloc is either mutable or references comptime-mutable memory.
            .comptime_field => true, // Comptime field pointers are comptime-mutable, albeit only to the "correct" value.
            .eu_payload, .opt_payload => |base| Value.fromIndex(base).canMutateComptimeVarState(pool),
            .uav => |uav| Value.fromIndex(uav.val).canMutateComptimeVarState(pool),
            .arr_elem, .field => |base_index| Value.fromIndex(base_index.base).canMutateComptimeVarState(pool),
        },
        .slice => |slice| Value.fromIndex(slice.ptr).canMutateComptimeVarState(pool),
        .opt => |opt| switch (opt.val) {
            .none => false,
            else => |payload| Value.fromIndex(payload).canMutateComptimeVarState(pool),
        },
        .aggregate => |aggregate| for (aggregate.storage.values()) |elem| {
            if (Value.fromIndex(elem).canMutateComptimeVarState(pool)) break true;
        } else false,
        .un => |un| Value.fromIndex(un.val).canMutateComptimeVarState(pool),
        else => false,
    };
}

pub fn toFloat(val: Value, comptime T: type, pool: *const InternPool) T {
    return switch (pool.indexToKey(val.index)) {
        .int => |int| switch (int.storage) {
            .big_int => |big_int| big_int.toFloat(T, .nearest_even)[0],
            inline .u64, .i64 => |x| @floatFromInt(x),
        },
        .float => |float| switch (float.storage) {
            inline else => |x| @floatCast(x),
        },
        else => unreachable,
    };
}

pub fn floatCast(val: Value, dest_ty: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (val.isUndef(pool)) return .fromIndex(try pool.get(.{ .undef = dest_ty.index }));
    return .fromIndex(try pool.internFloat(.{
        .ty = dest_ty.index,
        .storage = switch (dest_ty.floatBits()) {
            16 => .{ .f16 = val.toFloat(f16, pool) },
            32 => .{ .f32 = val.toFloat(f32, pool) },
            64 => .{ .f64 = val.toFloat(f64, pool) },
            80 => .{ .f80 = val.toFloat(f80, pool) },
            128 => .{ .f128 = val.toFloat(f128, pool) },
            else => unreachable,
        },
    }));
}

pub fn elemValue(val: Value, pool: *InternPool, index: usize) std.mem.Allocator.Error!Value {
    switch (pool.indexToKey(val.index)) {
        .undef => |ty| return .fromIndex(try pool.get(.{ .undef = Type.fromIndex(ty).childType(pool).index })),
        .aggregate => |aggregate| {
            const len = pool.aggregateTypeLen(aggregate.ty);
            if (index < len) return .fromIndex(switch (aggregate.storage) {
                .bytes => |bytes| try pool.get(.{ .int = .{
                    .ty = .u8_type,
                    .storage = .{ .u64 = bytes.at(index, pool) },
                } }),
                .elems => |elems| elems[index],
                .repeated_elem => |elem| elem,
            });
            assert(index == len);
            return Type.fromIndex(aggregate.ty).sentinel(pool).?;
        },
        else => unreachable,
    }
}

/// Asserts the value is an aggregate/union, and returns the value of the field at `index`.
pub fn fieldValue(val: Value, index: usize, pool: *InternPool) std.mem.Allocator.Error!Value {
    return switch (pool.indexToKey(val.index)) {
        .undef => |ty| .fromIndex(try pool.get(.{
            .undef = Type.fromIndex(ty).fieldType(index, pool).index,
        })),
        .aggregate => |aggregate| .fromIndex(switch (aggregate.storage) {
            .bytes => |bytes| try pool.get(.{ .int = .{
                .ty = .u8_type,
                .storage = .{ .u64 = bytes.at(index, pool) },
            } }),
            .elems => |elems| elems[index],
            .repeated_elem => |elem| elem,
        }),
        .un => |un| blk: {
            switch (Type.fromIndex(un.ty).containerLayout(pool)) {
                .auto, .@"extern" => {}, // TODO assert the tag is correct
                .@"packed" => unreachable,
            }
            break :blk .fromIndex(un.val);
        },
        .bitpack => |bitpack| blk: {
            const ty: Type = .fromIndex(bitpack.ty);
            assert(ty.containerLayout(pool) == .@"packed");
            const int_val: Value = .fromIndex(bitpack.backing_int_val);
            assert(!int_val.isUndef(pool));
            const field_ty = ty.fieldType(index, pool);
            const field_bit_offset: u16 = switch (ty.zigTypeTag(pool)) {
                .@"union" => 0,
                .@"struct" => off: {
                    var off: u16 = 0;
                    for (0..index) |preceding_field_index| {
                        off += @intCast(ty.fieldType(preceding_field_index, pool).bitSize(pool));
                    }
                    break :off off;
                },
                else => unreachable,
            };
            const buf = try pool.gpa.alloc(u8, @intCast((ty.bitSize(pool) + 7) / 8));
            defer pool.gpa.free(buf);
            @memset(buf, 0);
            int_val.writeToPackedMemory(pool, buf, 0);
            break :blk try readFromPackedMemory(field_ty, pool, buf, field_bit_offset);
        },
        else => unreachable,
    };
}

/// Read this comptime value into the native `std.lang` type `T`, the inverse of the compiler's
/// `uninterpret`, used to bring reflection structures back into the host. `.direct` mode: `std.lang`
/// is assumed to match what the REPL was built against, so fields are matched by index and enum tags
/// by integer value. `TypeMismatch` therefore signals a corrupt `std.lang`.
pub fn interpret(val: Value, comptime T: type, pool: *InternPool) error{ OutOfMemory, UndefinedValue, TypeMismatch }!T {
    const ty = val.typeOf(pool);
    if (ty.zigTypeTag(pool) != @typeInfo(T)) return error.TypeMismatch;
    if (val.isUndef(pool)) return error.UndefinedValue;

    return switch (@typeInfo(T)) {
        .type,
        .noreturn,
        .comptime_float,
        .comptime_int,
        .undefined,
        .null,
        .@"fn",
        .@"opaque",
        .spirv,
        .enum_literal,
        => comptime unreachable, // comptime-only or otherwise impossible

        .pointer,
        .array,
        .error_union,
        .error_set,
        .frame,
        .@"anyframe",
        .vector,
        => comptime unreachable, // unsupported

        .void => {},

        .bool => switch (val.index) {
            .bool_false => false,
            .bool_true => true,
            else => unreachable,
        },

        .int => switch (pool.indexToKey(val.index).int.storage) {
            inline .u64, .i64 => |x| std.math.cast(T, x) orelse return error.TypeMismatch,
            .big_int => |big| big.toInt(T) catch return error.TypeMismatch,
        },

        .float => val.toFloat(T, pool),

        .optional => |opt| if (val.optionalValue(pool)) |unwrapped|
            try unwrapped.interpret(opt.child, pool)
        else
            null,

        .@"enum" => {
            const int = val.getUnsignedInt(pool) orelse return error.TypeMismatch;
            return std.enums.fromInt(T, int) orelse error.TypeMismatch;
        },

        .@"union" => |@"union"| {
            const tag_val = val.unionTag(pool) orelse return error.TypeMismatch;
            const tag = try tag_val.interpret(@"union".tag_type.?, pool);
            return switch (tag) {
                inline else => |tag_comptime| @unionInit(
                    T,
                    @tagName(tag_comptime),
                    try val.unionPayload(pool).interpret(@FieldType(T, @tagName(tag_comptime)), pool),
                ),
            };
        },

        .@"struct" => |@"struct"| {
            if (pool.loadStructType(ty.index).field_types.len != @"struct".field_names.len) return error.TypeMismatch;
            var result: T = undefined;
            inline for (@"struct".field_names, @"struct".field_types, 0..) |field_name, field_type, field_idx| {
                const field_val = try val.fieldValue(field_idx, pool);
                @field(result, field_name) = try field_val.interpret(field_type, pool);
            }
            return result;
        },
    };
}

/// The inverse of `interpret`: construct a comptime `Value` of type `ty` from the native `std.lang`
/// value `val` (direct mode, so fields are matched by index and enum tags by integer value). A shape
/// that does not match `ty` means a corrupt `std.lang`. Unlike `interpret`, this takes `sema`: minting
/// a union or struct value drives the lazy union-tag-enum and field resolution, which live on `Sema`.
pub fn uninterpret(val: anytype, ty: Type, sema: *Sema) Sema.Error!Value {
    const T = @TypeOf(val);
    const ip = sema.intern_pool;
    if (ty.zigTypeTag(ip) != @typeInfo(T)) @panic("std.lang is corrupt");

    return switch (@typeInfo(T)) {
        .type,
        .noreturn,
        .comptime_float,
        .comptime_int,
        .undefined,
        .null,
        .@"fn",
        .@"opaque",
        .spirv,
        .enum_literal,
        => comptime unreachable, // comptime-only or otherwise impossible

        .pointer,
        .array,
        .error_union,
        .error_set,
        .frame,
        .@"anyframe",
        .vector,
        => comptime unreachable, // unsupported

        .void => .fromIndex(.void_value),

        .bool => .fromIndex(if (val) .bool_true else .bool_false),

        .int => .fromIndex(try ip.internInt(.{
            .ty = ty.index,
            .storage = switch (@typeInfo(T).int.signedness) {
                .unsigned => .{ .u64 = @intCast(val) },
                .signed => .{ .i64 = @intCast(val) },
            },
        })),

        .float => .fromIndex(try ip.internFloat(.{
            .ty = ty.index,
            .storage = switch (T) {
                f16 => .{ .f16 = val },
                f32 => .{ .f32 = val },
                f64 => .{ .f64 = val },
                f80 => .{ .f80 = val },
                f128 => .{ .f128 = val },
                else => comptime unreachable,
            },
        })),

        .optional => if (val) |some|
            .fromIndex(try ip.internOpt(.{
                .ty = ty.index,
                .val = (try uninterpret(some, ty.optionalChild(ip), sema)).index,
            }))
        else
            .fromIndex(try ip.internOpt(.{ .ty = ty.index, .val = .none })),

        .@"enum" => .fromIndex(try ip.internEnumTag(.{
            .ty = ty.index,
            .int = (try uninterpret(@backingInt(val), .fromIndex(ip.loadEnumType(ty.index).int_tag_type), sema)).index,
        })),

        .@"union" => |@"union"| {
            const tag: @"union".tag_type.? = val;
            // The REPL's union tag enum is resolved lazily (the compiler's `unionTagType` reads a
            // stored one); resolving the layout also makes the field types available.
            try sema.ensureLayoutResolved(ty.index);
            const tag_val = try uninterpret(tag, .fromIndex(try sema.unionTagEnumType(ty.index)), sema);
            const field_ty = ty.unionFieldType(tag_val, ip) orelse @panic("std.lang is corrupt");
            return switch (val) {
                inline else => |payload| .fromIndex(try ip.internUnion(.{
                    .ty = ty.index,
                    .tag = tag_val.index,
                    .val = (try uninterpret(payload, field_ty, sema)).index,
                })),
            };
        },

        .@"struct" => |@"struct"| {
            if (try sema.structFieldCount(ty.index) != @"struct".field_names.len) @panic("std.lang is corrupt");
            // `Type.fieldType` asserts a resolved layout; the REPL resolves it lazily.
            try sema.ensureLayoutResolved(ty.index);
            var field_vals: [@"struct".field_names.len]InternPool.Index = undefined;
            inline for (&field_vals, @"struct".field_names, 0..) |*field_val, field_name, field_idx| {
                field_val.* = (try uninterpret(@field(val, field_name), ty.fieldType(field_idx, ip), sema)).index;
            }
            return try sema.aggregateValue(ty, &field_vals);
        },
    };
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
    if (val.getUnsignedInt(pool)) |x| return std.math.big.int.Mutable.init(&space.limbs, x).toConst();
    const int_key = switch (pool.indexToKey(val.index)) {
        .enum_tag => |enum_tag| pool.indexToKey(enum_tag.int).int,
        .bitpack => |bitpack| pool.indexToKey(bitpack.backing_int_val).int,
        .int => |int| int,
        else => unreachable,
    };
    return int_key.storage.toBigInt(space);
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

pub fn getErrorName(val: Value, pool: *const InternPool) InternPool.OptionalNullTerminatedString {
    return switch (pool.indexToKey(val.index)) {
        .err => |err| err.name.toOptional(),
        .error_union => |error_union| switch (error_union.val) {
            .err_name => |err_name| err_name.toOptional(),
            .payload => .none,
        },
        else => unreachable,
    };
}

pub fn isNull(val: Value, pool: *const InternPool) bool {
    return switch (val.index) {
        .undef => unreachable,
        .unreachable_value => unreachable,
        .null_value => true,
        else => switch (pool.indexToKey(val.index)) {
            .undef => unreachable,
            .ptr => |ptr| switch (ptr.base_addr) {
                .int => ptr.byte_offset == 0,
                else => false,
            },
            .opt => |opt| opt.val == .none,
            else => false,
        },
    };
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

pub fn pointerNav(val: Value, pool: *const InternPool) ?InternPool.Nav.Index {
    return switch (pool.indexToKey(val.index)) {
        .@"extern" => |e| e.owner_nav,
        .func => |func| func.owner_nav.unwrap(),
        .ptr => |ptr| if (ptr.byte_offset == 0) switch (ptr.base_addr) {
            .nav => |nav| nav,
            else => null,
        } else null,
        else => null,
    };
}

pub fn compareHetero(lhs: Value, op: std.math.CompareOperator, rhs: Value, pool: *const InternPool) bool {
    if (lhs.pointerNav(pool)) |lhs_nav| {
        if (rhs.pointerNav(pool)) |rhs_nav| {
            switch (op) {
                .eq => return lhs_nav == rhs_nav,
                .neq => return lhs_nav != rhs_nav,
                else => {},
            }
        } else {
            switch (op) {
                .eq => return false,
                .neq => return true,
                else => {},
            }
        }
    } else if (rhs.pointerNav(pool)) |_| {
        switch (op) {
            .eq => return false,
            .neq => return true,
            else => {},
        }
    }
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
            .ptr => |ptr| switch (ptr.base_addr) {
                .int => ptr.byte_offset,
                .field => |field| {
                    const base_addr = Value.fromIndex(field.base).getUnsignedInt(pool) orelse return null;
                    const struct_ty = Value.fromIndex(field.base).typeOf(pool).childType(pool);
                    return base_addr + struct_ty.structFieldOffset(pool, @intCast(field.index)) + ptr.byte_offset;
                },
                else => null,
            },
            .opt => |opt| switch (opt.val) {
                .none => 0,
                else => |payload| Value.fromIndex(payload).getUnsignedInt(pool),
            },
            .enum_tag => |enum_tag| Value.fromIndex(enum_tag.int).getUnsignedInt(pool),
            .bitpack => |bitpack| Value.fromIndex(bitpack.backing_int_val).getUnsignedInt(pool),
            .err => |err| pool.getErrorValueIfExists(err.name).?,
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
        .aggregate => |aggregate| switch (aggregate.storage) {
            .bytes => |bytes| for (bytes.toSlice(lhs.typeOf(pool).arrayLenIncludingSentinel(pool), pool)) |byte| {
                if (!std.math.compare(byte, op, 0)) break false;
            } else true,
            .elems => |elems| for (elems) |elem| {
                if (!Value.fromIndex(elem).compareAllWithZero(op, pool)) break false;
            } else true,
            .repeated_elem => |elem| Value.fromIndex(elem).compareAllWithZero(op, pool),
        },
        .undef => false,
        else => order(lhs, .zero_comptime_int, pool).compare(op),
    };
}

pub fn eql(a: Value, b: Value, ty: Type, pool: *const InternPool) bool {
    assert(a.typeOf(pool).index == ty.index);
    assert(b.typeOf(pool).index == ty.index);
    return a.index == b.index;
}

pub fn compareScalar(lhs: Value, op: std.math.CompareOperator, rhs: Value, ty: Type, pool: *const InternPool) bool {
    return switch (op) {
        .eq => lhs.eql(rhs, ty, pool),
        .neq => !lhs.eql(rhs, ty, pool),
        else => compareHetero(lhs, op, rhs, pool),
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

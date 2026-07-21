//! This file contains logic for bit-casting arbitrary values at comptime, including splicing
//! bits together for comptime stores of bit-pointers. The strategy is to "flatten" values to
//! a sequence of values in *packed* memory, and then unflatten through a combination of special
//! cases (particularly for pointers and `undefined` values) and in-memory buffer reinterprets.

pub fn castMemory(sema: *Sema, val: Value, dest_ty: Type, byte_offset: u64) Sema.Error!?Value {
    const ip = sema.intern_pool;
    const val_ty = val.typeOf(ip);

    if (dest_ty.index == val_ty.index) {
        assert(byte_offset == 0);
        return val;
    }

    var unpack: UnpackValueBytes = .{
        .sema = sema,
        .skip_bytes = byte_offset,
        .remaining_bytes = dest_ty.abiSize(ip),
        .unpacked = .init(sema.arena),
    };
    unpack.add(val) catch |err| switch (err) {
        error.ReinterpretDeclRef => return null,
        else => |e| return e,
    };

    var pack: PackValueBytes = .{
        .sema = sema,
        .unpacked = unpack.unpacked.items,
    };
    return pack.get(dest_ty) catch |err| switch (err) {
        error.ReinterpretDeclRef => return null,
        else => |e| return e,
    };
}

/// Splice `splice_val` into `val` at `byte_offset`, replacing overlapping bits.
pub fn spliceMemory(sema: *Sema, val: Value, splice_val: Value, byte_offset: u64) Sema.Error!?Value {
    const ip = sema.intern_pool;
    const val_ty = val.typeOf(ip);
    const splice_val_ty = splice_val.typeOf(ip);

    var unpack: UnpackValueBytes = .{
        .sema = sema,
        .skip_bytes = 0,
        .remaining_bytes = byte_offset,
        .unpacked = .init(sema.arena),
    };
    unpack.add(val) catch |err| switch (err) {
        error.ReinterpretDeclRef => return null,
        else => |e| return e,
    };

    const splice_len = splice_val_ty.abiSize(ip);

    unpack.remaining_bytes = splice_len;
    unpack.add(splice_val) catch |err| switch (err) {
        error.ReinterpretDeclRef => return null,
        else => |e| return e,
    };

    unpack.skip_bytes = byte_offset + splice_len;
    unpack.remaining_bytes = val_ty.abiSize(ip) * 8 - byte_offset - splice_len;
    unpack.add(val) catch |err| switch (err) {
        error.ReinterpretDeclRef => return null,
        else => |e| return e,
    };

    var pack: PackValueBytes = .{
        .sema = sema,
        .unpacked = unpack.unpacked.items,
    };
    return pack.get(val_ty) catch |err| switch (err) {
        error.ReinterpretDeclRef => return null,
        else => |e| return e,
    };
}

const UnpackValueBytes = struct {
    sema: *Sema,
    skip_bytes: u64,
    remaining_bytes: u64,
    unpacked: std.array_list.Managed(InternPool.Index),

    fn add(unpack: *UnpackValueBytes, val: Value) (error{ReinterpretDeclRef} || Sema.Error)!void {
        const ip = unpack.sema.intern_pool;

        if (unpack.remaining_bytes == 0) return;

        const ty = val.typeOf(ip);
        const size = ty.abiSize(ip);

        if (unpack.skip_bytes >= size) {
            unpack.skip_bytes -= size;
            return;
        }

        switch (ip.indexToKey(val.index)) {
            .undef,
            .int,
            .enum_tag,
            .simple_value,
            .float,
            .ptr,
            .opt,
            => try unpack.primitive(val),

            .bitpack => |bitpack| try unpack.primitive(.fromIndex(bitpack.backing_int_val)),

            .aggregate => switch (ty.zigTypeTag(ip)) {
                .vector => unreachable, // ill-defined layout
                .array => {
                    for (0..@intCast(ty.arrayLen(ip))) |elem_index| {
                        const elem_val = try val.elemValue(ip, @intCast(elem_index));
                        try unpack.add(elem_val);
                    }
                    if (ty.sentinel(ip)) |s| {
                        try unpack.add(s);
                    }
                },
                .@"struct" => switch (ty.containerLayout(ip)) {
                    .auto => unreachable, // ill-defined layout
                    .@"packed" => unreachable, // uses `.bitpack`, not `.aggregate`
                    .@"extern" => {
                        const field_count = ip.aggregateElementCount(ty.index);
                        var offset: u64 = 0;
                        for (0..@intCast(field_count)) |field_index| {
                            const pad_bytes = ty.structFieldOffset(ip, field_index) - offset;
                            const field_val = try val.fieldValue(field_index, ip);
                            try unpack.padding(pad_bytes);
                            try unpack.add(field_val);
                            offset += pad_bytes + field_val.typeOf(ip).abiSize(ip);
                        }
                        try unpack.padding(size - offset);
                    },
                },
                else => unreachable,
            },

            .un => |un| {
                const payload_val: Value = .fromIndex(un.val);
                const pad_bytes = size - payload_val.typeOf(ip).abiSize(ip);
                try unpack.add(payload_val);
                try unpack.padding(pad_bytes);
            },

            else => unreachable, // ill-defined layout or not real values
        }
    }

    fn padding(unpack: *UnpackValueBytes, num_bytes: u64) Sema.Error!void {
        if (num_bytes == 0) return;
        const undef_u8: Value = .fromIndex(try unpack.sema.intern_pool.get(.{ .undef = .u8_type }));
        for (0..@intCast(num_bytes)) |_| {
            unpack.primitive(undef_u8) catch |err| switch (err) {
                error.ReinterpretDeclRef => unreachable,
                else => |e| return e,
            };
        }
    }

    fn primitive(unpack: *UnpackValueBytes, val: Value) (error{ReinterpretDeclRef} || Sema.Error)!void {
        const ip = unpack.sema.intern_pool;

        if (unpack.remaining_bytes == 0) return;

        const ty = val.typeOf(ip);
        const size = ty.abiSize(ip);

        if (unpack.skip_bytes >= size) {
            unpack.skip_bytes -= size;
            return;
        }

        if (unpack.skip_bytes > 0) {
            const offset = unpack.skip_bytes;
            unpack.skip_bytes = 0;
            return unpack.splitPrimitive(val, offset, @min(size - offset, unpack.remaining_bytes));
        }

        if (unpack.remaining_bytes < size) {
            return unpack.splitPrimitive(val, 0, unpack.remaining_bytes);
        }

        unpack.remaining_bytes -= size;
        try unpack.unpacked.append(val.index);
    }

    fn splitPrimitive(unpack: *UnpackValueBytes, val: Value, offset: u64, len: u64) (error{ReinterpretDeclRef} || Sema.Error)!void {
        const sema = unpack.sema;
        const ip = sema.intern_pool;
        const ty = val.typeOf(ip);

        assert(offset + len <= ty.abiSize(ip));

        try unpack.unpacked.ensureUnusedCapacity(@intCast(len));
        unpack.remaining_bytes -= len;

        switch (ip.indexToKey(val.index)) {
            // In the `ptr` case, `writeToMemory` returns `error.ReinterpretDeclRef` for a non-integer pointer.
            .int, .float, .enum_tag, .ptr, .opt => {
                const buf = try sema.arena.alloc(u8, @intCast(ty.abiSize(ip)));
                val.writeToMemory(ip, buf) catch |err| switch (err) {
                    error.IllDefinedMemoryLayout => unreachable,
                    else => |e| return e,
                };
                for (buf[@intCast(offset)..][0..@intCast(len)]) |byte_raw| {
                    const byte_val = try sema.intValue_u64(.fromIndex(.u8_type), byte_raw);
                    unpack.unpacked.appendAssumeCapacity(byte_val.index);
                }
            },
            .undef => {
                const undef_u8 = try ip.get(.{ .undef = .u8_type });
                for (0..@intCast(len)) |_| {
                    unpack.unpacked.appendAssumeCapacity(undef_u8);
                }
            },
            .simple_value => unreachable, // only true/false, both 1 byte
            else => unreachable, // zero-bit or not primitives
        }
    }
};

const PackValueBytes = struct {
    sema: *Sema,
    byte_offset: u64 = 0,
    unpacked: []const InternPool.Index,

    fn get(pack: *PackValueBytes, ty: Type) (Sema.Error || error{ReinterpretDeclRef})!Value {
        const sema = pack.sema;
        const ip = sema.intern_pool;
        const arena = sema.arena;
        switch (ty.zigTypeTag(ip)) {
            .vector => unreachable, // ill-defined layout
            .array => {
                const elem_ty = ty.childType(ip);
                const elems = try arena.alloc(InternPool.Index, @intCast(ty.arrayLen(ip)));
                for (elems) |*elem| {
                    elem.* = (try pack.get(elem_ty)).index;
                }
                if (ty.sentinel(ip)) |_| {
                    pack.padding(elem_ty.abiSize(ip));
                }
                return try sema.aggregateValue(ty, elems);
            },
            .@"struct" => switch (ty.containerLayout(ip)) {
                .auto => unreachable, // ill-defined layout
                .@"extern" => {
                    const field_count = ip.aggregateElementCount(ty.index);
                    const elems = try arena.alloc(InternPool.Index, @intCast(field_count));
                    @memset(elems, .none);
                    var offset: u64 = 0;
                    for (0..@intCast(field_count)) |field_index| {
                        const field_ty = ty.fieldType(field_index, ip);
                        const pad_bytes = ty.structFieldOffset(ip, field_index) - offset;
                        pack.padding(pad_bytes);
                        elems[field_index] = (try pack.get(field_ty)).index;
                        offset += pad_bytes + field_ty.abiSize(ip);
                    }
                    pack.padding(ty.abiSize(ip) - offset);
                    // Any zero-bit fields are OPV or comptime fields; fill those now.
                    for (elems, 0..) |*elem, field_index| {
                        if (elem.* != .none) continue;
                        const val = (try ty.structFieldValueComptime(sema, field_index)).?;
                        elem.* = val.index;
                    }
                    return try sema.aggregateValue(ty, elems);
                },
                .@"packed" => {
                    const backing_int_val = try pack.primitive(ty.bitpackBackingInt(ip));
                    if (backing_int_val.isUndef(ip)) return try sema.undefValue(ty);
                    return try sema.bitpackValue(ty, backing_int_val);
                },
            },
            .@"union" => switch (ty.containerLayout(ip)) {
                .auto => unreachable, // ill-defined layout
                .@"extern" => {
                    const prev_unpacked = pack.unpacked;
                    const prev_byte_offset = pack.byte_offset;

                    const backing_ty: Type = .fromIndex(try ip.internArrayType(.{ .len = ty.abiSize(ip), .child = .u8_type }));

                    const backing_result: enum { undef, reinterpret_decl_ref } = backing: {
                        const backing_val = pack.get(backing_ty) catch |err| switch (err) {
                            error.ReinterpretDeclRef => break :backing .reinterpret_decl_ref,
                            else => |e| return e,
                        };
                        if (backing_val.isUndef(ip)) break :backing .undef;
                        return .fromIndex(try ip.internUnion(.{
                            .ty = ty.index,
                            .tag = .none,
                            .val = backing_val.index,
                        }));
                    };

                    const tag_ty = ty.unionTagTypeHypothetical(ip);
                    const field_count = ip.loadEnumType(tag_ty.index).field_names.len;
                    const field_order = try arena.alloc(u32, field_count);
                    for (field_order, 0..) |*f, i| f.* = @intCast(i);
                    const SizeSortCtx = struct {
                        ip: *const InternPool,
                        union_ty: Type,
                        fn lessThan(ctx: @This(), a_idx: u32, b_idx: u32) bool {
                            const a_ty = ctx.union_ty.fieldType(a_idx, ctx.ip);
                            const b_ty = ctx.union_ty.fieldType(b_idx, ctx.ip);
                            return a_ty.abiSize(ctx.ip) > b_ty.abiSize(ctx.ip);
                        }
                    };
                    std.mem.sortUnstable(u32, field_order, SizeSortCtx{ .ip = ip, .union_ty = ty }, SizeSortCtx.lessThan);

                    for (field_order) |field_index| {
                        pack.unpacked = prev_unpacked;
                        pack.byte_offset = prev_byte_offset;
                        const field_ty = ty.fieldType(field_index, ip);
                        const field_val = pack.get(field_ty) catch |err| switch (err) {
                            error.ReinterpretDeclRef => continue,
                            else => |e| return e,
                        };
                        if (field_val.isUndef(ip)) continue;
                        pack.padding(ty.abiSize(ip) - field_ty.abiSize(ip));
                        const tag_val = (try sema.enumValueFieldIndex(tag_ty.index, field_index)).?;
                        return .fromIndex(try ip.internUnion(.{ .ty = ty.index, .tag = tag_val.index, .val = field_val.index }));
                    }

                    switch (backing_result) {
                        .undef => return try sema.undefValue(ty),
                        .reinterpret_decl_ref => return error.ReinterpretDeclRef,
                    }
                },
                .@"packed" => {
                    const backing_int_val = try pack.primitive(ty.bitpackBackingInt(ip));
                    if (backing_int_val.isUndef(ip)) return try sema.undefValue(ty);
                    return try sema.bitpackValue(ty, backing_int_val);
                },
            },
            .@"enum" => {
                const tag_int_val = try pack.primitive(.fromIndex(ip.loadEnumType(ty.index).int_tag_type));
                if (tag_int_val.isUndef(ip)) return try sema.undefValue(ty);
                return .fromIndex(try ip.internEnumTag(.{ .ty = ty.index, .int = tag_int_val.index }));
            },
            else => return pack.primitive(ty),
        }
    }

    fn padding(pack: *PackValueBytes, num_bytes: u64) void {
        _ = pack.prepareBytes(num_bytes);
    }

    fn primitive(pack: *PackValueBytes, want_ty: Type) (Sema.Error || error{ReinterpretDeclRef})!Value {
        const sema = pack.sema;
        const ip = sema.intern_pool;

        if (try want_ty.onePossibleValue(sema)) |opv| return opv;

        const vals, const byte_offset = pack.prepareBytes(want_ty.abiSize(ip));

        for (vals) |val| {
            if (!Value.fromIndex(val).isUndef(ip)) break;
        } else {
            return try sema.undefValue(want_ty);
        }

        if (vals.len == 1 and
            want_ty.isPtrAtRuntime(ip) and
            Value.fromIndex(vals[0]).typeOf(ip).isPtrAtRuntime(ip))
        {
            return .fromIndex(try ip.getCoerced(vals[0], want_ty.index));
        }

        // Reinterpret via an in-memory buffer.
        var buf_len: u64 = 0;
        for (vals) |ip_val| {
            buf_len += Value.fromIndex(ip_val).typeOf(ip).abiSize(ip);
        }

        const buf = try sema.arena.alloc(u8, @intCast(buf_len));
        {
            var offset: usize = 0;
            for (vals) |ip_val| {
                const val: Value = .fromIndex(ip_val);
                const ty = val.typeOf(ip);
                const size = ty.abiSize(ip);
                if (val.isUndef(ip)) {
                    @memset(buf[offset..][0..@intCast(size)], 0xAA);
                } else {
                    val.writeToMemory(ip, buf[offset..][0..@intCast(size)]) catch |err| switch (err) {
                        error.IllDefinedMemoryLayout => unreachable,
                        else => |e| return e,
                    };
                }
                offset += @intCast(size);
            }
        }
        const bytes = buf[@intCast(byte_offset)..];

        const endian = @import("builtin").target.cpu.arch.endian();
        switch (want_ty.zigTypeTag(ip)) {
            .bool => return .makeBool(bytes[0] != 0),
            .int => return try Value.readIntFromMemory(want_ty, ip, bytes, sema.arena),
            .float => switch (want_ty.floatBits()) {
                16 => return try sema.floatValue(want_ty, @as(f16, @bitCast(std.mem.readInt(u16, bytes[0..2], endian)))),
                32 => return try sema.floatValue(want_ty, @as(f32, @bitCast(std.mem.readInt(u32, bytes[0..4], endian)))),
                64 => return try sema.floatValue(want_ty, @as(f64, @bitCast(std.mem.readInt(u64, bytes[0..8], endian)))),
                80 => return try sema.floatValue(want_ty, @as(f80, @bitCast(std.mem.readInt(u80, bytes[0..10], endian)))),
                128 => return try sema.floatValue(want_ty, @as(f128, @bitCast(std.mem.readInt(u128, bytes[0..16], endian)))),
                else => unreachable,
            },
            .pointer => {
                assert(!want_ty.isSlice(ip));
                const ptr_addr = std.mem.readVarInt(u64, bytes[0..@intCast(want_ty.abiSize(ip))], endian);
                return try sema.ptrIntValue(want_ty, ptr_addr);
            },
            .optional => {
                assert(want_ty.isPtrLikeOptional(ip));
                const ptr_ty = want_ty.optionalChild(ip);
                const ptr_addr = std.mem.readVarInt(u64, bytes[0..@intCast(want_ty.abiSize(ip))], endian);
                return .fromIndex(try ip.internOpt(.{
                    .ty = want_ty.index,
                    .val = if (ptr_addr == 0) .none else (try sema.ptrIntValue(ptr_ty, ptr_addr)).index,
                }));
            },
            else => unreachable,
        }
    }

    fn prepareBytes(pack: *PackValueBytes, need_bytes: u64) struct { []const InternPool.Index, u64 } {
        if (need_bytes == 0) return .{ &.{}, 0 };
        const ip = pack.sema.intern_pool;

        var bytes: u64 = 0;
        var len: usize = 0;
        while (bytes < pack.byte_offset + need_bytes) {
            bytes += Value.fromIndex(pack.unpacked[len]).typeOf(ip).abiSize(ip);
            len += 1;
        }

        const result_vals = pack.unpacked[0..len];
        const result_offset = pack.byte_offset;

        const extra_bytes = bytes - pack.byte_offset - need_bytes;
        if (extra_bytes == 0) {
            pack.unpacked = pack.unpacked[len..];
            pack.byte_offset = 0;
        } else {
            pack.unpacked = pack.unpacked[len - 1 ..];
            pack.byte_offset = Value.fromIndex(pack.unpacked[0]).typeOf(ip).abiSize(ip) - extra_bytes;
        }

        return .{ result_vals, result_offset };
    }
};

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Sema = @import("Sema.zig");
const Type = @import("Type.zig");
const Value = @import("Value.zig");

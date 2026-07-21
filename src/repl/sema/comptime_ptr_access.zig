pub const ComptimeLoadResult = union(enum) {
    success: MutableValue,

    runtime_load,
    undef,
    err_payload: InternPool.NullTerminatedString,
    null_payload,
    inactive_union_field,
    needed_well_defined: Type,
    out_of_bounds: Type,
    exceeds_host_size,
};

pub fn loadComptimePtr(sema: *Sema, ptr: Value) !ComptimeLoadResult {
    const ip = sema.intern_pool;
    const ptr_info = ptr.typeOf(ip).ptrInfo(ip);
    const elem_ty: Type = .fromIndex(ptr_info.child);
    const host_size = ptr_info.packed_offset.host_size;

    if (host_size == 0) {
        return loadComptimePtrInner(sema, ptr, elem_ty, 0);
    }

    assert(elem_ty.hasBitRepresentation(ip));
    if (ptr_info.flags.vector_index == .none) {
        if (ptr_info.packed_offset.bit_offset + elem_ty.bitSize(ip) > host_size * 8) {
            return .exceeds_host_size;
        }
        const load_ty: Type = .fromIndex(try ip.internIntType(.unsigned, @intCast(host_size * 8)));
        const backing_int_mv = switch (try loadComptimePtrInner(sema, ptr, load_ty, 0)) {
            else => |result| return result,
            .success => |mv| mv,
        };
        const backing_int_val = try backing_int_mv.intern(ip, sema.arena);
        const buf = try sema.arena.alloc(u8, host_size);
        @memset(buf, 0);
        backing_int_val.writeToPackedMemory(ip, buf, 0);
        const result_val: Value = try .readFromPackedMemory(elem_ty, ip, buf, ptr_info.packed_offset.bit_offset);
        return .{ .success = .{ .interned = result_val.index } };
    }
    if (@intFromEnum(ptr_info.flags.vector_index) >= host_size) {
        return .exceeds_host_size;
    }
    const load_ty: Type = .fromIndex(try ip.internVectorType(.{
        .len = host_size,
        .child = elem_ty.index,
    }));
    const vector_mv = switch (try loadComptimePtrInner(sema, ptr, load_ty, 0)) {
        else => |result| return result,
        .success => |mv| mv,
    };
    const vector_val = try vector_mv.intern(ip, sema.arena);
    const result_val = try vector_val.elemValue(ip, @intFromEnum(ptr_info.flags.vector_index));
    return .{ .success = .{ .interned = result_val.index } };
}

pub const ComptimeStoreResult = union(enum) {
    success,

    runtime_store,
    comptime_field_mismatch: Value,
    undef,
    err_payload: InternPool.NullTerminatedString,
    null_payload,
    inactive_union_field,
    needed_well_defined: Type,
    out_of_bounds: Type,
    exceeds_host_size,
};

/// Perform a comptime store of value `store_val` to a pointer.
/// Asserts that the type of `store_val` equals the element type of the pointer type.
pub fn storeComptimePtr(
    sema: *Sema,
    ptr: Value,
    store_val: Value,
) !ComptimeStoreResult {
    const ip = sema.intern_pool;
    const ptr_info = ptr.typeOf(ip).ptrInfo(ip);
    const elem_ty: Type = .fromIndex(ptr_info.child);
    const host_size = ptr_info.packed_offset.host_size;
    assert(store_val.typeOf(ip).index == elem_ty.index);

    if (host_size == 0) {
        return storeComptimePtrInner(sema, ptr, store_val);
    }

    assert(elem_ty.hasBitRepresentation(ip));
    if (ptr_info.flags.vector_index == .none) {
        if (ptr_info.packed_offset.bit_offset + elem_ty.bitSize(ip) > host_size * 8) {
            return .exceeds_host_size;
        }
        const backing_ty: Type = .fromIndex(try ip.internIntType(.unsigned, @intCast(host_size * 8)));
        const backing_int_mv = switch (try loadComptimePtrInner(sema, ptr, backing_ty, 0)) {
            .success => |mv| mv,
            .runtime_load => return .runtime_store,
            inline else => |payload, tag| return @unionInit(ComptimeStoreResult, @tagName(tag), payload),
        };
        const old_backing_int_val = try backing_int_mv.intern(ip, sema.arena);
        const buf = try sema.arena.alloc(u8, host_size);
        @memset(buf, 0);
        old_backing_int_val.writeToPackedMemory(ip, buf, 0);
        store_val.writeToPackedMemory(ip, buf, ptr_info.packed_offset.bit_offset);
        const new_backing_int_val: Value = try .readFromPackedMemory(backing_ty, ip, buf, 0);
        return storeComptimePtrInner(sema, ptr, new_backing_int_val);
    }

    if (@intFromEnum(ptr_info.flags.vector_index) >= host_size) {
        return .exceeds_host_size;
    }
    const vec_ty: Type = .fromIndex(try ip.internVectorType(.{
        .len = host_size,
        .child = elem_ty.index,
    }));
    const vector_mv = switch (try loadComptimePtrInner(sema, ptr, vec_ty, 0)) {
        .success => |mv| mv,
        .runtime_load => return .runtime_store,
        inline else => |payload, tag| return @unionInit(ComptimeStoreResult, @tagName(tag), payload),
    };
    const old_vector_val = try vector_mv.intern(ip, sema.arena);
    const elems_buf = try sema.arena.alloc(InternPool.Index, host_size);
    for (elems_buf, 0..) |*elem, elem_index| {
        const elem_val = try old_vector_val.elemValue(ip, elem_index);
        elem.* = elem_val.index;
    }
    elems_buf[@intFromEnum(ptr_info.flags.vector_index)] = store_val.index;
    const new_vector_val = try sema.aggregateValue(vec_ty, elems_buf);
    return storeComptimePtrInner(sema, ptr, new_vector_val);
}

/// Like `storeComptimePtr`, except ignores the type of `ptr`, instead treating it as a single-item
/// pointer to `store_val.typeOf(ip)`.
fn storeComptimePtrInner(
    sema: *Sema,
    ptr: Value,
    store_val: Value,
) !ComptimeStoreResult {
    const ip = sema.intern_pool;
    const store_ty = store_val.typeOf(ip);

    if (store_ty.classify(ip) == .one_possible_value) {
        // zero-bit store; nothing to do
        return .success;
    }

    const strat = try prepareComptimePtrStore(sema, ptr, store_ty, 0);

    switch (strat) {
        .comptime_field => {
            // To "store" to a comptime field, just perform a load of the field
            // and see if the store value matches.
            const expected_mv = switch (try loadComptimePtr(sema, ptr)) {
                .success => |mv| mv,
                .runtime_load => unreachable, // this is a comptime field
                .exceeds_host_size => unreachable, // checked above
                .undef => return .undef,
                .err_payload => |err| return .{ .err_payload = err },
                .null_payload => return .null_payload,
                .inactive_union_field => return .inactive_union_field,
                .needed_well_defined => |ty| return .{ .needed_well_defined = ty },
                .out_of_bounds => |ty| return .{ .out_of_bounds = ty },
            };
            const expected = try expected_mv.intern(ip, sema.arena);
            if (store_val.index != expected.index) {
                return .{ .comptime_field_mismatch = expected };
            }
            return .success;
        },
        .runtime_store => return .runtime_store,
        .undef => return .undef,
        .err_payload => |err| return .{ .err_payload = err },
        .null_payload => return .null_payload,
        .inactive_union_field => return .inactive_union_field,
        .needed_well_defined => |ty| return .{ .needed_well_defined = ty },
        .out_of_bounds => |ty| return .{ .out_of_bounds = ty },

        .direct => |direct| {
            try checkComptimeVarStore(sema, direct.alloc);
            const want_ty = direct.val.typeOf(ip);
            const coerced_store_val = try ip.getCoerced(store_val.index, want_ty.index);
            direct.val.* = .{ .interned = coerced_store_val };
            return .success;
        },

        .index => |index| {
            try checkComptimeVarStore(sema, index.alloc);
            const want_ty = index.val.typeOf(ip).childType(ip);
            const coerced_store_val = try ip.getCoerced(store_val.index, want_ty.index);
            try index.val.setElem(ip, sema.arena, @intCast(index.elem_index), .{ .interned = coerced_store_val });
            return .success;
        },

        .flat_index => |flat| {
            try checkComptimeVarStore(sema, flat.alloc);
            const store_elems = store_val.typeOf(ip).arrayBase(ip)[1];
            const flat_elems = try sema.arena.alloc(InternPool.Index, @intCast(store_elems));
            {
                var next_idx: u64 = 0;
                var skip: u64 = 0;
                try flattenArray(sema, .{ .interned = store_val.index }, &skip, &next_idx, flat_elems);
            }
            for (flat_elems, 0..) |elem, idx| {
                var index: u64 = flat.flat_elem_index + idx;
                const val_ptr, const final_idx = (try recursiveIndex(sema, flat.val, &index)).?;
                try val_ptr.setElem(ip, sema.arena, @intCast(final_idx), .{ .interned = elem });
            }
            return .success;
        },

        .reinterpret => |reinterpret| {
            try checkComptimeVarStore(sema, reinterpret.alloc);
            if (!reinterpret.val.typeOf(ip).hasWellDefinedLayout(ip)) {
                return .{ .needed_well_defined = reinterpret.val.typeOf(ip) };
            }
            if (!store_ty.hasWellDefinedLayout(ip)) {
                return .{ .needed_well_defined = store_ty };
            }
            const old_val = try reinterpret.val.intern(ip, sema.arena);
            const new_val = try sema.spliceMemory(
                old_val,
                store_val,
                reinterpret.byte_offset,
            ) orelse return .runtime_store;
            reinterpret.val.* = .{ .interned = new_val.index };
            return .success;
        },
    }
}

/// Perform a comptime load of type `load_ty` from a pointer.
/// The pointer's type is ignored.
fn loadComptimePtrInner(
    sema: *Sema,
    ptr_val: Value,
    load_ty: Type,
    /// If `load_ty` is an array, this is the number of array elements to skip
    /// before `load_ty`. Otherwise, it is ignored and may be `undefined`.
    array_offset: u64,
) !ComptimeLoadResult {
    const ip = sema.intern_pool;

    const ptr = switch (ip.indexToKey(ptr_val.index)) {
        .undef => return .undef,
        .ptr => |ptr| ptr,
        else => unreachable,
    };

    const base_val: MutableValue = switch (ptr.base_addr) {
        .nav => |nav| .{ .interned = ip.getNav(nav).resolved.?.value },
        .uav => |uav| .{ .interned = uav.val },
        .comptime_alloc => |alloc_index| sema.getComptimeAlloc(alloc_index).val,
        .comptime_field => |val| .{ .interned = val },
        .int => return .runtime_load,
        .eu_payload => |base_ptr_ip| val: {
            const base_ptr: Value = .fromIndex(base_ptr_ip);
            const base_ty = base_ptr.typeOf(ip).childType(ip);
            switch (try loadComptimePtrInner(sema, base_ptr, base_ty, undefined)) {
                .success => |eu_val| switch (eu_val.unpackErrorUnion(ip)) {
                    .undef => return .undef,
                    .err => |err| return .{ .err_payload = err },
                    .payload => |payload| break :val payload,
                },
                else => |err| return err,
            }
        },
        .opt_payload => |base_ptr_ip| val: {
            const base_ptr: Value = .fromIndex(base_ptr_ip);
            const base_ty = base_ptr.typeOf(ip).childType(ip);
            switch (try loadComptimePtrInner(sema, base_ptr, base_ty, undefined)) {
                .success => |opt_val| switch (opt_val.unpackOptional(ip)) {
                    .undef => return .undef,
                    .null => return .null_payload,
                    .payload => |payload| break :val payload,
                },
                else => |err| return err,
            }
        },
        .arr_elem => |base_index| val: {
            const base_ptr: Value = .fromIndex(base_index.base);
            const base_ty = base_ptr.typeOf(ip).childType(ip);

            // We have a comptime-only array. This case is a little nasty.
            // To avoid loading too much data, we want to figure out how many elements we need.
            // If `load_ty` and the array share a base type, we'll load the correct number of elements.
            // Otherwise, we'll be reinterpreting (which we can't do, since it's comptime-only); just
            // load a single element and let the logic below emit its error.

            const load_one_ty, const load_count = load_ty.arrayBase(ip);
            const count = if (load_one_ty.index == base_ty.index) load_count else 1;

            const want_ty = try ip.internArrayType(.{
                .len = count,
                .child = base_ty.index,
            });

            switch (try loadComptimePtrInner(sema, base_ptr, .fromIndex(want_ty), base_index.index)) {
                .success => |arr_val| break :val arr_val,
                else => |err| return err,
            }
        },
        .field => |base_index| val: {
            const base_ptr: Value = .fromIndex(base_index.base);
            const base_ty = base_ptr.typeOf(ip).childType(ip);

            const agg_val = switch (try loadComptimePtrInner(sema, base_ptr, base_ty, undefined)) {
                .success => |val| val,
                else => |err| return err,
            };

            const agg_ty = agg_val.typeOf(ip);
            switch (agg_ty.zigTypeTag(ip)) {
                .@"struct", .pointer => break :val try agg_val.getElem(ip, @intCast(base_index.index)),
                .@"union" => {
                    const tag_val: Value, const payload_mv: MutableValue = switch (agg_val) {
                        .un => |un| .{ Value.fromIndex(un.tag), un.payload.* },
                        .interned => |ip_index| switch (ip.indexToKey(ip_index)) {
                            .undef => return .undef,
                            .un => |un| .{ Value.fromIndex(un.tag), .{ .interned = un.val } },
                            else => unreachable,
                        },
                        else => unreachable,
                    };
                    if ((try sema.enumTagFieldIndex(ip.indexToKey(tag_val.index).enum_tag.ty, tag_val)).? != base_index.index) {
                        return .inactive_union_field;
                    }
                    break :val payload_mv;
                },
                else => unreachable,
            }
        },
    };

    if (ptr.byte_offset == 0) {
        if (load_ty.zigTypeTag(ip) != .array or array_offset == 0) {
            if (.ok == try sema.coerceInMemoryAllowed(load_ty, base_val.typeOf(ip), false, null)) {
                // We already have a value which is IMC to the desired type.
                return .{ .success = base_val };
            }
        }
    }

    restructure_array: {
        // We might also be changing the length of an array, or restructuring it.
        const load_one_ty, const load_count = load_ty.arrayBase(ip);

        const extra_base_index: u64 = if (ptr.byte_offset == 0) 0 else idx: {
            if (load_one_ty.comptimeOnly(ip)) break :restructure_array;
            const elem_len = load_one_ty.abiSize(ip);
            if (ptr.byte_offset % elem_len != 0) break :restructure_array;
            break :idx @divExact(ptr.byte_offset, elem_len);
        };

        const val_one_ty, const val_count = base_val.typeOf(ip).arrayBase(ip);
        if (.ok == try sema.coerceInMemoryAllowed(load_one_ty, val_one_ty, false, null)) {
            // Changing the length of an array.
            const skip_base: u64 = extra_base_index + if (load_ty.zigTypeTag(ip) == .array) skip: {
                break :skip load_ty.childType(ip).arrayBase(ip)[1] * array_offset;
            } else 0;
            if (skip_base + load_count > val_count) return .{ .out_of_bounds = base_val.typeOf(ip) };
            const elems = try sema.arena.alloc(InternPool.Index, @intCast(load_count));
            var skip: u64 = skip_base;
            var next_idx: u64 = 0;
            try flattenArray(sema, base_val, &skip, &next_idx, elems);
            next_idx = 0;
            const val = try unflattenArray(sema, load_ty, elems, &next_idx);
            return .{ .success = .{ .interned = val.index } };
        }
    }

    // We need to reinterpret memory.
    if (!load_ty.hasWellDefinedLayout(ip)) {
        return .{ .needed_well_defined = load_ty };
    }
    if (!base_val.typeOf(ip).hasWellDefinedLayout(ip)) {
        return .{ .needed_well_defined = base_val.typeOf(ip) };
    }

    var cur_val = base_val;
    var cur_offset = ptr.byte_offset;

    if (load_ty.zigTypeTag(ip) == .array and array_offset > 0) {
        cur_offset += load_ty.childType(ip).abiSize(ip) * array_offset;
    }

    const need_bytes = load_ty.abiSize(ip);

    if (cur_offset + need_bytes > cur_val.typeOf(ip).abiSize(ip)) {
        return .{ .out_of_bounds = cur_val.typeOf(ip) };
    }

    while (true) {
        const cur_ty = cur_val.typeOf(ip);
        switch (cur_ty.zigTypeTag(ip)) {
            .noreturn,
            .type,
            .comptime_int,
            .comptime_float,
            .null,
            .undefined,
            .enum_literal,
            .@"opaque",
            .spirv,
            .@"fn",
            .error_union,
            => unreachable, // ill-defined layout
            .int,
            .float,
            .bool,
            .void,
            .pointer,
            .error_set,
            .@"anyframe",
            .frame,
            .@"enum",
            .vector,
            => break, // terminal types (no sub-values)
            .optional => break, // this can only be a pointer-like optional so is terminal
            .array => {
                const elem_ty = cur_ty.childType(ip);
                const elem_size = elem_ty.abiSize(ip);
                const elem_idx = cur_offset / elem_size;
                const next_elem_off = elem_size * (elem_idx + 1);
                if (cur_offset + need_bytes <= next_elem_off) {
                    cur_val = try cur_val.getElem(ip, @intCast(elem_idx));
                    cur_offset -= elem_idx * elem_size;
                } else {
                    break;
                }
            },
            .@"struct" => switch (cur_ty.containerLayout(ip)) {
                .auto => unreachable, // ill-defined layout
                .@"packed" => break, // let the memory reinterpret logic handle this
                .@"extern" => for (0..try sema.structFieldCount(cur_ty.index)) |field_idx| {
                    const start_off = cur_ty.structFieldOffset(ip, field_idx);
                    const end_off = start_off + cur_ty.fieldType(field_idx, ip).abiSize(ip);
                    if (cur_offset >= start_off and cur_offset + need_bytes <= end_off) {
                        cur_val = try cur_val.getElem(ip, field_idx);
                        cur_offset -= start_off;
                        break;
                    }
                } else break, // pointer spans multiple fields
            },
            .@"union" => switch (cur_ty.containerLayout(ip)) {
                .auto => unreachable, // ill-defined layout
                .@"packed" => break, // let the memory reinterpret logic handle this
                .@"extern" => break, // handled by the memory reinterpret logic
            },
        }
    }

    // Fast path: check again if we're now at the type we want to load.
    if (cur_offset == 0 and cur_val.typeOf(ip).index == load_ty.index) {
        return .{ .success = cur_val };
    }

    // Otherwise, use the memory reinterpretation logic to pull out the bytes we need.
    const reinterpret_val = try cur_val.intern(ip, sema.arena);
    const result_val = try sema.castMemory(reinterpret_val, load_ty, cur_offset) orelse return .runtime_load;
    return .{ .success = .{ .interned = result_val.index } };
}

const ComptimeStoreStrategy = union(enum) {
    direct: struct {
        alloc: ComptimeAllocIndex,
        val: *MutableValue,
    },
    index: struct {
        alloc: ComptimeAllocIndex,
        val: *MutableValue,
        elem_index: u64,
    },
    flat_index: struct {
        alloc: ComptimeAllocIndex,
        val: *MutableValue,
        flat_elem_index: u64,
    },
    reinterpret: struct {
        alloc: ComptimeAllocIndex,
        val: *MutableValue,
        byte_offset: u64,
    },

    comptime_field,
    runtime_store,
    undef,
    err_payload: InternPool.NullTerminatedString,
    null_payload,
    inactive_union_field,
    needed_well_defined: Type,
    out_of_bounds: Type,

    fn alloc(strat: ComptimeStoreStrategy) ComptimeAllocIndex {
        return switch (strat) {
            inline .direct, .index, .flat_index, .reinterpret => |info| info.alloc,
            .comptime_field,
            .runtime_store,
            .undef,
            .err_payload,
            .null_payload,
            .inactive_union_field,
            .needed_well_defined,
            .out_of_bounds,
            => unreachable,
        };
    }
};

/// Decide the strategy we will use to perform a comptime store of type `store_ty` to a pointer.
/// The pointer's type is ignored.
fn prepareComptimePtrStore(
    sema: *Sema,
    ptr_val: Value,
    store_ty: Type,
    /// If `store_ty` is an array, this is the number of array elements to skip
    /// before `store_ty`. Otherwise, it is ignored and may be `undefined`.
    array_offset: u64,
) !ComptimeStoreStrategy {
    const ip = sema.intern_pool;

    const ptr = switch (ip.indexToKey(ptr_val.index)) {
        .undef => return .undef,
        .ptr => |ptr| ptr,
        else => unreachable,
    };

    // `base_strat` will not be an error case.
    const base_strat: ComptimeStoreStrategy = switch (ptr.base_addr) {
        .nav, .uav, .int => return .runtime_store,
        .comptime_field => return .comptime_field,
        .comptime_alloc => |alloc_index| .{ .direct = .{
            .alloc = alloc_index,
            .val = &sema.getComptimeAlloc(alloc_index).val,
        } },
        .eu_payload => |base_ptr_ip| base_val: {
            const base_ptr: Value = .fromIndex(base_ptr_ip);
            const base_ty = base_ptr.typeOf(ip).childType(ip);
            const eu_val_ptr, const alloc = switch (try prepareComptimePtrStore(sema, base_ptr, base_ty, undefined)) {
                .direct => |direct| .{ direct.val, direct.alloc },
                .index => |index| .{
                    try index.val.elem(ip, sema.arena, @intCast(index.elem_index)),
                    index.alloc,
                },
                .flat_index => unreachable, // base_ty is not an array
                .reinterpret => unreachable, // base_ty has ill-defined layout
                else => |err| return err,
            };
            try eu_val_ptr.unintern(ip, sema.arena, false, false);
            switch (eu_val_ptr.*) {
                .interned => |ip_index| switch (ip.indexToKey(ip_index)) {
                    .undef => return .undef,
                    .error_union => |eu| return .{ .err_payload = eu.val.err_name },
                    else => unreachable,
                },
                .eu_payload => |data| break :base_val .{ .direct = .{
                    .val = data.child,
                    .alloc = alloc,
                } },
                else => unreachable,
            }
        },
        .opt_payload => |base_ptr_ip| base_val: {
            const base_ptr: Value = .fromIndex(base_ptr_ip);
            const base_ty = base_ptr.typeOf(ip).childType(ip);
            const opt_val_ptr, const alloc = switch (try prepareComptimePtrStore(sema, base_ptr, base_ty, undefined)) {
                .direct => |direct| .{ direct.val, direct.alloc },
                .index => |index| .{
                    try index.val.elem(ip, sema.arena, @intCast(index.elem_index)),
                    index.alloc,
                },
                .flat_index => unreachable, // base_ty is not an array
                .reinterpret => unreachable, // base_ty has ill-defined layout
                else => |err| return err,
            };
            try opt_val_ptr.unintern(ip, sema.arena, false, false);
            switch (opt_val_ptr.*) {
                .interned => |ip_index| switch (ip.indexToKey(ip_index)) {
                    .undef => return .undef,
                    .opt => return .null_payload,
                    else => unreachable,
                },
                .opt_payload => |data| break :base_val .{ .direct = .{
                    .val = data.child,
                    .alloc = alloc,
                } },
                else => unreachable,
            }
        },
        .arr_elem => |base_index| base_val: {
            const base_ptr: Value = .fromIndex(base_index.base);
            const base_ty = base_ptr.typeOf(ip).childType(ip);

            // We have a comptime-only array. This case is a little nasty.
            // To avoid messing with too much data, we want to figure out how many elements we need to store.
            // If `store_ty` and the array share a base type, we'll store the correct number of elements.
            // Otherwise, we'll be reinterpreting (which we can't do, since it's comptime-only); just
            // load a single element and let the logic below emit its error.

            const store_one_ty, const store_count = store_ty.arrayBase(ip);
            const count = if (store_one_ty.index == base_ty.index) store_count else 1;

            const want_ty = try ip.internArrayType(.{
                .len = count,
                .child = base_ty.index,
            });

            const result = try prepareComptimePtrStore(sema, base_ptr, .fromIndex(want_ty), base_index.index);
            switch (result) {
                .direct, .index, .flat_index => break :base_val result,
                .reinterpret => unreachable, // comptime-only array so ill-defined layout
                else => |err| return err,
            }
        },
        .field => |base_index| strat: {
            const base_ptr: Value = .fromIndex(base_index.base);
            const base_ty = base_ptr.typeOf(ip).childType(ip);

            const agg_val, const alloc = switch (try prepareComptimePtrStore(sema, base_ptr, base_ty, undefined)) {
                .direct => |direct| .{ direct.val, direct.alloc },
                .index => |index| .{
                    try index.val.elem(ip, sema.arena, @intCast(index.elem_index)),
                    index.alloc,
                },
                .flat_index => unreachable, // base_ty is not an array
                .reinterpret => unreachable, // base_ty has ill-defined layout
                else => |err| return err,
            };

            const agg_ty = agg_val.typeOf(ip);
            switch (agg_ty.zigTypeTag(ip)) {
                .@"struct", .pointer => break :strat .{ .direct = .{
                    .val = try agg_val.elem(ip, sema.arena, @intCast(base_index.index)),
                    .alloc = alloc,
                } },
                .@"union" => {
                    if (agg_val.* == .interned and Value.fromIndex(agg_val.interned).isUndef(ip)) {
                        return .undef;
                    }
                    try agg_val.unintern(ip, sema.arena, false, false);
                    const un = agg_val.un;
                    if ((try sema.enumTagFieldIndex(ip.indexToKey(un.tag).enum_tag.ty, .fromIndex(un.tag))).? != base_index.index) {
                        return .inactive_union_field;
                    }
                    break :strat .{ .direct = .{
                        .val = un.payload,
                        .alloc = alloc,
                    } };
                },
                else => unreachable,
            }
        },
    };

    if (ptr.byte_offset == 0) {
        if (store_ty.zigTypeTag(ip) != .array or array_offset == 0) direct: {
            const base_val_ty = switch (base_strat) {
                .direct => |direct| direct.val.typeOf(ip),
                .index => |index| index.val.typeOf(ip).childType(ip),
                .flat_index, .reinterpret => break :direct,
                else => unreachable,
            };
            if (.ok == try sema.coerceInMemoryAllowed(base_val_ty, store_ty, true, null)) {
                // The base strategy already gets us a value which the desired type is IMC to.
                return base_strat;
            }
        }
    }

    restructure_array: {
        const store_one_ty, const store_count = store_ty.arrayBase(ip);
        const extra_base_index: u64 = if (ptr.byte_offset == 0) 0 else idx: {
            if (store_one_ty.comptimeOnly(ip)) break :restructure_array;
            const elem_len = store_one_ty.abiSize(ip);
            if (ptr.byte_offset % elem_len != 0) break :restructure_array;
            break :idx @divExact(ptr.byte_offset, elem_len);
        };

        const base_val, const base_elem_offset, const oob_ty = switch (base_strat) {
            .direct => |direct| .{ direct.val, 0, direct.val.typeOf(ip) },
            .index => |index| restructure_info: {
                const elem_ty = index.val.typeOf(ip).childType(ip);
                const elem_off = elem_ty.arrayBase(ip)[1] * index.elem_index;
                break :restructure_info .{ index.val, elem_off, elem_ty };
            },
            .flat_index => |flat| .{ flat.val, flat.flat_elem_index, flat.val.typeOf(ip) },
            .reinterpret => break :restructure_array,
            else => unreachable,
        };
        const val_one_ty, const val_count = base_val.typeOf(ip).arrayBase(ip);
        if (.ok != try sema.coerceInMemoryAllowed(val_one_ty, store_one_ty, true, null)) {
            break :restructure_array;
        }
        if (base_elem_offset + extra_base_index + store_count > val_count) return .{ .out_of_bounds = oob_ty };

        if (store_ty.zigTypeTag(ip) == .array) {
            const skip = store_ty.childType(ip).arrayBase(ip)[1] * array_offset;
            return .{ .flat_index = .{
                .alloc = base_strat.alloc(),
                .val = base_val,
                .flat_elem_index = skip + base_elem_offset + extra_base_index,
            } };
        }

        // `base_val` must be an array, since otherwise the "direct reinterpret" logic above noticed it.
        assert(base_val.typeOf(ip).zigTypeTag(ip) == .array);

        var index: u64 = base_elem_offset + extra_base_index;
        const arr_val, const arr_index = (try recursiveIndex(sema, base_val, &index)).?;
        return .{ .index = .{
            .alloc = base_strat.alloc(),
            .val = arr_val,
            .elem_index = arr_index,
        } };
    }

    // We need to reinterpret memory.
    if (!store_ty.hasWellDefinedLayout(ip)) {
        return .{ .needed_well_defined = store_ty };
    }

    var cur_val: *MutableValue, var cur_offset: u64 = switch (base_strat) {
        .direct => |direct| .{ direct.val, 0 },
        .index => |index| .{ index.val, index.elem_index * index.val.typeOf(ip).childType(ip).abiSize(ip) },
        .flat_index => |flat_index| .{
            flat_index.val,
            flat_index.flat_elem_index * flat_index.val.typeOf(ip).arrayBase(ip)[0].abiSize(ip),
        },
        .reinterpret => |r| .{ r.val, r.byte_offset },
        else => unreachable,
    };
    cur_offset += ptr.byte_offset;

    if (!cur_val.typeOf(ip).hasWellDefinedLayout(ip)) {
        return .{ .needed_well_defined = cur_val.typeOf(ip) };
    }

    if (store_ty.zigTypeTag(ip) == .array and array_offset > 0) {
        cur_offset += store_ty.childType(ip).abiSize(ip) * array_offset;
    }

    const need_bytes = store_ty.abiSize(ip);

    if (cur_offset + need_bytes > cur_val.typeOf(ip).abiSize(ip)) {
        return .{ .out_of_bounds = cur_val.typeOf(ip) };
    }

    while (true) {
        const cur_ty = cur_val.typeOf(ip);
        switch (cur_ty.zigTypeTag(ip)) {
            .noreturn,
            .type,
            .comptime_int,
            .comptime_float,
            .null,
            .undefined,
            .enum_literal,
            .@"opaque",
            .spirv,
            .@"fn",
            .error_union,
            => unreachable, // ill-defined layout
            .int,
            .float,
            .bool,
            .void,
            .pointer,
            .error_set,
            .@"anyframe",
            .frame,
            .@"enum",
            .vector,
            => break, // terminal types (no sub-values)
            .optional => break, // this can only be a pointer-like optional so is terminal
            .array => {
                const elem_ty = cur_ty.childType(ip);
                const elem_size = elem_ty.abiSize(ip);
                const elem_idx = cur_offset / elem_size;
                const next_elem_off = elem_size * (elem_idx + 1);
                if (cur_offset + need_bytes <= next_elem_off) {
                    cur_val = try cur_val.elem(ip, sema.arena, @intCast(elem_idx));
                    cur_offset -= elem_idx * elem_size;
                } else {
                    break;
                }
            },
            .@"struct" => switch (cur_ty.containerLayout(ip)) {
                .auto => unreachable, // ill-defined layout
                .@"packed" => break, // let the memory reinterp logic handle this
                .@"extern" => for (0..try sema.structFieldCount(cur_ty.index)) |field_idx| {
                    const start_off = cur_ty.structFieldOffset(ip, field_idx);
                    const end_off = start_off + cur_ty.fieldType(field_idx, ip).abiSize(ip);
                    if (cur_offset >= start_off and cur_offset + need_bytes <= end_off) {
                        cur_val = try cur_val.elem(ip, sema.arena, field_idx);
                        cur_offset -= start_off;
                        break;
                    }
                } else break, // pointer spans multiple fields
            },
            .@"union" => switch (cur_ty.containerLayout(ip)) {
                .auto => unreachable, // ill-defined layout
                .@"packed" => break, // let the memory reinterp logic handle this
                .@"extern" => break, // let the memory reinterp logic handle this
            },
        }
    }

    // Fast path: check again if we're now at the type we want to store.
    if (cur_offset == 0 and cur_val.typeOf(ip).index == store_ty.index) {
        return .{ .direct = .{
            .alloc = base_strat.alloc(),
            .val = cur_val,
        } };
    }

    return .{ .reinterpret = .{
        .alloc = base_strat.alloc(),
        .val = cur_val,
        .byte_offset = cur_offset,
    } };
}

/// Given a potentially-nested array value, recursively flatten all of its elements into the given
/// output array. The result can be used by `unflattenArray` to restructure array values.
fn flattenArray(
    sema: *Sema,
    val: MutableValue,
    skip: *u64,
    next_idx: *u64,
    out: []InternPool.Index,
) Allocator.Error!void {
    if (next_idx.* == out.len) return;

    const ip = sema.intern_pool;

    const ty = val.typeOf(ip);
    const base_elem_count = ty.arrayBase(ip)[1];
    if (skip.* >= base_elem_count) {
        skip.* -= base_elem_count;
        return;
    }

    if (ty.zigTypeTag(ip) != .array) {
        out[@intCast(next_idx.*)] = (try val.intern(ip, sema.arena)).index;
        next_idx.* += 1;
        return;
    }

    const arr_base_elem_count = ty.childType(ip).arrayBase(ip)[1];
    for (0..@intCast(ty.arrayLen(ip))) |elem_idx| {
        if (next_idx.* == out.len) return;
        if (skip.* >= arr_base_elem_count) {
            skip.* -= arr_base_elem_count;
            continue;
        }
        try flattenArray(sema, try val.getElem(ip, elem_idx), skip, next_idx, out);
    }
    if (ty.sentinel(ip)) |s| {
        try flattenArray(sema, .{ .interned = s.index }, skip, next_idx, out);
    }
}

/// Given a sequence of non-array elements, "unflatten" them into the given array type.
fn unflattenArray(
    sema: *Sema,
    ty: Type,
    elems: []const InternPool.Index,
    next_idx: *u64,
) Sema.Error!Value {
    const ip = sema.intern_pool;
    const arena = sema.arena;

    if (ty.zigTypeTag(ip) != .array) {
        const val: Value = .fromIndex(elems[@intCast(next_idx.*)]);
        next_idx.* += 1;
        return .fromIndex(try ip.getCoerced(val.index, ty.index));
    }

    const elem_ty = ty.childType(ip);
    const buf = try arena.alloc(InternPool.Index, @intCast(ty.arrayLen(ip)));
    for (buf) |*elem| {
        elem.* = (try unflattenArray(sema, elem_ty, elems, next_idx)).index;
    }
    if (ty.sentinel(ip) != null) {
        _ = try unflattenArray(sema, elem_ty, elems, next_idx);
    }
    return sema.aggregateValue(ty, buf);
}

/// Given a `MutableValue` representing a potentially-nested array, treats `index` as an index into
/// the array's base type. The final level of array is not dereferenced.
fn recursiveIndex(
    sema: *Sema,
    mv: *MutableValue,
    index: *u64,
) !?struct { *MutableValue, u64 } {
    const ip = sema.intern_pool;

    const ty = mv.typeOf(ip);
    assert(ty.zigTypeTag(ip) == .array);

    const ty_base_elems = ty.arrayBase(ip)[1];
    if (index.* >= ty_base_elems) {
        index.* -= ty_base_elems;
        return null;
    }

    const elem_ty = ty.childType(ip);
    if (elem_ty.zigTypeTag(ip) != .array) {
        assert(index.* < ty.arrayLenIncludingSentinel(ip)); // should be handled by initial check
        return .{ mv, index.* };
    }

    for (0..@intCast(ty.arrayLenIncludingSentinel(ip))) |elem_index| {
        if (try recursiveIndex(sema, try mv.elem(ip, sema.arena, elem_index), index)) |result| {
            return result;
        }
    }
    unreachable; // should be handled by initial check
}

fn checkComptimeVarStore(sema: *Sema, alloc_index: ComptimeAllocIndex) !void {
    _ = sema;
    _ = alloc_index;
}

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const InternPool = @import("InternPool.zig");
const ComptimeAllocIndex = InternPool.Key.ComptimeAllocIndex;
const Sema = @import("Sema.zig");
const MutableValue = @import("MutableValue.zig").MutableValue;
const Type = @import("Type.zig");
const Value = @import("Value.zig");

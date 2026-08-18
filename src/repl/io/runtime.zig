//! The interpreter's runtime layer: what a compiled program lowers to machine instructions, performed
//! here directly against session state. Runtime-original -- no compiler function to mirror; where the
//! compiler emits AIR, `Sema` hands off here. Two kinds: runtime memory (retarget a mutable global's
//! pointer so the reused `comptime_ptr_access` navigation reaches it, `writeBack` persisting a store),
//! and runtime I/O (bind the intrinsic `Io` as `root.std_options_debug_io`, and perform the leaves a
//! compiled program would reach by syscall -- `__repl_write` out to the host, `__repl_now` reading the
//! host clock back in).

const std = @import("std");
const assert = std.debug.assert;
const Zir = std.zig.Zir;

const InternPool = @import("../sema/InternPool.zig");
pub const Sema = @import("../sema/Sema.zig");
const Session = @import("../Session.zig");
const Type = @import("../sema/Type.zig");
const Value = @import("../sema/Value.zig");

/// Standard streams occupy descriptors 0/1/2 (posix stdin/stdout/stderr); opened files are numbered
/// above them in the session's file table, so the two descriptor namespaces never alias.
const first_file_fd = 3;

/// Bind `root.std_options_debug_io` to the intrinsic `Io` as a hidden `pub_decls` Nav -- as if root
/// declared it, so nothing surfaces as a user binding or importable module. A no-op unless the session
/// both loads `std` and has an output sink; a failed impl eval is swallowed so print degrades to the
/// default `Io` at the print site rather than breaking every line.
pub fn install(sema: *Sema, impl_source: [:0]const u8) Sema.Error!void {
    assert(impl_source.len > 0);
    const session = sema.session orelse return;
    if (session.runtime.installed) return;
    if (session.module_source == null or session.runtime.io == null) return;
    session.runtime.installed = true;

    const ip = sema.intern_pool;
    const impl_ty = sema.lowerModule("std.options.debug_io", impl_source) catch return;
    const io_name = try ip.getOrPutString(sema.gpa, "io", .no_embedded_nulls);
    const io_val = (sema.containerDeclByName(impl_ty, io_name) catch return) orelse return;

    const name = try ip.getOrPutString(sema.gpa, "std_options_debug_io", .no_embedded_nulls);
    const nav = try ip.createNav(sema.gpa, name, name);
    ip.navPtr(nav).resolved = .{
        .type = io_val.typeOf(ip).toIndex(),
        .value = io_val.index,
        .@"align" = .none,
        .@"linksection" = .none,
        .@"addrspace" = .generic,
        .@"const" = true,
        .@"threadlocal" = false,
        .is_extern_decl = false,
    };
    try ip.namespacePtr(session.root_namespace).pub_decls.putContext(sema.gpa, nav, {}, .{ .pool = ip });
}

/// Perform a call whose callee is one of the runtime intrinsics the interpreter supplies for the leaves
/// a compiled program would reach by syscall -- what the intrinsic `Io`'s vtable slots call instead.
/// Null for any other extern, so the caller reports the usual non-function-callee error. Each intrinsic
/// is one direction of the runtime boundary: `__repl_write` reads bytes out of interpreter values to the
/// host; `__repl_now` reads host state (the clock) back in as a fresh interpreter value.
pub fn callIntrinsic(
    sema: *Sema,
    ext: InternPool.Key.Extern,
    explicit_len: u32,
    args_body: []const Zir.Inst.Index,
    inst: Zir.Inst.Index,
) Sema.Error!?Value {
    const ip = sema.intern_pool;
    const name = ip.getNav(ext.owner_nav).name;
    const param_types = ip.indexToKey(ext.ty).func_type.param_types;

    // The write leaf `__repl_write(fd: i64, ptr: [*]const u8, len: usize)` -- what the intrinsic `Io`'s
    // `operate(.file_write_streaming)` reaches instead of a syscall. `fd` names the stream (posix stdout
    // 1, stderr 2), so both flow to the right place.
    if (name.eqlSlice("__repl_write", ip)) {
        assert(param_types.len == 3);
        assert(explicit_len == 3);
        const fd = try resolveArg(sema, args_body, explicit_len, 0, param_types[0], inst);
        const ptr = try resolveArg(sema, args_body, explicit_len, 1, param_types[1], inst);
        const len = try resolveArg(sema, args_body, explicit_len, 2, param_types[2], inst);
        try write(sema, fd, ptr, len);
        return .{ .index = .void_value };
    }

    // The clock `__repl_now(clock: u32) i64` -- the leaf `Io.Clock.now` reaches. Returns the host
    // reading as a runtime `i64` interpreter value.
    if (name.eqlSlice("__repl_now", ip)) {
        assert(param_types.len == 1);
        assert(explicit_len == 1);
        const clock = try resolveArg(sema, args_body, explicit_len, 0, param_types[0], inst);
        return try now(sema, clock);
    }

    // The open leaf `__repl_open(path_ptr: [*]const u8, path_len: usize) i64` -- what the intrinsic
    // `Io`'s `dirOpenFile` reaches. Opens the host file and returns its handle-table index (or -1).
    if (name.eqlSlice("__repl_open", ip)) {
        assert(param_types.len == 2);
        assert(explicit_len == 2);
        const ptr = try resolveArg(sema, args_body, explicit_len, 0, param_types[0], inst);
        const len = try resolveArg(sema, args_body, explicit_len, 1, param_types[1], inst);
        return try open(sema, ptr, len);
    }

    // The read leaf `__repl_read(fd: i64, ptr: [*]u8, len: usize) i64` -- what `operate(.file_read_
    // streaming)` reaches. Reads host bytes into the interpreter buffer and returns the count (0 at EOF,
    // -1 on failure).
    if (name.eqlSlice("__repl_read", ip)) {
        assert(param_types.len == 3);
        assert(explicit_len == 3);
        const fd = try resolveArg(sema, args_body, explicit_len, 0, param_types[0], inst);
        const ptr = try resolveArg(sema, args_body, explicit_len, 1, param_types[1], inst);
        const len = try resolveArg(sema, args_body, explicit_len, 2, param_types[2], inst);
        return try read(sema, fd, ptr, len);
    }

    // The close leaf `__repl_close(fd: i64) void` -- what the intrinsic `Io`'s `fileClose` reaches. Ends
    // the host file's lifetime and frees its descriptor for reuse.
    if (name.eqlSlice("__repl_close", ip)) {
        assert(param_types.len == 1);
        assert(explicit_len == 1);
        const fd = try resolveArg(sema, args_body, explicit_len, 0, param_types[0], inst);
        return try close(sema, fd);
    }

    return null;
}

fn i64Value(ip: *InternPool, n: i64) Sema.Error!Value {
    return .{ .index = try ip.internInt(.{ .ty = .i64_type, .storage = .{ .i64 = n } }), .is_comptime = false };
}

/// Open the host file `__repl_open(path, ...)` names, returning its index in the session handle table
/// as a runtime `i64` -- the descriptor the interpreter `File` carries. Negative on any failure, so the
/// intrinsic `dirOpenFile` maps it to an error.
fn open(sema: *Sema, ptr: Value, len_val: Value) Sema.Error!Value {
    const ip = sema.intern_pool;
    const session = sema.session orelse return i64Value(ip, -1);
    const host = session.runtime.io orelse return i64Value(ip, -1);
    const path = (try readBytes(sema, ptr, len_val)) orelse return i64Value(ip, -1);
    defer sema.gpa.free(path);
    const file = (hostOpen(host, path)) orelse return i64Value(ip, -1);

    // Reuse the lowest freed descriptor before growing the table, the way a kernel hands back the
    // lowest unused fd; a closed slot is left null by `close`.
    const files = &session.runtime.open_files;
    for (files.items, 0..) |slot, i| {
        if (slot != null) continue;
        files.items[i] = file;
        return i64Value(ip, @intCast(first_file_fd + i));
    }
    const index = files.items.len;
    files.append(sema.gpa, file) catch {
        file.close(host);
        return i64Value(ip, -1);
    };
    return i64Value(ip, @intCast(first_file_fd + index));
}

/// Close the open file at descriptor `fd` and free its table slot, so the descriptor is available to a
/// later `open`. A standard-stream or already-free descriptor is a no-op (its lifetime is not the
/// session's to end).
fn close(sema: *Sema, fd_val: Value) Sema.Error!Value {
    const ip = sema.intern_pool;
    const session = sema.session orelse return .{ .index = .void_value };
    const host = session.runtime.io orelse return .{ .index = .void_value };
    const fd = intOf(ip, fd_val.index) orelse return .{ .index = .void_value };
    if (fd < first_file_fd) return .{ .index = .void_value };
    const descriptor = fd - first_file_fd;
    if (descriptor >= session.runtime.open_files.items.len) return .{ .index = .void_value };
    const index: usize = @intCast(descriptor);
    if (session.runtime.open_files.items[index]) |file| {
        file.close(host);
        session.runtime.open_files.items[index] = null;
    }
    return .{ .index = .void_value };
}

/// Open `path` relative to the host cwd. `Dir.cwd()` references a posix constant absent on freestanding,
/// where there is no filesystem anyway; a comptime switch keeps that path out of the freestanding build.
fn hostOpen(host: std.Io, path: []const u8) ?std.Io.File {
    return switch (@import("builtin").target.os.tag) {
        .freestanding => null,
        else => std.Io.Dir.cwd().openFile(host, path, .{}) catch null,
    };
}

/// Read from the open file at descriptor `fd` into the interpreter buffer `ptr` names, materializing the
/// host bytes as interpreter values -- the read-in direction, the reverse of `write`. Returns the count
/// (0 at EOF, -1 on failure).
fn read(sema: *Sema, fd_val: Value, buf_ptr: Value, len_val: Value) Sema.Error!Value {
    const ip = sema.intern_pool;
    const session = sema.session orelse return i64Value(ip, -1);
    const host = session.runtime.io orelse return i64Value(ip, -1);
    const file = hostFile(session, intOf(ip, fd_val.index) orelse return i64Value(ip, -1)) orelse return i64Value(ip, -1);
    const len: usize = @intCast(intOf(ip, len_val.index) orelse return i64Value(ip, -1));
    if (len == 0) return i64Value(ip, 0);

    const scratch = try sema.gpa.alloc(u8, len);
    defer sema.gpa.free(scratch);
    const n = file.readStreaming(host, &.{scratch}) catch |err| switch (err) {
        error.EndOfStream => return i64Value(ip, 0),
        else => return i64Value(ip, -1),
    };

    // The buffer write-back: store each host byte into the interpreter buffer through the reused store
    // path, the mirror of `write` reading bytes out. The `[*]u8` buffer pointer is a `.ptr` over some
    // base; each element pointer is `*u8` at the same base advanced by the byte offset (`u8` is 1 byte).
    const buf_key = ip.indexToKey(buf_ptr.index).ptr;
    const u8_ptr_ty = try ip.internPtrType(info: {
        var info = buf_ptr.typeOf(ip).ptrInfo(ip);
        info.flags.size = .one;
        break :info info;
    });
    for (scratch[0..n], 0..) |byte, i| {
        const elem_ptr: Value = .{ .index = try ip.internPtr(.{
            .ty = u8_ptr_ty,
            .base_addr = buf_key.base_addr,
            .byte_offset = buf_key.byte_offset + i,
        }) };
        try sema.storePtrVal(elem_ptr, .{ .index = try ip.internInt(.{ .ty = .u8_type, .storage = .{ .u64 = byte } }) });
    }
    return i64Value(ip, @intCast(n));
}

/// Read the `len`-byte `[]const u8` at `ptr` into a freshly-allocated host buffer, or null when the
/// bytes are out of the reader's reach. Caller frees.
fn readBytes(sema: *Sema, ptr: Value, len_val: Value) Sema.Error!?[]u8 {
    const ip = sema.intern_pool;
    const len: usize = @intCast(intOf(ip, len_val.index) orelse return null);
    const buf = try sema.gpa.alloc(u8, len);
    errdefer sema.gpa.free(buf);
    if (len == 0) return buf;

    const backing = (try ptrBacking(sema, ptr.index)) orelse return null;
    if (ip.indexToKey(backing.array) != .aggregate) return null;
    const agg = ip.indexToKey(backing.array).aggregate;
    for (buf, 0..) |*b, i| {
        const v = intOf(ip, try ip.aggregateElementAt(agg, backing.start + i)) orelse return null;
        if (v > 255) return null;
        b.* = @intCast(v);
    }
    return buf;
}

/// The host clock reading `__repl_now(clock)` names, materialized as a runtime `i64` interpreter value
/// -- the read-back direction, host state becoming an interpreter Value. Zero when no host `Io` is
/// wired (a freestanding frontend), so the call stays total.
fn now(sema: *Sema, clock_val: Value) Sema.Error!Value {
    const ip = sema.intern_pool;
    const nanoseconds: i64 = ns: {
        const host = (sema.session orelse break :ns 0).runtime.io orelse break :ns 0;
        const clock_int = intOf(ip, clock_val.index) orelse break :ns 0;
        const clock: std.Io.Clock = @fromBackingInt(@intCast(@as(u8, @intCast(clock_int))));
        break :ns @intCast(host.vtable.now(host.userdata, clock).nanoseconds);
    };
    return .{ .index = try ip.internInt(.{ .ty = .i64_type, .storage = .{ .i64 = nanoseconds } }), .is_comptime = false };
}

/// Evaluate call argument `arg_index` from `args_body`, coerced to its parameter type. Argument bodies
/// follow the `explicit_len` leading end-offset words; body `i` runs from the previous argument's end
/// (or `explicit_len` for the first) to its own, mirroring the call-argument layout in `Sema.evalCall`.
fn resolveArg(sema: *Sema, args_body: []const Zir.Inst.Index, explicit_len: u32, arg_index: u32, param_ty: InternPool.Index, inst: Zir.Inst.Index) Sema.Error!Value {
    const start = if (arg_index == 0) explicit_len else @backingInt(args_body[arg_index - 1]);
    const end = @backingInt(args_body[arg_index]);
    try sema.inst_map.put(sema.gpa, inst, .{ .index = param_ty });
    const raw = try sema.resolveInlineBody(args_body[start..end], inst);
    return try sema.coerceValueToType(raw, param_ty);
}

/// Emit `len` bytes at the `[*]const u8` `ptr` names to the host `Io`, on the stream `fd` selects
/// (posix stdout 1, stderr 2). Drops the write when the bytes are out of the reader's reach or no host
/// Io is set.
fn write(sema: *Sema, fd_val: Value, ptr: Value, len_val: Value) Sema.Error!void {
    const ip = sema.intern_pool;
    const session = sema.session orelse return;
    const host = session.runtime.io orelse return;
    const file = hostFile(session, intOf(ip, fd_val.index) orelse return) orelse return;
    const buf = (try readBytes(sema, ptr, len_val)) orelse return;
    defer sema.gpa.free(buf);
    if (buf.len == 0) return;
    file.writeStreamingAll(host, buf) catch {};
}

/// The host `File` a descriptor names: 0/1/2 are the standard streams; higher descriptors index the
/// session's open-file table. Null for an out-of-range or already-closed opened-file descriptor, so a
/// read/write to it is dropped rather than crashing (using a stale descriptor is an error, not a bug).
fn hostFile(session: *Session, fd: u64) ?std.Io.File {
    if (fd < first_file_fd) return streamFile(fd);
    const descriptor = fd - first_file_fd;
    if (descriptor >= session.runtime.open_files.items.len) return null;
    return session.runtime.open_files.items[@intCast(descriptor)];
}

/// The `File` for a standard-stream descriptor (posix stdin 0 / stdout 1 / stderr 2), routed by the host
/// Io. On freestanding the handle type is `void` and the host Io (a `WriterIo`) ignores it, so a
/// void-handle file stands in; elsewhere the descriptor is the real one the host Io dispatches on.
fn streamFile(fd: u64) std.Io.File {
    return switch (@import("builtin").target.os.tag) {
        .freestanding => .{ .handle = {}, .flags = .{ .nonblocking = false } },
        else => .{ .handle = @intCast(fd), .flags = .{ .nonblocking = false } },
    };
}

const PtrBacking = struct {
    array: InternPool.Index,
    start: u64,
};

/// The backing aggregate and start element a `[*]const u8`/`[]const u8` points at, following the bases
/// the reader can reach. Mirrors the render module's `ptrBacking`, plus the `comptime_alloc` base a
/// runtime-mutated buffer (the intrinsic `Io`'s writer buffer) resolves to -- that one needs `sema` to
/// read the alloc's live value, so this takes `sema` rather than a bare pool.
fn ptrBacking(sema: *Sema, ptr_index: InternPool.Index) Sema.Error!?PtrBacking {
    const ip = sema.intern_pool;
    if (ip.indexToKey(ptr_index) != .ptr) return null;
    const p = ip.indexToKey(ptr_index).ptr;
    const inner: PtrBacking = switch (p.base_addr) {
        .uav => |u| .{ .array = u.val, .start = 0 },
        .nav => |nav| blk: {
            const r = ip.getNav(nav).resolved orelse return null;
            break :blk .{ .array = r.value, .start = 0 };
        },
        .comptime_alloc => |idx| blk: {
            const agg = try sema.getComptimeAlloc(idx).val.intern(ip, sema.arena);
            break :blk .{ .array = agg.index, .start = 0 };
        },
        .arr_elem => |ae| blk: {
            const base = (try ptrBacking(sema, ae.base)) orelse return null;
            break :blk .{ .array = base.array, .start = base.start + ae.index };
        },
        else => return null,
    };
    if (p.byte_offset == 0) return inner;
    if (ip.indexToKey(inner.array) != .aggregate) return null;
    const elem_ty = ip.childType(ip.indexToKey(inner.array).aggregate.ty);
    const elem_size = Type.fromIndex(elem_ty).abiSize(ip);
    if (elem_size == 0 or p.byte_offset % elem_size != 0) return null;
    return .{ .array = inner.array, .start = inner.start + @divExact(p.byte_offset, elem_size) };
}

fn intOf(ip: *const InternPool, index: InternPool.Index) ?u64 {
    const k = ip.indexToKey(index);
    if (k != .int) return null;
    return switch (k.int.storage) {
        .u64 => |v| v,
        .i64 => |v| if (v >= 0) @intCast(v) else null,
        else => null,
    };
}

/// Whether `nav` names an external symbol whose data lives in the linker, not the session store.
fn isExternData(ip: *const InternPool, nav: InternPool.Nav) bool {
    return nav.resolved.?.is_extern_decl and Type.fromIndex(nav.resolved.?.type).zigTypeTag(ip) != .@"fn";
}

/// The `Nav` a pointer chain roots at, or null if it roots elsewhere (an integer address, an anonymous
/// decl, an already-comptime alloc).
fn navRoot(ip: *const InternPool, ptr_index: InternPool.Index) ?InternPool.Nav.Index {
    return switch (ip.indexToKey(ptr_index).ptr.base_addr) {
        .nav => |nav_id| nav_id,
        .field, .arr_elem => |base| navRoot(ip, base.base),
        .opt_payload, .eu_payload => |base| navRoot(ip, base),
        else => null,
    };
}

/// Re-intern a nav-rooted pointer chain with its root swapped to `new_root`, preserving each level's
/// type and byte offset. Null for a chain this interpreter cannot yet re-root.
fn rebaseTo(
    sema: *Sema,
    ptr_index: InternPool.Index,
    nav_id: InternPool.Nav.Index,
    new_root: InternPool.Key.Ptr.BaseAddr,
) Sema.Error!?InternPool.Index {
    const ip = sema.intern_pool;
    const ptr = ip.indexToKey(ptr_index).ptr;
    const base_addr: InternPool.Key.Ptr.BaseAddr = switch (ptr.base_addr) {
        .nav => |id| if (id == nav_id) new_root else return null,
        inline .field, .arr_elem => |base, tag| ba: {
            const rebased = (try rebaseTo(sema, base.base, nav_id, new_root)) orelse return null;
            break :ba @unionInit(InternPool.Key.Ptr.BaseAddr, @tagName(tag), .{ .base = rebased, .index = base.index });
        },
        inline .opt_payload, .eu_payload => |base, tag| ba: {
            const rebased = (try rebaseTo(sema, base, nav_id, new_root)) orelse return null;
            break :ba @unionInit(InternPool.Key.Ptr.BaseAddr, @tagName(tag), rebased);
        },
        else => return null,
    };
    return try ip.internPtr(.{ .ty = ptr.ty, .base_addr = base_addr, .byte_offset = ptr.byte_offset });
}

/// Retarget a pointer for a runtime load onto a read-only view of the mutable global's current value.
/// Null when the interpreter cannot perform the load, so the caller reports it. A load only reads, so
/// no alloc is needed.
pub fn retargetLoad(sema: *Sema, ptr: Value) Sema.Error!?Value {
    const ip = sema.intern_pool;
    const nav_id = navRoot(ip, ptr.index) orelse return null;
    const nav = ip.getNav(nav_id);
    if (isExternData(ip, nav)) return null;
    const root: InternPool.Key.Ptr.BaseAddr = .{ .uav = .{ .val = nav.resolved.?.value, .orig_ty = nav.resolved.?.type } };
    const rooted = (try rebaseTo(sema, ptr.index, nav_id, root)) orelse return null;
    return .{ .index = rooted };
}

/// A mutable global backed by a temporary comptime alloc for a runtime store: after the reused comptime
/// store mutates the alloc, `writeBack` persists it.
pub const StoreTarget = struct {
    ptr: Value,
    nav_id: InternPool.Nav.Index,
    alloc_index: InternPool.Key.ComptimeAllocIndex,
};

/// Retarget a pointer for a runtime store: back the mutable global with a temporary comptime alloc and
/// re-root the chain at it. Null when the interpreter cannot perform the store.
pub fn retargetStore(sema: *Sema, ptr: Value) Sema.Error!?StoreTarget {
    const ip = sema.intern_pool;
    const nav_id = navRoot(ip, ptr.index) orelse return null;
    const nav = ip.getNav(nav_id);
    if (isExternData(ip, nav)) return null;
    const alloc_ptr = try sema.pushComptimeAlloc(nav.resolved.?.type, .{ .index = nav.resolved.?.value }, false, .none);
    const alloc_index = ip.indexToKey(alloc_ptr.index).ptr.base_addr.comptime_alloc;
    const rooted = (try rebaseTo(sema, ptr.index, nav_id, .{ .comptime_alloc = alloc_index })) orelse return null;
    return .{ .ptr = .{ .index = rooted }, .nav_id = nav_id, .alloc_index = alloc_index };
}

/// Persist an alloc-backed store into the mutable global's slot, after a successful store.
pub fn writeBack(sema: *Sema, target: StoreTarget) Sema.Error!void {
    const ip = sema.intern_pool;
    const new_value = try sema.getComptimeAlloc(target.alloc_index).val.intern(ip, sema.arena);
    ip.navPtr(target.nav_id).resolved.?.value = new_value.index;
}

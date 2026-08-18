//! Writes a Sema-produced Value to a writer in REPL display form.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("../sema/InternPool.zig");
const Value = @import("../sema/Value.zig");
const Type = @import("../sema/Type.zig");
const Session = @import("../Session.zig");

/// Error union for renderers: `Writer.Error` for the I/O path, plus
/// `Allocator.Error` because the type-name path (`Type.print`) allocates to
/// sort `error{...}` member names.
pub const Error = std.Io.Writer.Error || std.mem.Allocator.Error;

/// A `{f}`-formattable wrapper for a value, the `Value` analogue of
/// `Type.Formatter`: `render` needs the `InternPool`, which a bare
/// `format(self, writer)` cannot take. Lets diagnostics write `"value '{f}'"` with
/// `value.fmt(ip)`. OOM while rendering degrades to `<value>` (a diagnostic is
/// best-effort and `format` yields only `Writer.Error`).
pub const Formatter = struct {
    value: Value,
    pool: *InternPool,
    pub fn format(self: Formatter, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        render(self.value, self.pool, null, writer) catch |err| switch (err) {
            error.WriteFailed => return error.WriteFailed,
            else => try writer.writeAll("<value>"),
        };
    }
};

pub fn fmt(value: Value, pool: *InternPool) Formatter {
    return .{ .value = value, .pool = pool };
}

/// Writes a value to `writer` with no trailing newline: a REPL result line
/// appends its own terminator at the print site; diagnostics embed the value
/// mid-message.
pub fn render(
    value: Value,
    pool: *InternPool,
    session: ?*const Session,
    writer: *std.Io.Writer,
) Error!void {
    assert(value.index != .none);

    const key = pool.indexToKey(value.index);
    return switch (key) {
        .int => |iv| {
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const big = iv.storage.toBigInt(&space);
            return writer.print("{f}", .{big});
        },
        .float => |fv| renderFloat(fv, writer),
        .simple_value => |sv| writer.writeAll(simpleValueText(sv)),
        .undef => writer.writeAll("undefined"),
        .opt => |o| if (o.val == .none)
            writer.writeAll("null")
        else
            render(.{ .index = o.val }, pool, session, writer),
        // A single-item pointer to a `[N]u8` const ref is a string literal
        // (`&"..."`): show the pointee bytes as a string, not the raw address.
        // Mirrors src/print_value.zig printPtr's `.uav` aggregate shortcut.
        .ptr => |p| {
            if (p.base_addr == .uav) {
                const pointee = pool.indexToKey(p.base_addr.uav.val);
                if (pointee == .aggregate)
                    if (try renderBytes(pool, writer, pointee.aggregate, .ref)) return;
            }
            // `{any}` renders a single-item pointer to an array/vector as the `[]const T` it points
            // at (Writer.printValue's `.one` -> `@as([]const child, value)`), so show the pointee.
            const pty = pool.indexToKey(p.ty);
            if (pty == .ptr_type and pty.ptr_type.flags.size == .one) {
                switch (pool.indexToKey(pty.ptr_type.child)) {
                    .array_type => |at| if (try renderIndexable(pool, session, writer, value.index, at.child, at.len)) return,
                    .vector_type => |vt| if (try renderIndexable(pool, session, writer, value.index, vt.child, vt.len)) return,
                    else => {},
                }
            }
            return writer.print("ptr@{d}+{d}", .{ @backingInt(p.ty), p.byte_offset });
        },
        .slice => |s| {
            const child = pool.indexToKey(s.ty).ptr_type.child;
            const len = intOf(pool, s.len) orelse -1;
            if (len >= 0 and try renderIndexable(pool, session, writer, s.ptr, child, @intCast(len))) return;
            // Otherwise the elements live behind the slice's `ptr` in a Sema
            // comptime alloc the renderer cannot reach, so render just the length.
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const slice_len = pool.indexToKey(s.len).int.storage.toBigInt(&space);
            return writer.print("slice[{f}]", .{slice_len});
        },
        .err => |e| writer.print("error.{s}", .{pool.stringSlice(e.name)}),
        .error_union => |eu| renderErrorUnion(eu, pool, session, writer),
        .func => |f| writer.print("fn@{d}", .{@backingInt(f.zir_body_inst)}),
        .@"extern" => |e| writer.print("(extern '{s}')", .{pool.stringSlice(pool.getNav(e.owner_nav).name)}),
        .aggregate => |agg| renderAggregate(agg, pool, session, writer),
        .enum_literal => |enum_literal| writer.print(".{f}", .{enum_literal.fmt(pool)}),
        .enum_tag => |et| renderEnumTag(et, pool, session, writer),
        .un => |uv| renderUnion(uv, pool, session, writer),
        // A bare type Key viewed as a value identifies the type itself
        // (Sema's value-of-type-type convention; see Value.typeOf). The
        // value Keys above are exhaustive, so the assert turns a future
        // unclassified one into a crash rather than a mis-render as a type.
        .bitpack => |bp| renderBitpack(bp, pool, session, writer),
        else => blk: {
            assert(key.isType());
            break :blk renderTypeRef(value.index, pool, writer);
        },
    };
}

/// Render an aggregate. A struct with a `session` to read its field names prints
/// shaped -- `.{ .field = val, ... }`; a tuple `.{ v0, v1, ... }`; an array or
/// vector, or a struct with no name source, positionally `{ v0, v1, ... }`.
fn renderAggregate(
    agg: InternPool.Key.Aggregate,
    pool: *InternPool,
    session: ?*const Session,
    writer: *std.Io.Writer,
) Error!void {
    // A by-value `[N]u8` array prints as a string (`"...".*`), like any bytes ref.
    if (try renderBytes(pool, writer, agg, .value)) return;
    const ty_key = pool.indexToKey(agg.ty);
    const shaped = ty_key == .struct_type and session != null;
    // A struct (named or anonymous) and a tuple both print `.{ ... }` -- matching `{any}` and
    // the compiler's `printAggregate`, which never prefix a type name; a struct additionally
    // shows field names. Arrays and vectors print positionally `{ ... }`.
    if (shaped or ty_key == .tuple_type) try writer.writeByte('.');
    try writer.writeAll("{ ");
    // Arrays and vectors display their declared length, which excludes the
    // sentinel slot the aggregate stores (`printAggregate` iterates `arrayLen`, not
    // `arrayLenIncludingSentinel`). Structs/tuples carry no such count in the type,
    // so fall back to the storage length (`.repeated_elem` reads it from the type).
    const count: u64 = switch (ty_key) {
        .array_type => |at| at.len,
        .vector_type => |vt| vt.len,
        else => switch (agg.storage) {
            .elems => |es| es.len,
            .bytes, .repeated_elem => pool.aggregateElementCount(agg.ty),
        },
    };
    var i: u64 = 0;
    while (i < count) : (i += 1) {
        if (i > 0) try writer.writeAll(", ");
        if (shaped) {
            if (structFieldName(pool, session.?, agg.ty, @intCast(i))) |name|
                try writer.print(".{s} = ", .{name});
        }
        try render(.{ .index = try pool.aggregateElementAt(agg, i) }, pool, session, writer);
    }
    try writer.writeAll(" }");
}

/// The name of struct field `index` -- stored for a reified struct, read from the
/// declaring ZIR for a declared one (whose fields are resolved lazily). Null if
/// unavailable. The read-only analogue of `Sema.structFieldNameAt`.
fn structFieldName(pool: *const InternPool, session: *const Session, struct_ty: InternPool.Index, index: u32) ?[]const u8 {
    const d = switch (pool.indexToKey(struct_ty).struct_type) {
        .reified => {
            const f = pool.loadStructType(struct_ty);
            return if (index < f.field_names.len) pool.stringSlice(f.field_names[index]) else null;
        },
        .declared => |dd| dd,
        .generated_union_tag => return null,
    };
    if (d.source_zir_id >= session.files.items.len) return null;
    const zir = session.files.items[d.source_zir_id].zir orelse return null;
    var it = zir.getStructDecl(d.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (field.idx == index) return zir.nullTerminatedString(field.name);
    }
    return null;
}

/// The i128 value of an `int` Key, or null if `idx` is not an integer or overflows.
fn intOf(pool: *const InternPool, idx: InternPool.Index) ?i128 {
    const key = pool.indexToKey(idx);
    if (key != .int) return null;
    return switch (key.int.storage) {
        .u64 => |v| @intCast(v),
        .i64 => |v| @intCast(v),
        .big_int => |b| b.toInt(i128) catch null,
    };
}

/// The concrete byte of an interned element, or null if it is `undefined` or not
/// a `u8`-range integer -- either of which disqualifies a u8 array from string
/// form (the compiler's `.bytes` storage encodes neither; src/print_value.zig).
fn byteValue(pool: *const InternPool, elem: InternPool.Index) ?u8 {
    const v = intOf(pool, elem) orelse return null;
    if (v < 0 or v > 255) return null;
    return @intCast(v);
}

/// Whether an interned value is the `.ref` (pointer to the array) or `.value`
/// (the array itself) form of a bytes container -- the compiler's `is_ref`
/// distinction, which decides the trailing `.*` (src/print_value.zig
/// printAggregate).
const BytesForm = enum { ref, value };

/// Render aggregate `agg` as a quoted Zig string when it is a `[N]u8` array,
/// appending `.*` for the `.value` form. `.bytes` storage is the concrete byte
/// run and always qualifies; the element storage forms qualify only when every
/// element is a concrete `u8` (a single `undefined` element, which `.bytes`
/// cannot encode, falls back to the positional `{ ... }`). Returns false without
/// writing otherwise, so the caller renders positionally.
fn renderBytes(pool: *InternPool, writer: *std.Io.Writer, agg: InternPool.Key.Aggregate, form: BytesForm) Error!bool {
    const ty_key = pool.indexToKey(agg.ty);
    if (ty_key != .array_type or ty_key.array_type.child != .u8_type) return false;
    const count = ty_key.array_type.len;
    switch (agg.storage) {
        .bytes => |bytes| {
            try writer.writeByte('"');
            try std.zig.stringEscape(bytes.toSlice(count, pool), writer);
            try writer.writeByte('"');
        },
        .elems, .repeated_elem => {
            var i: u64 = 0;
            while (i < count) : (i += 1) {
                if (byteValue(pool, try pool.aggregateElementAt(agg, i)) == null) return false;
            }
            try writer.writeByte('"');
            i = 0;
            while (i < count) : (i += 1) {
                try std.zig.stringEscape(&.{byteValue(pool, try pool.aggregateElementAt(agg, i)).?}, writer);
            }
            try writer.writeByte('"');
        },
    }
    if (form == .value) try writer.writeAll(".*");
    return true;
}

/// The backing array and start element for a pointer when it names a const value the read-only
/// renderer can follow: a `.uav` or `.nav` (the whole value) or an `.arr_elem` into one (the
/// `arr[0..]`/`arr[a..b]` shape). Null for `comptime_alloc`/`field` bases, whose storage lives in
/// Sema out of the renderer's reach.
const PtrBacking = struct { array: InternPool.Index, start: u64 };
fn ptrBacking(pool: *const InternPool, ptr_index: InternPool.Index) ?PtrBacking {
    if (pool.indexToKey(ptr_index) != .ptr) return null;
    const p = pool.indexToKey(ptr_index).ptr;
    const inner: PtrBacking = switch (p.base_addr) {
        .uav => |u| .{ .array = u.val, .start = 0 },
        .nav => |nav| blk: {
            const r = pool.getNav(nav).resolved orelse return null;
            break :blk .{ .array = r.value, .start = 0 };
        },
        .arr_elem => |ae| blk: {
            const base = ptrBacking(pool, ae.base) orelse return null;
            break :blk .{ .array = base.array, .start = base.start + ae.index };
        },
        else => return null,
    };
    if (p.byte_offset == 0) return inner;
    if (pool.indexToKey(inner.array) != .aggregate) return null;
    const elem_ty = pool.childType(pool.indexToKey(inner.array).aggregate.ty);
    const elem_size = Type.fromIndex(elem_ty).abiSize(pool);
    if (elem_size == 0) return null;
    return .{ .array = inner.array, .start = inner.start + p.byte_offset / elem_size };
}

/// Render the `len` elements a pointer indexes -- for both a slice's `ptr` and a single-item
/// pointer to an array (`{any}` treats `*[N]T` as `[]const T`). An all-concrete `u8` run renders
/// as a quoted string (the REPL's byte convention, like renderBytes); otherwise positionally
/// `{ v0, v1, ... }`. False (no output) when the backing is out of the renderer's reach, so the
/// caller falls back to the length placeholder / raw address.
fn renderIndexable(pool: *InternPool, session: ?*const Session, writer: *std.Io.Writer, ptr_index: InternPool.Index, child: InternPool.Index, len: u64) Error!bool {
    const backing = ptrBacking(pool, ptr_index) orelse return false;
    if (pool.indexToKey(backing.array) != .aggregate) return false;
    const agg = pool.indexToKey(backing.array).aggregate;
    const total: u64 = switch (agg.storage) {
        .elems => |es| es.len,
        .bytes => pool.aggregateElementCount(agg.ty),
        .repeated_elem => std.math.maxInt(u64),
    };
    if (backing.start + len > total) return false;

    if (child == .u8_type) bytes: {
        var i: u64 = 0;
        while (i < len) : (i += 1) {
            if (byteValue(pool, try pool.aggregateElementAt(agg, backing.start + i)) == null) break :bytes;
        }
        try writer.writeByte('"');
        i = 0;
        while (i < len) : (i += 1) {
            try std.zig.stringEscape(&.{byteValue(pool, try pool.aggregateElementAt(agg, backing.start + i)).?}, writer);
        }
        try writer.writeByte('"');
        return true;
    }

    try writer.writeAll("{ ");
    var i: u64 = 0;
    while (i < len) : (i += 1) {
        if (i > 0) try writer.writeAll(", ");
        try render(.{ .index = try pool.aggregateElementAt(agg, backing.start + i) }, pool, session, writer);
    }
    try writer.writeAll(" }");
    return true;
}

/// The field name an `enum_tag` selects, read from the enum's resolved fields (a value
/// of the enum having been produced means they are stored -- including a union's
/// generated tag enum, resolved when the union value was created). An auto enum indexes
/// by the tag; an explicit one matches the tag value. Null if not resolved.
fn enumTagName(pool: *const InternPool, enum_ty: InternPool.Index, int_idx: InternPool.Index) ?[]const u8 {
    const tag = intOf(pool, int_idx) orelse return null;
    const f = pool.loadEnumType(enum_ty);
    if (f.field_values.len == 0) return if (tag >= 0 and tag < f.field_names.len) pool.stringSlice(f.field_names[@intCast(tag)]) else null;
    for (f.field_values, 0..) |v, pos| {
        if (intOf(pool, v)) |vv| if (vv == tag) return pool.stringSlice(f.field_names[pos]);
    }
    return null;
}

/// `.tag` when the tag name resolves, else the underlying integer.
fn renderEnumTag(et: InternPool.Key.EnumTag, pool: *InternPool, session: ?*const Session, writer: *std.Io.Writer) Error!void {
    if (enumTagName(pool, et.ty, et.int)) |name| return writer.print(".{s}", .{name});
    return render(.{ .index = et.int }, pool, session, writer);
}

/// `.{ .field = payload }` when the active field name resolves, else the payload. The
/// field name comes from the tag value's enum -- for a generated tag enum, its fields
/// were resolved when this union value was created (mirrors the compiler printing the
/// tag value in `src/print_value.zig`).
fn renderUnion(uv: InternPool.Key.Union, pool: *InternPool, session: ?*const Session, writer: *std.Io.Writer) Error!void {
    const tag_key = pool.indexToKey(uv.tag);
    if (tag_key == .enum_tag) if (enumTagName(pool, tag_key.enum_tag.ty, tag_key.enum_tag.int)) |name| {
        try writer.print(".{{ .{s} = ", .{name});
        try render(.{ .index = uv.val }, pool, session, writer);
        return writer.writeAll(" }");
    };
    return render(.{ .index = uv.val }, pool, session, writer);
}

fn renderErrorUnion(
    eu: InternPool.Key.ErrorUnion,
    pool: *InternPool,
    session: ?*const Session,
    writer: *std.Io.Writer,
) Error!void {
    switch (eu.val) {
        .err_name => |name| try writer.print("error.{s}", .{pool.stringSlice(name)}),
        .payload => |idx| try render(.{ .index = idx }, pool, session, writer),
    }
}

/// A packed struct/union value is stored as its backing integer (`.bitpack`). Render it by unpacking the
/// bits: a struct shows its fields (`Name{ .a = .., .b = .. }`) like any aggregate; a union has no active
/// field to name, so it shows the backing bits as an explicit `@bitCast`, mirroring src/print_value.zig.
/// Unpacking interns each field value, which is why the renderer holds a mutable pool.
fn renderBitpack(bp: InternPool.Key.Bitpack, pool: *InternPool, session: ?*const Session, writer: *std.Io.Writer) Error!void {
    const ty: Type = .fromIndex(bp.ty);
    const backing_ty = ty.bitpackBackingInt(pool);
    const buf = try pool.gpa.alloc(u8, @intCast((backing_ty.bitSize(pool) + 7) / 8));
    defer pool.gpa.free(buf);
    @memset(buf, 0);
    Value.fromIndex(bp.backing_int_val).writeToPackedMemory(pool, buf, 0);

    switch (pool.indexToKey(bp.ty)) {
        .struct_type => {
            const field_types = pool.loadStructType(bp.ty).field_types;
            const elems = try pool.gpa.alloc(InternPool.Index, field_types.len);
            defer pool.gpa.free(elems);
            var bit_offset: usize = 0;
            for (field_types, elems) |field_ty, *elem| {
                elem.* = (try Value.readFromPackedMemory(.fromIndex(field_ty), pool, buf, bit_offset)).index;
                bit_offset += @intCast(Type.fromIndex(field_ty).bitSize(pool));
            }
            return renderAggregate(.{ .ty = bp.ty, .storage = .{ .elems = elems } }, pool, session, writer);
        },
        .union_type => {
            try writer.writeAll("@bitCast(@as(");
            try renderTypeRef(backing_ty.index, pool, writer);
            try writer.writeAll(", ");
            try render(.{ .index = bp.backing_int_val }, pool, session, writer);
            return writer.writeAll("))");
        },
        else => unreachable,
    }
}

fn simpleValueText(sv: InternPool.SimpleValue) []const u8 {
    return switch (sv) {
        .void => "void",
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
) Error!void {
    try Type.print(Type.fromIndex(type_index), pool, writer);
}

/// Print each float-storage variant in its native precision through
/// `std.fmt.float.render` -- the building block `{d}` routes through, but
/// invoked directly so wide types keep full precision rather than degrading
/// to the f64-sized buffer `std.fmt`'s float printer allocates. Full-precision
/// decimal output can be thousands of digits, so the buffer is sized for the
/// widest storage variant (see `std.fmt.float.bufferSize`).
///
/// Full-precision decimal strips the trailing decimal for integral values
/// (`4.0` -> "4"), which is ambiguous next to integers in REPL output.
/// We restore the `.0` when the printed form has no decimal exponent or
/// dot -- but leave NaN / inf / -inf untouched.
fn renderFloat(
    float: InternPool.Key.Float,
    writer: *std.Io.Writer,
) Error!void {
    // Mirrors the compiler's value printer (src/print_value.zig): floats render at f64 precision with
    // no synthetic trailing `.0`.
    switch (float.storage) {
        inline else => |v| try writer.print("{d}", .{@as(f64, @floatCast(v))}),
    }
}

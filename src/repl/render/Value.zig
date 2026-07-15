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
    pool: *const InternPool,
    pub fn format(self: Formatter, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        render(self.value, self.pool, null, writer) catch |err| switch (err) {
            error.WriteFailed => return error.WriteFailed,
            else => try writer.writeAll("<value>"),
        };
    }
};

pub fn fmt(value: Value, pool: *const InternPool) Formatter {
    return .{ .value = value, .pool = pool };
}

/// Writes a value to `writer` with no trailing newline: a REPL result line
/// appends its own terminator at the print site; diagnostics embed the value
/// mid-message.
pub fn render(
    value: Value,
    pool: *const InternPool,
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
            return writer.print("ptr@{d}+{d}", .{ @intFromEnum(p.ty), p.byte_offset });
        },
        .slice => |s| {
            if (try renderByteSlice(pool, writer, s)) return;
            // Otherwise the elements live behind the slice's `ptr` in a Sema
            // comptime alloc the renderer cannot reach, so render just the length.
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const len = pool.indexToKey(s.len).int.storage.toBigInt(&space);
            return writer.print("slice[{f}]", .{len});
        },
        .err => |e| writer.print("error.{s}", .{pool.stringSlice(e.name)}),
        .error_union => |eu| renderErrorUnion(eu, pool, session, writer),
        .func => |f| writer.print("fn@{d}", .{@intFromEnum(f.zir_body_inst)}),
        .aggregate => |agg| renderAggregate(agg, pool, session, writer),
        .enum_tag => |et| renderEnumTag(et, pool, session, writer),
        .un => |uv| renderUnion(uv, pool, session, writer),
        // A bare type Key viewed as a value identifies the type itself
        // (Sema's value-of-type-type convention; see Value.typeOf). The
        // value Keys above are exhaustive, so the assert turns a future
        // unclassified one into a crash rather than a mis-render as a type.
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
    pool: *const InternPool,
    session: ?*const Session,
    writer: *std.Io.Writer,
) Error!void {
    // A by-value `[N]u8` array prints as a string (`"...".*`), like any bytes ref.
    if (try renderBytes(pool, writer, agg, .value)) return;
    const ty_key = pool.indexToKey(agg.ty);
    const shaped = ty_key == .struct_type and session != null;
    // A named struct prints `TypeName{ ... }`; a tuple `.{ ... }`; an array or
    // vector positionally `{ ... }`.
    if (shaped) try renderTypeRef(agg.ty, pool, writer) else if (ty_key == .tuple_type) try writer.writeByte('.');
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
            .repeated_elem => pool.aggregateElementCount(agg.ty),
        },
    };
    var i: u64 = 0;
    while (i < count) : (i += 1) {
        if (i > 0) try writer.writeAll(", ");
        if (shaped) {
            if (structFieldName(pool, session.?, agg.ty, @intCast(i))) |name|
                try writer.print(".{s} = ", .{name});
        }
        const elem_idx: InternPool.Index = switch (agg.storage) {
            .repeated_elem => |e| e,
            .elems => |es| es[@intCast(i)],
        };
        try render(.{ .index = elem_idx }, pool, session, writer);
    }
    try writer.writeAll(" }");
}

/// The name of struct field `index` -- stored for a reified struct, read from the
/// declaring ZIR for a declared one. Null if unavailable (the caller falls back to
/// positional). The read-only analogue of `Sema.structFieldNameAt`.
fn structFieldName(pool: *const InternPool, session: *const Session, struct_ty: InternPool.Index, index: u32) ?[]const u8 {
    if (pool.loadStructType(struct_ty)) |f| return if (index < f.field_names.len) pool.stringSlice(f.field_names[index]) else null;
    const d = switch (pool.indexToKey(struct_ty).struct_type) {
        .declared => |dd| dd,
        else => return null,
    };
    if (d.source_zir_id >= session.files.items.len) return null;
    const zir = session.files.items[d.source_zir_id].zir orelse return null;
    var it = zir.getStructDecl(d.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (field.idx == index) return zir.nullTerminatedString(field.name);
    }
    return null;
}

/// The name of union field `index` -- stored for a reified union, read from the
/// declaring ZIR for a declared one. The read-only analogue of `Sema.unionFieldNameAt`.
fn unionFieldName(pool: *const InternPool, session: *const Session, union_ty: InternPool.Index, index: u32) ?[]const u8 {
    if (pool.unionFields(union_ty)) |f| return if (index < f.field_names.len) pool.stringSlice(f.field_names[index]) else null;
    const d = switch (pool.indexToKey(union_ty).union_type) {
        .declared => |dd| dd,
        else => return null,
    };
    if (d.source_zir_id >= session.files.items.len) return null;
    const zir = session.files.items[d.source_zir_id].zir orelse return null;
    var it = zir.getUnionDecl(d.decl_inst).iterateFields();
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

fn aggElem(agg: InternPool.Key.Aggregate, i: u64) InternPool.Index {
    return switch (agg.storage) {
        .repeated_elem => |e| e,
        .elems => |es| es[@intCast(i)],
    };
}

/// Whether an interned value is the `.ref` (pointer to the array) or `.value`
/// (the array itself) form of a bytes container -- the compiler's `is_ref`
/// distinction, which decides the trailing `.*` (src/print_value.zig
/// printAggregate).
const BytesForm = enum { ref, value };

/// Render aggregate `agg` as a quoted Zig string when it is an all-concrete-byte
/// `[N]u8` array, stripping one trailing `0` as the compiler does, appending `.*`
/// for the `.value` form. Returns false without writing otherwise, so the caller
/// renders positionally. The REPL interns each byte as its own `u8` slot rather
/// than the compiler's packed `.bytes` storage, so string form keys on the
/// element type and concreteness: a single `undefined` element falls back to the
/// positional `{ ... }`, mirroring that `.bytes` cannot encode undef.
fn renderBytes(pool: *const InternPool, writer: *std.Io.Writer, agg: InternPool.Key.Aggregate, form: BytesForm) Error!bool {
    const ty_key = pool.indexToKey(agg.ty);
    if (ty_key != .array_type or ty_key.array_type.child != .u8_type) return false;
    var count = ty_key.array_type.lenIncludingSentinel();
    var i: u64 = 0;
    while (i < count) : (i += 1) {
        if (byteValue(pool, aggElem(agg, i)) == null) return false;
    }
    if (count > 0 and byteValue(pool, aggElem(agg, count - 1)).? == 0) count -= 1;
    try writer.writeByte('"');
    i = 0;
    while (i < count) : (i += 1) {
        try std.zig.stringEscape(&.{byteValue(pool, aggElem(agg, i)).?}, writer);
    }
    try writer.writeByte('"');
    if (form == .value) try writer.writeAll(".*");
    return true;
}

/// The backing array and start element for a slice's pointer when it is a
/// self-contained const ref the read-only renderer can follow: a `.uav` (the
/// whole array) or an `.arr_elem` into one (the `arr[0..]` shape `coerceToSlice`
/// builds). Null for `comptime_alloc`/`nav`/`field` bases, whose storage lives in
/// Sema out of the renderer's reach.
fn sliceBacking(pool: *const InternPool, slice: InternPool.Key.Slice) ?struct { array: InternPool.Index, start: u64 } {
    if (pool.indexToKey(slice.ptr) != .ptr) return null;
    switch (pool.indexToKey(slice.ptr).ptr.base_addr) {
        .uav => |u| return .{ .array = u.val, .start = 0 },
        .arr_elem => |ae| {
            if (pool.indexToKey(ae.base) != .ptr) return null;
            const base = pool.indexToKey(ae.base).ptr.base_addr;
            if (base != .uav) return null;
            return .{ .array = base.uav.val, .start = ae.index };
        },
        else => return null,
    }
}

/// Render a `[]u8`/`[:0]u8` slice as a quoted string when its backing array is a
/// reachable const ref of concrete bytes over the sliced range; false (no output)
/// otherwise, so the caller falls back to the length placeholder.
fn renderByteSlice(pool: *const InternPool, writer: *std.Io.Writer, slice: InternPool.Key.Slice) Error!bool {
    const slice_ty = pool.indexToKey(slice.ty);
    if (slice_ty != .ptr_type or slice_ty.ptr_type.child != .u8_type) return false;
    const backing = sliceBacking(pool, slice) orelse return false;
    const len_i = intOf(pool, slice.len) orelse return false;
    if (len_i < 0) return false;
    const len: u64 = @intCast(len_i);
    if (pool.indexToKey(backing.array) != .aggregate) return false;
    const agg = pool.indexToKey(backing.array).aggregate;
    const total: u64 = switch (agg.storage) {
        .elems => |es| es.len,
        .repeated_elem => std.math.maxInt(u64),
    };
    if (backing.start + len > total) return false;
    var i: u64 = 0;
    while (i < len) : (i += 1) {
        if (byteValue(pool, aggElem(agg, backing.start + i)) == null) return false;
    }
    try writer.writeByte('"');
    i = 0;
    while (i < len) : (i += 1) {
        try std.zig.stringEscape(&.{byteValue(pool, aggElem(agg, backing.start + i)).?}, writer);
    }
    try writer.writeByte('"');
    return true;
}

/// The field name an `enum_tag` selects: for a generated union-tag enum, the
/// union's field at the tag index; otherwise the enum's resolved fields (cached
/// once a value of the enum was produced) -- an auto enum indexes by the tag, an
/// explicit one matches the tag value. Null if the fields are not resolved.
fn enumTagName(pool: *const InternPool, session: *const Session, enum_ty: InternPool.Index, int_idx: InternPool.Index) ?[]const u8 {
    const tag = intOf(pool, int_idx) orelse return null;
    const gen = pool.indexToKey(enum_ty).enum_type.generatedUnion();
    if (gen != .none) return if (tag >= 0) unionFieldName(pool, session, gen, @intCast(tag)) else null;
    const f = pool.loadEnumType(enum_ty) orelse return null;
    if (f.field_values.len == 0) return if (tag >= 0 and tag < f.field_names.len) pool.stringSlice(f.field_names[@intCast(tag)]) else null;
    for (f.field_values, 0..) |v, pos| {
        if (intOf(pool, v)) |vv| if (vv == tag) return pool.stringSlice(f.field_names[pos]);
    }
    return null;
}

/// `.tag` when the tag name resolves, else the underlying integer.
fn renderEnumTag(et: InternPool.Key.EnumTag, pool: *const InternPool, session: ?*const Session, writer: *std.Io.Writer) Error!void {
    if (session) |s| if (enumTagName(pool, s, et.ty, et.int)) |name| return writer.print(".{s}", .{name});
    return render(.{ .index = et.int }, pool, session, writer);
}

/// `.{ .field = payload }` when the active field name resolves, else the payload.
fn renderUnion(uv: InternPool.Key.Union, pool: *const InternPool, session: ?*const Session, writer: *std.Io.Writer) Error!void {
    if (session) |s| {
        const tag_key = pool.indexToKey(uv.tag);
        if (tag_key == .enum_tag) if (intOf(pool, tag_key.enum_tag.int)) |idx| {
            if (idx >= 0) if (unionFieldName(pool, s, uv.ty, @intCast(idx))) |name| {
                try renderTypeRef(uv.ty, pool, writer);
                try writer.print("{{ .{s} = ", .{name});
                try render(.{ .index = uv.val }, pool, session, writer);
                return writer.writeAll(" }");
            };
        };
    }
    return render(.{ .index = uv.val }, pool, session, writer);
}

fn renderErrorUnion(
    eu: InternPool.Key.ErrorUnion,
    pool: *const InternPool,
    session: ?*const Session,
    writer: *std.Io.Writer,
) Error!void {
    switch (eu.val) {
        .err_name => |name| try writer.print("error.{s}", .{pool.stringSlice(name)}),
        .payload => |idx| try render(.{ .index = idx }, pool, session, writer),
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

/// Print each float-storage variant in its native precision. f80 has no
/// dedicated `std.fmt` formatter, so we widen to f128 for display only;
/// the stored value keeps its precision.
///
/// `std.fmt`'s `{d}` strips the trailing decimal for integral values
/// (`4.0` -> "4"), which is ambiguous next to integers in REPL output.
/// We restore the `.0` when the printed form has no decimal exponent or
/// dot -- but leave NaN / inf / -inf untouched.
fn renderFloat(
    float: InternPool.Key.Float,
    writer: *std.Io.Writer,
) Error!void {
    var buf: [128]u8 = undefined;
    const text = switch (float.storage) {
        .f80 => |v| std.fmt.bufPrint(&buf, "{d}", .{@as(f128, @floatCast(v))}) catch unreachable,
        inline else => |v| std.fmt.bufPrint(&buf, "{d}", .{v}) catch unreachable,
    };
    try writer.writeAll(text);
    if (needsTrailingDecimal(text)) try writer.writeAll(".0");
}

/// True IFF `text` is a finite-magnitude float printed without a decimal
/// point or exponent (e.g. "4", "-7") -- in which case appending ".0"
/// keeps the value visually distinct from an integer. NaN / inf / -inf
/// start with a non-digit and are left alone.
fn needsTrailingDecimal(text: []const u8) bool {
    if (text.len == 0) return false;
    if (std.mem.indexOfAny(u8, text, ".eE") != null) return false;
    const start: usize = if (text[0] == '-' or text[0] == '+') 1 else 0;
    if (start >= text.len) return false;
    return std.ascii.isDigit(text[start]);
}

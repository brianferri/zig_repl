//! CSI (Control Sequence Introducer) parser. ECMA-48 / ISO 6429
//! sec 5.4. Wire form:
//!
//!   ESC [ <params> <intermediates> <final>
//!
//! Where:
//!   params         = ASCII digits, with `;` separating primary
//!                    parameters and `:` introducing sub-parameters
//!                    (a post-ECMA-48 extension that protocols opt
//!                    into). Private-use lead bytes 0x3C..0x3F (`<`
//!                    `=` `>` `?`) act as intermediates.
//!   intermediates  = bytes in 0x20..0x2F plus the private-use
//!                    lead bytes mentioned above.
//!   final          = a single byte in 0x40..0x7E.
//!
//! Out-of-range finals or excess intermediates are reported as
//! `null token` with `consumed = cursor` so the caller drops the
//! malformed prefix and recovers.

const std = @import("std");
const assert = std.debug.assert;
const Standard = @import("../Standard.zig");

pub const max_params: u32 = 16;
pub const max_subparams_per_param: u32 = 8;
pub const max_intermediates: u32 = 2;

pub const Sequence = struct {
    /// Primary parameters in declaration order. `params_count == 0`
    /// means "all defaults". A missing primary position (e.g. the
    /// `1` in `CSI ;2u`) is reported as its default value `0`.
    params: [max_params]u32 = @splat(0),
    /// `params_count` slots in `params` are populated.
    params_count: u32 = 0,
    /// Sub-parameters per primary, packed. `subparams_count[i]`
    /// slots in `subparams[i]` are populated. Sub-params are a
    /// post-ECMA-48 extension consumed by protocols that opt in.
    subparams: [max_params][max_subparams_per_param]u32 = @splat(@splat(0)),
    subparams_count: [max_params]u32 = @splat(0),
    /// Intermediate bytes in 0x20..0x2F plus the private-use lead
    /// bytes 0x3C..0x3F (`<` `=` `>` `?`).
    intermediates: [max_intermediates]u8 = @splat(0),
    intermediates_count: u32 = 0,
    /// Final byte in 0x40..0x7E. Always present for a well-formed
    /// CSI sequence.
    final: u8,

    /// Returns the i-th primary parameter, or `default` if missing.
    /// Wraps the bounds check so consumers can read defaults without
    /// inline `if (i < count)` ladders.
    pub fn param(seq: Sequence, i: u32, default: u32) u32 {
        assert(i < max_params);
        if (i >= seq.params_count) return default;
        return seq.params[i];
    }

    pub fn hasIntermediate(seq: Sequence, b: u8) bool {
        for (seq.intermediates[0..seq.intermediates_count]) |it| {
            if (it == b) return true;
        }
        return false;
    }

    /// Whether the sequence carries one of the private-use lead bytes
    /// `?` `>` `<` that mark capability queries/replies rather than key
    /// events. (`=`, the fourth private-lead byte, is unused by the
    /// keyboard protocols, so it is not treated as one here.)
    pub fn hasPrivateLead(seq: Sequence) bool {
        return seq.hasIntermediate('?') or seq.hasIntermediate('>') or seq.hasIntermediate('<');
    }
};

/// Whether `b` is a CSI final byte (0x40..0x7E, ECMA-48 sec 5.4). A final
/// terminates the sequence; any other byte after the parameters/intermediates
/// is malformed.
pub fn isFinal(b: u8) bool {
    return b >= 0x40 and b <= 0x7e;
}

/// Whether `buf` contains a CSI sequence (`ESC [ ...`) whose final byte
/// equals `final`. When `lead` is non-null, the byte right after `[` must
/// equal it -- the private-use lead (e.g. `?`) on a capability reply.
/// Used to spot one specific reply inside a batch of probe responses.
pub fn containsFinal(buf: []const u8, lead: ?u8, final: u8) bool {
    assert(buf.len < std.math.maxInt(u32));
    var i: u32 = 0;
    while (i + 1 < buf.len) : (i += 1) {
        if (buf[i] != 0x1b) continue;
        if (buf[i + 1] != '[') continue;
        var j: u32 = i + 2;
        if (lead) |l| {
            if (j >= buf.len or buf[j] != l) continue;
            j += 1;
        }
        while (j < buf.len) : (j += 1) {
            const b = buf[j];
            if (b == final) return true;
            // Any other CSI final byte: this sequence isn't the one
            // we're after. Stop and keep scanning from the next ESC.
            if (isFinal(b)) break;
        }
    }
    return false;
}

pub const standard: Standard = .{
    .introducer = '[',
    .name = "CSI",
    .parse = parse,
};

fn parse(input: []const u8) Standard.Result {
    assert(input.len >= 2);
    assert(input[0] == 0x1b);
    assert(input[1] == '[');

    var csi: Sequence = .{ .final = 0 };
    var scan: ParamScan = .{};
    var cursor: u32 = 2;

    cursor = scanParams(&csi, &scan, input, cursor);
    cursor = scanIntermediates(&csi, input, cursor) catch
        return .{ .token = null, .consumed = @intCast(cursor) };

    if (cursor >= input.len) return .{ .token = null, .consumed = 0 };
    const final = input[cursor];
    if (!isFinal(final)) {
        return .{ .token = null, .consumed = @intCast(cursor + 1) };
    }
    csi.final = final;

    // Flush trailing parameter only when a digit was accumulated. A
    // bare `CSI A` has zero parameters; a trailing-separator shape
    // like `CSI 1;A` correctly stops at 1 param (the spec leaves
    // post-separator empty slots up to the consumer to default).
    if (scan.have_current_param) commitParam(&csi, scan);

    return .{ .token = .{ .csi = csi }, .consumed = @intCast(cursor + 1) };
}

const ParamScan = struct {
    current_param: u32 = 0,
    current_subparam: u32 = 0,
    have_current_param: bool = false,
    in_subparam: bool = false,
};

/// Walk parameter bytes per ECMA-48: 0x30..0x39 are digits, ';'
/// (0x3B) separates primary params, ':' (0x3A) separates sub-params.
/// 0x3C..0x3F are private-use lead bytes which `scanIntermediates`
/// picks up next. Returns the cursor position at first non-param byte.
fn scanParams(
    csi: *Sequence,
    scan: *ParamScan,
    input: []const u8,
    start: u32,
) u32 {
    assert(start <= input.len);
    var cursor = start;
    while (cursor < input.len) : (cursor += 1) {
        const b = input[cursor];
        if (b >= '0' and b <= '9') {
            scan.have_current_param = true;
            const digit: u32 = b - '0';
            if (scan.in_subparam) {
                const slot = csi.params_count;
                if (csi.subparams_count[slot] >= max_subparams_per_param) continue;
                scan.current_subparam = scan.current_subparam * 10 + digit;
            } else {
                scan.current_param = scan.current_param * 10 + digit;
            }
            continue;
        }
        if (b == ';') {
            commitParam(csi, scan.*);
            scan.* = .{};
            continue;
        }
        if (b == ':') {
            commitParam(csi, scan.*);
            scan.current_subparam = 0;
            scan.have_current_param = false;
            scan.in_subparam = true;
            continue;
        }
        break;
    }
    assert(cursor >= start);
    return cursor;
}

/// Intermediate bytes are 0x20..0x2F and 0x3C..0x3F (private-use
/// lead). Returns the cursor position at first non-intermediate
/// byte. Errors when capacity is exceeded so the caller can bail
/// the whole sequence.
fn scanIntermediates(csi: *Sequence, input: []const u8, start: u32) !u32 {
    assert(start <= input.len);
    var cursor = start;
    while (cursor < input.len) : (cursor += 1) {
        const b = input[cursor];
        const is_intermediate = (b >= 0x20 and b <= 0x2F);
        const is_private = (b >= 0x3C and b <= 0x3F);
        if (!is_intermediate and !is_private) break;
        if (csi.intermediates_count >= max_intermediates) return error.TooManyIntermediates;
        csi.intermediates[csi.intermediates_count] = b;
        csi.intermediates_count += 1;
    }
    assert(cursor >= start);
    return cursor;
}

fn commitParam(csi: *Sequence, scan: ParamScan) void {
    if (scan.in_subparam) {
        // Sub-param attaches to the LAST committed primary. The `:`
        // dispatch always commits a primary first, so we expect
        // `params_count >= 1` here. The `0 -> 0` fallback covers the
        // degenerate `CSI :5u` shape (no primary first) by implicitly
        // attaching to slot 0.
        const slot: u32 = if (csi.params_count == 0) 0 else csi.params_count - 1;
        const sub_slot = csi.subparams_count[slot];
        if (sub_slot < max_subparams_per_param) {
            const value: u32 = if (scan.have_current_param) scan.current_subparam else 0;
            csi.subparams[slot][sub_slot] = value;
            csi.subparams_count[slot] = sub_slot + 1;
        }
        return;
    }
    if (csi.params_count >= max_params) return;
    csi.params[csi.params_count] = if (scan.have_current_param) scan.current_param else 0;
    csi.params_count += 1;
}

//! CSI (Control Sequence Introducer) parser, `ESC [ <params> <intermediates>
//! <final>` (ECMA-48 sec 5.4). Params are ASCII digits, `;`-separated, with `:`
//! sub-parameters; intermediates are 0x20..0x2F plus private-use lead bytes
//! 0x3C..0x3F; the final is one byte in 0x40..0x7E. A malformed sequence yields
//! a `null` token with `consumed = cursor` so the caller drops it and recovers.

const std = @import("std");
const assert = std.debug.assert;
const Standard = @import("../Standard.zig");

pub const max_params: u32 = 16;
pub const max_subparams_per_param: u32 = 8;
pub const max_intermediates: u32 = 2;

pub const Sequence = struct {
    /// Primary parameters in order. A missing position (the `1` in `CSI ;2u`)
    /// reads as its default `0`.
    params: [max_params]u32 = @splat(0),
    params_count: u32 = 0,
    /// Per-primary sub-parameters, `subparams_count[i]` slots populated each.
    subparams: [max_params][max_subparams_per_param]u32 = @splat(@splat(0)),
    subparams_count: [max_params]u32 = @splat(0),
    intermediates: [max_intermediates]u8 = @splat(0),
    intermediates_count: u32 = 0,
    final: u8,

    /// The i-th primary parameter, or `default` if absent.
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

    /// The private-use lead bytes `?` `>` `<` mark capability queries/replies,
    /// not key events. (`=` is unused by the keyboard protocols, so it is excluded.)
    pub fn hasPrivateLead(seq: Sequence) bool {
        return seq.hasIntermediate('?') or seq.hasIntermediate('>') or seq.hasIntermediate('<');
    }
};

/// Whether `b` is a CSI final byte (0x40..0x7E, ECMA-48 sec 5.4).
pub fn isFinal(b: u8) bool {
    return b >= 0x40 and b <= 0x7e;
}

/// Whether `buf` contains a CSI sequence with the given `final`, and (when
/// `lead` is non-null) that lead byte right after `[`. Spots one specific reply
/// inside a batch of probe responses.
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
            // A different final ends this sequence; resume from the next ESC.
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

    // Flush the trailing parameter only when a digit accumulated, so `CSI A`
    // stays at zero params and `CSI 1;A` at one (empty trailing slot defaulted).
    if (scan.have_current_param) commitParam(&csi, scan);

    return .{ .token = .{ .csi = csi }, .consumed = @intCast(cursor + 1) };
}

const ParamScan = struct {
    current_param: u32 = 0,
    current_subparam: u32 = 0,
    have_current_param: bool = false,
    in_subparam: bool = false,
};

/// Walks parameter bytes (`;` separates primaries, `:` sub-params), stopping at
/// the first non-param byte and returning its cursor position.
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

/// Consumes intermediate bytes (0x20..0x2F, private-use lead 0x3C..0x3F),
/// stopping at the first non-intermediate. Errors when capacity is exceeded so
/// the caller can bail the whole sequence.
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
        // Attaches to the last committed primary; the slot-0 fallback covers the
        // degenerate `CSI :5u` shape with no primary first.
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

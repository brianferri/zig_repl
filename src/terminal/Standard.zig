//! Per-standard escape-sequence parser interface. Each ECMA-48 / VT100 / xterm
//! wire form (CSI, SS3, OSC, ...) lives under `standard/`; `Parser` dispatches
//! on the byte after ESC. Stateless, so a plain `(introducer, name, parse)` struct.

const std = @import("std");

const Standard = @This();

/// Byte after `ESC` that selects this standard (CSI=`[`, SS3=`O`, OSC=`]`, ...).
introducer: u8,
name: []const u8,
/// Parses from `input[0]` (ESC) to the end of the wire form; yields a `null`
/// token with `consumed=0` when the input is incomplete.
parse: *const fn (input: []const u8) Result,

pub const Result = struct {
    token: ?Token,
    consumed: u32,
};

/// Scans a string-command payload (`ESC <id> <payload> ST`) from `input[2]` for
/// its terminator -- BEL (0x07) or ST (`ESC \`) -- returning the payload end and
/// the bytes consumed through the terminator, or null when none is present yet.
pub fn scanStringTerminated(input: []const u8) ?struct { payload_end: u32, consumed: u32 } {
    var i: u32 = 2;
    while (i < input.len) : (i += 1) {
        if (input[i] == 0x07) return .{ .payload_end = i, .consumed = i + 1 };
        if (input[i] == 0x1b and i + 1 < input.len and input[i + 1] == '\\') {
            return .{ .payload_end = i, .consumed = i + 2 };
        }
    }
    return null;
}

/// Classified escape sequence emitted by `Parser`; each protocol decides how to
/// interpret it into a high-level `Event`.
pub const Token = union(enum) {
    /// Printable or C0 control other than ESC, passed through unchanged so
    /// protocols decide whether e.g. 0x03 is "Ctrl+C" or "ETX byte".
    ground: u8,
    /// `ESC` then a printable byte; conventionally Alt+<char>, meaning unbound.
    escape_alt: u8,
    csi: @import("standard/Csi.zig").Sequence,
    ss3: @import("standard/Ss3.zig").Sequence,
    /// `ESC ] ... ST` payload, verbatim.
    osc: []const u8,
    /// Lone ESC press (no follow-on byte within the parser's window).
    bare_escape,
};

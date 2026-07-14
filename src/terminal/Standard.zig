//! Per-standard escape-sequence parser interface. Each ECMA-48
//! / VT100 / xterm wire-form (CSI, SS3, OSC, DCS, ...) lives in
//! its own file under `standard/`; the `Parser` keeps a registry
//! of these and dispatches on the byte that follows ESC.
//!
//! No vtable / `@fieldParentPtr`: standards are stateless byte-
//! stream eaters, just `(introducer, name, parse)`.
//!
//! Result-shape (`Result`) and the classified-output union (`Token`)
//! live here too: they're intrinsic to what "standard" means. Each
//! standard contributes one variant to `Token`.

const std = @import("std");

const Standard = @This();

/// The byte that follows `ESC` to discriminate this standard from
/// the others. CSI = `[` (0x5B), SS3 = `O` (0x4F), OSC = `]` (0x5D),
/// DCS = `P` (0x50), SOS = `X` (0x58), PM = `^` (0x5E), APC = `_`
/// (0x5F), SS2 = `N` (0x4E).
introducer: u8,
/// Human-readable identifier for diagnostics.
name: []const u8,
/// Parse from `input[0]` (which is ESC) to the end of this
/// standard's wire form. Returns the consumed byte count and the
/// classified Token, or `null` token with `consumed=0` when the
/// input is incomplete.
parse: *const fn (input: []const u8) Result,

pub const Result = struct {
    token: ?Token,
    consumed: u32,
};

/// Scan a string-command payload (`ESC <id> <payload> ST`, shared by OSC
/// and the DCS/SOS/PM/APC commands) from `input[2]` for its terminator --
/// BEL (0x07) or ST (`ESC \`). Returns the payload's end index and the
/// bytes consumed through the terminator, or null when no terminator is
/// present in `input` yet. Callers assert the leading `ESC <id>`.
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

/// Classified escape sequence emitted by `Parser`. Each protocol
/// then decides how to interpret the sequence into a high-level
/// `Event`. Standard-specific wire shapes (CSI parameters, SS3
/// final byte, OSC payload, ...) live in their owning
/// `standard/*.zig` files; this union just collects them.
pub const Token = union(enum) {
    /// A plain ground-state codepoint -- printable or C0 control
    /// other than ESC. The Parser passes these through unchanged so
    /// Protocols can decide whether 0x03 is "Ctrl+C" or "ETX byte".
    ground: u8,
    /// `ESC` followed by a printable byte. Conventionally
    /// interpreted as Alt+<char> reporting; the Parser doesn't bind
    /// the meaning.
    escape_alt: u8,
    csi: @import("standard/Csi.zig").Sequence,
    ss3: @import("standard/Ss3.zig").Sequence,
    /// `ESC ] ... ST` payload, verbatim. Protocols decide what to
    /// do with it.
    osc: []const u8,
    /// Lone ESC press (no follow-on byte within the parser's window).
    bare_escape,
};

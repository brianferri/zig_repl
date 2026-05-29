//! Per-standard escape-sequence parser interface. Each ECMA-48
//! / VT100 / xterm wire-form (CSI, SS3, OSC, DCS, ...) lives in
//! its own file under `standard/`; the `Parser` keeps a registry
//! of these and dispatches on the byte that follows ESC.
//!
//! No vtable / `@fieldParentPtr`: standards are stateless byte-
//! stream eaters, just `(introducer, name, parse)`. Adding a new
//! standard is a single-file drop-in plus a one-line append to the
//! `Parser` registry.
//!
//! Result-shape (`Result`) and the classified-output union (`Token`)
//! live here too: they're intrinsic to what "standard" means. Each
//! standard contributes one variant to `Token`; adding a standard
//! means defining its `Sequence` type next to the parser and
//! appending one variant here.

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

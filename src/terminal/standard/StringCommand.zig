//! String-command consumer for DCS / SOS / PM / APC. ECMA-48 sec
//! 5.5 defines four "string commands" that take an arbitrary
//! payload terminated by ST (`ESC \`):
//!
//!   DCS = ESC P <payload> ST   (Device Control String)
//!   SOS = ESC X <payload> ST   (Start of String)
//!   PM  = ESC ^ <payload> ST   (Privacy Message)
//!   APC = ESC _ <payload> ST   (Application Program Command)
//!
//! For the input side of a REPL editor, the payloads carry
//! protocol-specific information that this layer doesn't need to
//! decode (Kitty graphics replies, DEC RIS responses, etc.). We
//! recognise the sequences so a stray DCS reply doesn't pollute
//! later parsing, but emit no Token -- the dispatcher drops the
//! consumed bytes and pulls the next sequence.
//!
//! Each prefix gets its own `Standard` registration (different
//! introducer byte, identical parse logic).

const std = @import("std");
const assert = std.debug.assert;
const Standard = @import("../Standard.zig");

pub const dcs: Standard = .{ .introducer = 'P', .name = "DCS", .parse = parse };
pub const sos: Standard = .{ .introducer = 'X', .name = "SOS", .parse = parse };
pub const pm: Standard = .{ .introducer = '^', .name = "PM", .parse = parse };
pub const apc: Standard = .{ .introducer = '_', .name = "APC", .parse = parse };

fn parse(input: []const u8) Standard.Result {
    assert(input.len >= 2);
    assert(input[0] == 0x1b);
    var i: u32 = 2;
    while (i < input.len) : (i += 1) {
        // ST (ESC \) is the canonical terminator. BEL (0x07) is
        // accepted as xterm's alternate, mirroring OSC.
        if (input[i] == 0x07) {
            return .{ .token = null, .consumed = i + 1 };
        }
        if (input[i] == 0x1b and i + 1 < input.len and input[i + 1] == '\\') {
            return .{ .token = null, .consumed = i + 2 };
        }
    }
    return .{ .token = null, .consumed = 0 };
}

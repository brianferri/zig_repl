//! ST (String Terminator) standalone consumer. ECMA-48 sec 5.5.
//! Wire form:
//!
//!   ESC \
//!
//! ST normally appears as the terminator of an OSC / DCS / SOS /
//! PM / APC payload, where it's matched inline by those parsers.
//! Registered here so a stray standalone `ESC \` (received outside
//! any string command's body) is consumed cleanly instead of
//! mis-dispatching as `escape_alt('\\')`.
//!
//! Emits no token -- the dispatcher drops the bytes and pulls the
//! next sequence. Mirrors the StringCommand consume-and-drop
//! pattern for the same reason: ST carries no input-event payload.

const std = @import("std");
const assert = std.debug.assert;
const Standard = @import("../Standard.zig");

pub const standard: Standard = .{
    .introducer = '\\',
    .name = "ST",
    .parse = parse,
};

fn parse(input: []const u8) Standard.Result {
    assert(input.len >= 2);
    assert(input[0] == 0x1b);
    assert(input[1] == '\\');
    return .{ .token = null, .consumed = 2 };
}

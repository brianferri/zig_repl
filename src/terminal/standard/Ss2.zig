//! SS2 (Single Shift 2) parser. ECMA-48 sec 8.3.139. Wire form:
//!
//!   ESC N <final>
//!
//! Designates G2 character set for the immediately-following byte.
//! Rare on input (xterm uses SS3 for keypad / arrow keys; few
//! terminals emit SS2 for keyboard) but covered here for Fe-family
//! completeness. Shape mirrors SS3 exactly.

const std = @import("std");
const assert = std.debug.assert;

const Standard = @import("../Standard.zig");

pub const standard: Standard = .{
    .introducer = 'N',
    .name = "SS2",
    .parse = parse,
};

fn parse(input: []const u8) Standard.Result {
    assert(input.len >= 2);
    assert(input[0] == 0x1b);
    assert(input[1] == 'N');
    if (input.len < 3) return .{ .token = null, .consumed = 0 };
    // SS2 carries the same shape as SS3 in the input direction --
    // reuse the SS3 variant so downstream protocols that handle SS3
    // arrows automatically pick up the rare SS2-encoded equivalent.
    return .{ .token = .{ .ss3 = .{ .final = input[2] } }, .consumed = 3 };
}

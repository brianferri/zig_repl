//! SS2 (Single Shift 2) parser, `ESC N <final>` (ECMA-48 sec 8.3.139). Rare on
//! input; covered for Fe-family completeness.

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
    // Same input-direction shape as SS3; reuse the variant so SS3 handlers pick
    // up the rare SS2-encoded equivalent.
    return .{ .token = .{ .ss3 = .{ .final = input[2] } }, .consumed = 3 };
}

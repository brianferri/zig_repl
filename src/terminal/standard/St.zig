//! Standalone ST (String Terminator) consumer, `ESC \` (ECMA-48 sec 5.5).
//! Registered so a stray ST outside any string-command body is consumed cleanly
//! instead of mis-dispatching as `escape_alt('\\')`. Emits no token.

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

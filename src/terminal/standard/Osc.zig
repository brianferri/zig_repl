//! OSC (Operating System Command) parser, `ESC ] <payload> ST` (ECMA-48 sec 5.5),
//! where ST is `ESC \` or BEL (0x07, xterm's alternate). Payload returned verbatim.

const std = @import("std");
const assert = std.debug.assert;

const Standard = @import("../Standard.zig");

pub const standard: Standard = .{
    .introducer = ']',
    .name = "OSC",
    .parse = parse,
};

fn parse(input: []const u8) Standard.Result {
    assert(input.len >= 2);
    assert(input[0] == 0x1b);
    assert(input[1] == ']');
    const scan = Standard.scanStringTerminated(input) orelse
        return .{ .token = null, .consumed = 0 };
    return .{ .token = .{ .osc = input[2..scan.payload_end] }, .consumed = scan.consumed };
}

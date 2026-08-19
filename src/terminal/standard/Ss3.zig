//! SS3 (Single Shift 3) parser, `ESC O <final>` (ECMA-48 sec 8.3.140, VT100
//! application mode). The final byte selects the key (`ESC O A` = app-mode up).

const std = @import("std");
const assert = std.debug.assert;
const Standard = @import("../Standard.zig");

pub const Sequence = struct {
    final: u8,
};

pub const standard: Standard = .{
    .introducer = 'O',
    .name = "SS3",
    .parse = parse,
};

fn parse(input: []const u8) Standard.Result {
    assert(input.len >= 2);
    assert(input[0] == 0x1b);
    assert(input[1] == 'O');
    if (input.len < 3) return .{ .token = null, .consumed = 0 };
    return .{ .token = .{ .ss3 = .{ .final = input[2] } }, .consumed = 3 };
}

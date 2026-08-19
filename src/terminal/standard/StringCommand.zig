//! String-command consumer for DCS / SOS / PM / APC (ECMA-48 sec 5.5): a payload
//! terminated by ST (`ESC \`). Recognised so a stray reply doesn't pollute later
//! parsing, but no Token is emitted -- the payloads carry nothing this layer
//! decodes. Each prefix gets its own `Standard` registration.

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
    const scan = Standard.scanStringTerminated(input) orelse
        return .{ .token = null, .consumed = 0 };
    return .{ .token = null, .consumed = scan.consumed };
}

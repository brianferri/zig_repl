const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: async and frame forms are rejected like the compiler" {
    try compliance.check(a, .{
        .{ .src = &.{"anyframe"}, .reject = {} },
        .{ .src = &.{"anyframe->u8"}, .reject = {} },
        .{ .src = &.{"blk: { const f = struct { fn g() void {} }.g; break :blk @Frame(f); }"}, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"anyframe->u8"}, "async has not been implemented in the self-hosted compiler yet");
}

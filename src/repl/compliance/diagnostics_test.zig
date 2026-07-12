const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: diagnostics match the compiler's wording" {
    try compliance.expectDiagnostic(a, &.{"blk: { const arr = [_]u8{ 1, 2, 3 }; break :blk arr[5]; }"}, "index 5 outside array of length 3");
    try compliance.expectDiagnostic(a, &.{"@as(u8, 7) / @as(u8, 0)"}, "division by zero here causes illegal behavior");
    try compliance.expectDiagnostic(a, &.{"blk: { break :blk @as(i32, -7) % @as(i32, 3); }"}, "signed integers and floats must use @rem or @mod");
    try compliance.expectDiagnostic(a, &.{"blk: { const S = struct { fn f(x: u32) u8 { return x; } }; break :blk S.f(5); }"}, "expected type 'u8', found 'u32'");
    try compliance.expectDiagnostic(a, &.{"blk: { const S = struct { fn f(x: u8) u8 { return x; } }; break :blk S.f(1, 2); }"}, "expected 1 argument(s), found 2");
}

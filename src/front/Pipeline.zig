const std = @import("std");
const assert = std.debug.assert;

const InputShape = @import("InputShape.zig");

pub const Result = struct {
    wrapped: InputShape.Wrapped,
    tree: std.zig.Ast,
    zir: std.zig.Zir,

    pub fn deinit(result: *Result, gpa: std.mem.Allocator) void {
        assert(@intFromPtr(result) != 0);
        result.zir.deinit(gpa);
        result.tree.deinit(gpa);
        result.wrapped.deinit(gpa);
        result.* = undefined;
    }

    pub fn hasParseErrors(result: *const Result) bool {
        assert(@intFromPtr(result) != 0);
        return result.tree.errors.len != 0;
    }

    pub fn hasZirErrors(result: *const Result) bool {
        assert(@intFromPtr(result) != 0);
        return result.zir.hasCompileErrors();
    }

    pub fn source(result: *const Result) [:0]const u8 {
        assert(@intFromPtr(result) != 0);
        return result.wrapped.text;
    }
};

pub fn run(gpa: std.mem.Allocator, input: []const u8) !Result {
    assert(input.len > 0);
    assert(input.len <= InputShape.max_input_bytes);

    var wrapped = try InputShape.wrap(gpa, input);
    errdefer wrapped.deinit(gpa);

    var tree = try std.zig.Ast.parse(gpa, wrapped.text, .zig);
    errdefer tree.deinit(gpa);

    var zir = try std.zig.AstGen.generate(gpa, tree);
    errdefer zir.deinit(gpa);

    return .{ .wrapped = wrapped, .tree = tree, .zir = zir };
}

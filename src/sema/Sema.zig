//! Runtime-only port of the compiler's `analyzeBodyInner` (Sema.zig). Drops
//! every `Block.is_comptime` branch, all `ComptimeReason`/`branch_quota`
//! machinery, and the per-thread analysis-graph bookkeeping
//! (`pt`/`owner`/`func_index`). Replaces the compiler's AIR backend with
//! direct interpretation against the InternPool.
//!
//! Reference: /home/brianferri/Desktop/Main/Projects/zig/src/Sema.zig.
//! Handler arms land per ZIR-tag group; until a tag is explicitly handled
//! it surfaces a deterministic `unsupported_zir_inst: <tag>` diagnostic.
//! There is no silent fallback.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Zir = std.zig.Zir;

const InternPool = @import("InternPool.zig");
const Value = @import("Value.zig");

const Sema = @This();

pub const Error = Allocator.Error || std.Io.Writer.Error || error{
    UnsupportedZirInst,
};

/// Walks the ZIR produced by AstGen for a single REPL line and returns its
/// resulting Value, or null when there is nothing to evaluate. Diagnostics
/// for unhandled instructions are written to `writer`.
pub fn analyze(
    gpa: Allocator,
    intern_pool: *InternPool,
    zir: Zir,
    writer: *std.Io.Writer,
) Error!?Value {
    assert(!zir.hasCompileErrors());
    assert(@intFromPtr(intern_pool) != 0);

    if (zir.instructions.len == 0) return null;

    const tags = zir.instructions.items(.tag);
    return dispatchInstruction(gpa, intern_pool, zir, tags[0], writer);
}

fn dispatchInstruction(
    gpa: Allocator,
    intern_pool: *InternPool,
    zir: Zir,
    tag: Zir.Inst.Tag,
    writer: *std.Io.Writer,
) Error!?Value {
    _ = gpa;
    _ = intern_pool;
    _ = zir;

    return switch (tag) {
        inline else => |unhandled| reportUnsupported(unhandled, writer),
    };
}

fn reportUnsupported(
    comptime tag: Zir.Inst.Tag,
    writer: *std.Io.Writer,
) Error!?Value {
    try writer.print("unsupported ZIR instruction: {s}\n", .{@tagName(tag)});
    return error.UnsupportedZirInst;
}

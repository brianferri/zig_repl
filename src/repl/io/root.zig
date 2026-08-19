//! The single facade `Sema` imports as `runtime`; runtime memory and I/O live behind `runtime.zig`.

const runtime = @import("runtime.zig");
const Sema = @import("../sema/Sema.zig");

pub const retargetLoad = runtime.retargetLoad;
pub const retargetStore = runtime.retargetStore;
pub const writeBack = runtime.writeBack;
pub const StoreTarget = runtime.StoreTarget;
pub const callIntrinsic = runtime.callIntrinsic;

pub const WriterIo = @import("writer_io.zig");

// Target-agnostic today, so every target embeds the same source; a divergent target gets its own file.
const impl_source: [:0]const u8 = @embedFile("impl.zig");

pub fn install(sema: *Sema) Sema.Error!void {
    return runtime.install(sema, impl_source);
}

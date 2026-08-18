//! The interpreter's runtime layer -- the single facade `Sema` imports as `runtime`. Store/load of
//! runtime memory and the runtime I/O both live behind here (see `runtime.zig`); `install` binds the
//! intrinsic `Io` (`impl.zig`) into root.

const runtime = @import("runtime.zig");
const Sema = @import("../sema/Sema.zig");

pub const retargetLoad = runtime.retargetLoad;
pub const retargetStore = runtime.retargetStore;
pub const writeBack = runtime.writeBack;
pub const StoreTarget = runtime.StoreTarget;
pub const callIntrinsic = runtime.callIntrinsic;

// A host `Io` backed by a writer, for frontends with no OS Io (wasm) and tests capturing output.
pub const WriterIo = @import("writer_io.zig");

// The intrinsic `Io` is target-agnostic today, so every target embeds the same source; a target that
// needs a different one gets its own file and a `switch` here.
const impl_source: [:0]const u8 = @embedFile("impl.zig");

pub fn install(sema: *Sema) Sema.Error!void {
    return runtime.install(sema, impl_source);
}

//! Core shared by the tty and wasm frontends. They are separate modules that
//! import this one; it names no frontend driver, so each frontend links only
//! the surface it needs (the wasm target never pulls the posix tty stack).

pub const Session = @import("Session.zig");
pub const eval = @import("eval.zig");
pub const sema = @import("sema/root.zig");
pub const front = @import("front/root.zig");
pub const render = @import("render/root.zig");
/// Module sources: where `@import` obtains bytes. `module.Source` is the
/// interface; `module.Native` reads the on-disk standard library, `module.Buffer`
/// an archive packed into the binary for targets with no filesystem. Locating or
/// embedding that source is the frontend's job (the core opens no files itself).
pub const module = @import("module/root.zig");
pub const io = @import("io/root.zig");
/// Generic command framework (`:name` dispatch). Frontends register their own
/// command set with `commands.Registry`; the frontend-specific
/// commands live in the frontend modules.
pub const commands = @import("drivers/commands/root.zig");

// `zig build test` only discovers tests in files referenced from a module
// root. The tty driver's files are forced from its own module root.
test {
    _ = @import("Session.zig");
    _ = @import("module/root.zig");
    _ = @import("eval.zig");
    _ = @import("drivers/commands/Command.zig");
    _ = @import("drivers/commands/registry.zig");
    _ = @import("drivers/commands/help.zig");
    _ = @import("drivers/commands/dump.zig");
    _ = @import("front/InputShape.zig");
    _ = @import("front/Pipeline.zig");
    _ = @import("render/Diagnostic.zig");
    _ = @import("render/Value.zig");
    _ = @import("sema/InternPool.zig");
    _ = @import("sema/Type.zig");
    _ = @import("sema/Value.zig");
    _ = @import("sema/Sema.zig");
    _ = @import("sema/arith.zig");
    _ = @import("sema_eval_test.zig");
    _ = @import("compliance/root.zig");
}

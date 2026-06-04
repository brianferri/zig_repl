// Root of the native executable's module: the frontend-agnostic core
// (`Session`, Sema) and the tty driver `main.zig` runs against it.
pub const Session = @import("Session.zig");
pub const sema = @import("sema/root.zig");
pub const Repl = @import("drivers/tty/Repl.zig");
// `zig build test` only discovers tests in modules referenced from the root
// file. Force inclusion of every source file's tests by referencing them at
// comptime here.
test {
    _ = @import("Session.zig");
    _ = @import("eval.zig");
    _ = @import("drivers/tty/Repl.zig");
    _ = @import("drivers/tty/root.zig");
    _ = @import("drivers/tty/quit.zig");
    _ = @import("drivers/tty/theme.zig");
    _ = @import("drivers/tty/terminal.zig");
    _ = @import("drivers/tty/LineEditor.zig");
    _ = @import("drivers/mock/Device.zig");
    _ = @import("drivers/tty/Theme.zig");
    _ = @import("drivers/tty/theme/root.zig");
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
    _ = @import("zig_compliance_test.zig");
}

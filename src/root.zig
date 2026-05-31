pub const Session = @import("Session.zig");
pub const Repl = @import("Repl.zig");
pub const LineEditor = @import("LineEditor.zig");
pub const commands = @import("commands.zig");
pub const sema = @import("sema/root.zig");
pub const render = struct {
    pub const Diagnostic = @import("render/Diagnostic.zig");
    pub const value = @import("render/Value.zig");
};

// `zig build test` only discovers tests in modules referenced from the root
// file. Force inclusion of every source file's tests by referencing them at
// comptime here.
test {
    _ = @import("Session.zig");
    _ = @import("Repl.zig");
    _ = @import("LineEditor.zig");
    _ = @import("Theme.zig");
    _ = @import("theme/root.zig");
    _ = @import("terminal/Color.zig");
    _ = @import("terminal/Terminal.zig");
    _ = @import("terminal/Parser.zig");
    _ = @import("terminal/Event.zig");
    _ = @import("terminal/Protocol.zig");
    _ = @import("terminal/Standard.zig");
    _ = @import("terminal/Negotiate.zig");
    _ = @import("terminal/standard/Csi.zig");
    _ = @import("terminal/standard/Ss2.zig");
    _ = @import("terminal/standard/Ss3.zig");
    _ = @import("terminal/standard/Osc.zig");
    _ = @import("terminal/standard/St.zig");
    _ = @import("terminal/standard/StringCommand.zig");
    _ = @import("terminal/protocol/Xterm.zig");
    _ = @import("terminal/protocol/ModifyOtherKeys.zig");
    _ = @import("terminal/protocol/Kitty.zig");
    _ = @import("terminal/protocol/BracketedPaste.zig");
    _ = @import("terminal/terminal_test.zig");
    // Platform backends import OS-specific headers; pick the one
    // matching the host so cross-target test runs stay clean.
    _ = switch (@import("builtin").os.tag) {
        .windows => @import("terminal/platform/Windows.zig"),
        else => @import("terminal/platform/Posix.zig"),
    };
    _ = @import("commands.zig");
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

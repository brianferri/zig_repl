pub const Session = @import("Session.zig");
pub const Repl = @import("Repl.zig");
pub const commands = @import("commands.zig");
pub const sema = struct {
    pub const InternPool = @import("sema/InternPool.zig");
    pub const Type = @import("sema/Type.zig");
    pub const Value = @import("sema/Value.zig");
    pub const Sema = @import("sema/Sema.zig");
};
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
    _ = @import("commands.zig");
    _ = @import("front/InputShape.zig");
    _ = @import("front/Pipeline.zig");
    _ = @import("render/Diagnostic.zig");
    _ = @import("render/Value.zig");
    _ = @import("sema/InternPool.zig");
    _ = @import("sema/Type.zig");
    _ = @import("sema/Value.zig");
    _ = @import("sema/Sema.zig");
}

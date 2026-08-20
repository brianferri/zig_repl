//! Frontend-agnostic interpreter session: allocator, intern pool, root namespace, and committed pipeline snapshots.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("sema/InternPool.zig");
const ModuleSource = @import("module/Fs.zig");
const ErrorMsg = @import("sema/ErrorMsg.zig").ErrorMsg;
const InputShape = @import("front/InputShape.zig");

const Session = @This();

gpa: std.mem.Allocator,
/// The caller owns and `deinit`s it; `Session.deinit` does not.
intern_pool: *InternPool,
/// Where top-level `const`/`var` lines bind; modules hang their own namespaces off it via the `parent`
/// chain (the compiler's per-file-root namespace).
root_namespace: InternPool.NamespaceIndex,
/// The empty `File` reserved for `@import("root")`: root's decls live in `root_namespace`, not one
/// container, so it has no ZIR, but it needs a permanent distinct `File.Index` so its identity
/// `(file_index, main_struct_inst)` never aliases a line or module. `null` until first `@import("root")`.
root_file: ?Index = null,
/// Each lowered source file (committed REPL lines + loaded modules); a `File.Index` indexes here. Each
/// file's Ast and wrapped source persist for the session because a Sema diagnostic resolves its
/// `LazySrcLoc` against the owning file's tree, so the tree must outlive analysis.
files: std.ArrayListUnmanaged(File) = .empty,
/// Pending Sema failure (the compiler's `Zcu.failed_analysis`, single-slot here since one unit is analyzed
/// per call). The driver resolves its `LazySrcLoc`, renders a caret, then `destroy`s it. gpa-owned.
failed_analysis: ?*ErrorMsg = null,
/// Loaded on-disk files by canonical sub-path (the compiler's `Zcu.import_table`); REPL lines are absent
/// (no path). Keys alias each `File.sub_file_path`, so the map is torn down before those strings are freed.
import_table: std.StringHashMapUnmanaged(Index) = .empty,
/// How `@import` obtains module bytes, injected by the frontend. `null` means modules cannot load, so
/// `@import` of std/root/builtin fails -- freestanding wasm and tests that never import.
module_source: ?*ModuleSource = null,
/// Runtime-layer state for the intrinsic `Io`: `io` is the single host `Io` every runtime leaf (print
/// sink, clock, filesystem) delegates to, frontend-injected; `null` leaves the runtime inert.
/// `installed` tracks whether `root.std_options_debug_io` is bound. `open_files` is the handle table a
/// `__repl_open` indexes into; `__repl_close` nulls the slot for reuse, and any still-open file is closed
/// at session teardown.
runtime: struct {
    io: ?std.Io = null,
    installed: bool = false,
    open_files: std.ArrayListUnmanaged(?std.Io.File) = .empty,
} = .{},

/// Index into `files`; the REPL's `Zcu.File.Index`.
pub const Index = u32;

/// A lowered source file, the REPL's `Zcu.File`.
pub const File = struct {
    /// The lowered ZIR, or `null` for a failed line kept as a tombstone so later `File.Index` values stay stable.
    zir: ?std.zig.Zir,
    /// The Ast the file was lowered from, kept so a Sema diagnostic can resolve its `LazySrcLoc` into a
    /// byte span. `null` only before it is set.
    tree: ?std.zig.Ast = null,
    /// The wrapped source the Ast was parsed from, plus the coordinates mapping it back to the user's text;
    /// a diagnostic slices the caret's source line from it. `null` for files with no wrap.
    wrapped: ?InputShape.Wrapped = null,
    /// Path relative to the source root, the base for this file's relative imports. `null` for a REPL line
    /// (no on-disk path); owned when non-null.
    sub_file_path: ?[]const u8,
    /// The file-root container type (`main_struct_inst`), set once the file is analysed as a module. `.none`
    /// for a REPL line (its decls bind into the session namespace).
    root_type: InternPool.Index = .none,
};

pub fn init(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    root_namespace: InternPool.NamespaceIndex,
) Session {
    return .{
        .gpa = gpa,
        .intern_pool = intern_pool,
        .root_namespace = root_namespace,
    };
}

pub fn deinit(session: *Session) void {
    if (session.runtime.io) |io| {
        for (session.runtime.open_files.items) |file| if (file) |f| f.close(io);
    }
    session.runtime.open_files.deinit(session.gpa);
    if (session.failed_analysis) |em| em.destroy(session.gpa);
    // Tear down `import_table` first: its keys alias the `sub_file_path` strings freed just below.
    session.import_table.deinit(session.gpa);
    for (session.files.items) |*file| {
        if (file.zir) |*z| z.deinit(session.gpa);
        if (file.tree) |*t| t.deinit(session.gpa);
        if (file.wrapped) |*w| w.deinit(session.gpa);
        if (file.sub_file_path) |p| session.gpa.free(p);
    }
    session.files.deinit(session.gpa);
    session.* = undefined;
}

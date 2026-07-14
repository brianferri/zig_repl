//! Frontend-agnostic interpreter session: the state a backend needs to
//! evaluate input -- allocator, intern pool, root namespace, and the
//! committed pipeline snapshots. No terminal, file, or IO surface; those
//! live in the frontend (`frontend/tty/Repl.zig` for the TTY REPL). Any
//! frontend -- the TTY REPL, a wasm module, or a test -- creates one of
//! these directly.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("sema/InternPool.zig");
const ModuleSource = @import("module/Source.zig");
const ErrorMsg = @import("sema/ErrorMsg.zig").ErrorMsg;
const InputShape = @import("front/InputShape.zig");

const Session = @This();

gpa: std.mem.Allocator,
/// Borrowed: caller owns the InternPool and is responsible for
/// `deinit`-ing it. Session.deinit does not touch the pool.
/// Decoupling lets tests share a pool across multiple Sessions
/// or construct minimal Sessions on top of an existing pool
/// without lifecycle complications.
intern_pool: *InternPool,
/// The session-root namespace -- the parent-less scope into which
/// top-level `const` / `var` lines bind. Mirrors the role of the
/// compiler's per-file-root namespace; modules hang their own
/// namespaces off this root via the `parent` chain.
root_namespace: InternPool.NamespaceIndex,
/// The file that backs `@import("root")` -- the REPL's `Zcu.root_mod`. The root's
/// decls live in `root_namespace` as resolved Navs spread across line files, not
/// one walkable container, so root has no ZIR of its own; this reserves an empty
/// `File` purely to give root a permanent, distinct `File.Index`, so its container
/// identity `(file_index, main_struct_inst)` can never alias a line or module.
/// Root's type lives in that file's `root_type` slot, read back via `fileRootType`
/// like any file. `null` until first `@import("root")`.
root_file: ?Index = null,
/// Every source file the session has lowered to ZIR: each committed REPL line
/// and each loaded module (`std` and the files it imports). Mirrors the
/// compiler's `Zcu.File` collection; `source_zir_id` (on a Func or a container
/// type) is a `File.Index` into this list, so crossing into another file's ZIR
/// is one indexed lookup, exactly as the compiler resolves a `TrackedInst`'s
/// file. Persist for the session lifetime, together with each file's Ast and
/// wrapped source -- a Sema diagnostic resolves its `LazySrcLoc` against the owning
/// file's tree, so the tree must outlive analysis, as `Zcu.File` keeps `tree`/`source`.
files: std.ArrayListUnmanaged(File) = .empty,
/// The pending Sema failure, set by `Sema.failWithOwnedErrorMsg` when a session is
/// present. The REPL's single-slot analog of the compiler's `Zcu.failed_analysis`
/// (a map keyed by `AnalUnit`): one unit is analyzed per call, so at most one
/// failure is pending at the analyze boundary. The driver, which holds the `Ast`,
/// resolves the carried `LazySrcLoc` and renders a caret, then `destroy`s it. gpa-owned.
failed_analysis: ?*ErrorMsg = null,
/// Loaded on-disk files by canonical sub-path -> `File.Index`, so each is read
/// and lowered once. The compiler's `Zcu.import_table`. REPL lines are not
/// here: they have no path. Keys alias each `File.sub_file_path` (no separate
/// allocation), so the map is torn down before those strings are freed.
import_table: std.StringHashMapUnmanaged(Index) = .empty,
/// How `@import` obtains module bytes, injected by the frontend (a pointer to
/// the `interface` field of a concrete reader it owns). `null` (the default)
/// means the environment cannot load modules, so `@import` of
/// `std`/`root`/`builtin` fails -- the case for freestanding wasm and for
/// tests that never import.
module_source: ?*ModuleSource = null,

/// Index into `files`; the REPL's `Zcu.File.Index`.
pub const Index = u32;

/// A lowered source file, the REPL's `Zcu.File`. No incremental rebuild, ZON,
/// or multi-module graph here.
pub const File = struct {
    /// The lowered ZIR, or `null` for a REPL line whose analysis failed -- kept
    /// as a tombstone so later `File.Index` values stay stable, as the compiler
    /// retains a failed file (`status == astgen_failure`).
    zir: ?std.zig.Zir,
    /// The Ast this file was lowered from, kept so a Sema diagnostic can resolve its
    /// `LazySrcLoc` (base declaration node + offset) into a byte span. Mirrors
    /// `Zcu.File.tree`; the compiler additionally makes it droppable and re-parses via
    /// `getTree`, an optimization not adopted here. `null` only before it is set.
    tree: ?std.zig.Ast = null,
    /// The wrapped source the Ast was parsed from, and the coordinates that map it
    /// back to what the user typed. Mirrors `Zcu.File.source`; a diagnostic renderer
    /// slices the caret's source line out of it. `null` for files with no wrap.
    wrapped: ?InputShape.Wrapped = null,
    /// Path relative to the source root, the base for this file's own relative
    /// imports (`Zcu.File.sub_file_path`). `null` for a REPL line, which has no
    /// on-disk path. Owned when non-null.
    sub_file_path: ?[]const u8,
    /// The file-root container type (`main_struct_inst`), set once the file is
    /// analysed as a module. The compiler's `Zcu.fileRootType`. `.none` for a
    /// REPL line (its decls bind into the session namespace, not a root type).
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
    if (session.failed_analysis) |em| em.destroy(session.gpa);
    // Tear down `import_table` first: its keys alias the `sub_file_path` strings
    // freed just below.
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

//! Root of the fuzz module. The suite is a standalone consumer of the `repl`
//! module (imported by name, not by `../` path), so it is fully decoupled from the
//! interpreter's internals -- `zig build fuzz` builds and runs it on its own.
//!
//! `stress_test.zig` holds a `std.testing.fuzz` target (the proper std mechanism,
//! coverage-guided under `zig build fuzz --fuzz`) alongside a deterministic
//! corpus-mutation loop. It runs as its own build step, not folded into `test`,
//! because the sanitizer coverage the coverage-guided runtime needs (`Module.fuzz`)
//! still segfaults that runtime (`fuzzer.zig` `fuzzer_new_input`) in the pinned
//! toolchain -- the ensureCorpusLoaded crash of ziglang/zig#25352 is fixed, this is
//! a later one. The corpus replay and mutation paths need no instrumentation and run
//! clean; fold into `test` once the runtime is stable.

test {
    _ = @import("regression_test.zig");
    _ = @import("stress_test.zig");
}

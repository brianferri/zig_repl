//! Root of the fuzz module. The suite is a standalone consumer of the `repl`
//! module (imported by name, not by `../` path), so it is fully decoupled from the
//! interpreter's internals -- `zig build fuzz` builds and runs it on its own.
//!
//! It runs as its own build step only because the pinned toolchain's coverage-
//! guided fuzzer (`--fuzz`) segfaults in its runtime (`fuzzer.zig:ensureCorpusLoaded`);
//! see ziglang/zig#25352. Once that is fixed upstream, drop the `fuzz` step and add
//! this module to the normal `test` step -- no code here changes.

test {
    _ = @import("regression_test.zig");
    _ = @import("stress_test.zig");
}

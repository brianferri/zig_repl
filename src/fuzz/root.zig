//! Standalone fuzz suite: imports `repl` by name, run via `zig build fuzz`. Its own
//! build step, separate from `test`, because the coverage-guided runtime
//! (`std.testing.fuzz` under `--fuzz`) still segfaults in the pinned toolchain
//! (`fuzzer.zig` `fuzzer_new_input`); the replay and mutation paths run clean.

test {
    _ = @import("regression_test.zig");
    _ = @import("stress_test.zig");
}

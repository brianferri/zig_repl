//! Deterministic randomized stress suite, imported into `zig build test`. Seeded by `-Dfuzz-seed` and
//! scaled by `-Dfuzz-iterations`; coverage-guided fuzzing runs through the compliance harness under `--fuzz`.

test {
    _ = @import("stress_test.zig");
}

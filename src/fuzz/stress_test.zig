//! Randomized stress: drive the interpreter with mutated inputs so a leak or crash
//! surfaces. Mutates the seed corpus of working programs -- the parser rejects
//! random bytes on sight, so perturbing working programs keeps inputs near-valid and
//! reaches AstGen/Sema/eval. Deterministic per `-Dfuzz-seed`, scaled by `-Dfuzz-iterations`.

const std = @import("std");
const options = @import("build_options");
const harness = @import("harness.zig");
const corpus = @import("corpus.zig");
const InputShape = @import("repl").front.InputShape;

const gpa = std.testing.allocator;
const Random = std.Random;

const max_bytes = InputShape.max_input_bytes;

const Strategy = enum { mutated_line, pristine_line, mutated_sequence, spliced_sequence };
const Op = enum { flip, replace, insert, delete, duplicate };

test "randomized interpreter stress (corpus mutation)" {
    var prng: Random.DefaultPrng = .init(options.fuzz_seed);
    const rand = prng.random();
    var buf: [max_bytes]u8 = undefined;

    var i: usize = 0;
    while (i < options.fuzz_iterations) : (i += 1) {
        switch (rand.enumValue(Strategy)) {
            .mutated_line => harness.runLine(gpa, mutate(rand, &buf)),
            // A pristine seed guarantees the run keeps exercising real evaluation,
            // not just near-misses the front end rejects.
            .pristine_line => harness.runLine(gpa, corpus.lines[rand.uintLessThanBiased(usize, corpus.lines.len)]),
            .mutated_sequence => {
                const seq = corpus.sequences[rand.uintLessThanBiased(usize, corpus.sequences.len)];
                var runner = harness.SessionRunner.init(gpa) orelse continue;
                defer runner.deinit();
                for (seq) |line| {
                    // Mutate in place off this line so each feed is independent.
                    const n = @min(line.len, buf.len);
                    @memcpy(buf[0..n], line[0..n]);
                    runner.feed(perturb(rand, buf[0..n], n));
                }
            },
            .spliced_sequence => {
                var runner = harness.SessionRunner.init(gpa) orelse continue;
                defer runner.deinit();
                const lines = rand.uintLessThanBiased(usize, 4) + 1;
                var l: usize = 0;
                while (l < lines) : (l += 1) runner.feed(mutate(rand, &buf));
            },
        }
    }
}

/// Build one mutated input in `buf`: a corpus line, sometimes spliced with a
/// second, then perturbed by a handful of byte edits.
fn mutate(rand: Random, buf: []u8) []const u8 {
    const base = corpus.lines[rand.uintLessThanBiased(usize, corpus.lines.len)];
    var len = @min(base.len, buf.len);
    @memcpy(buf[0..len], base[0..len]);

    if (rand.boolean()) {
        const other = corpus.lines[rand.uintLessThanBiased(usize, corpus.lines.len)];
        const at = rand.uintLessThanBiased(usize, len + 1);
        const take = @min(other.len, buf.len - at);
        @memcpy(buf[at..][0..take], other[0..take]);
        len = @max(len, at + take);
    }
    return perturb(rand, buf, len);
}

/// Apply a few byte-level edits to `buf[0..len]`, returning the new slice.
fn perturb(rand: Random, buf: []u8, start_len: usize) []const u8 {
    var len = start_len;
    const edits = rand.uintLessThanBiased(usize, 8);
    var e: usize = 0;
    while (e < edits and len > 0) : (e += 1) {
        const at = rand.uintLessThanBiased(usize, len);
        switch (rand.enumValue(Op)) {
            .flip => buf[at] ^= @as(u8, 1) << rand.int(u3),
            .replace => buf[at] = rand.int(u8),
            .insert => if (len < buf.len) {
                std.mem.copyBackwards(u8, buf[at + 1 .. len + 1], buf[at..len]);
                buf[at] = rand.int(u8);
                len += 1;
            },
            .delete => {
                std.mem.copyForwards(u8, buf[at .. len - 1], buf[at + 1 .. len]);
                len -= 1;
            },
            .duplicate => {
                const span = @min(rand.uintLessThanBiased(usize, 8) + 1, len - at);
                if (len + span <= buf.len) {
                    std.mem.copyBackwards(u8, buf[at + span .. len + span], buf[at..len]);
                    len += span;
                }
            },
        }
    }
    return buf[0..len];
}

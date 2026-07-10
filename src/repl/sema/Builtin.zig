//! Generates the `builtin` module's source, mirroring the compiler's
//! `src/Builtin.zig`. The compiler serializes a `Compilation`'s target and build
//! options into a source file it then analyses like any other; the REPL evaluates
//! native code, so the target is the REPL's own `@import("builtin").target`, and
//! only the target-model declarations are emitted -- enough for the
//! target-dependent resolution the REPL reaches (calling conventions:
//! `std.lang.CallingConvention.c` is `builtin.target.cCallingConvention()`).
//!
//! The `cpu`, `os`, and `abi` declarations, and the `target` that gathers them,
//! are written as fully expanded literals -- never via `Target` helper calls --
//! so the source parses back to the target value with no runtime dependency.

const std = @import("std");
const Allocator = std.mem.Allocator;
const native = @import("builtin");

/// Emit the `builtin` source for the native target. Caller owns the returned
/// bytes. Mirrors `Builtin.append`'s `abi`/`cpu`/`os`/`object_format`/`target`
/// serialization.
pub fn generate(gpa: Allocator) Allocator.Error![:0]u8 {
    const target = native.target;
    const arch_family_name = @tagName(target.cpu.arch.family());

    var buffer: std.array_list.Managed(u8) = .init(gpa);
    defer buffer.deinit();

    @setEvalBranchQuota(4000);
    try buffer.print(
        \\const std = @import("std");
        \\pub const abi: std.Target.Abi = .{f};
        \\pub const cpu: std.Target.Cpu = .{{
        \\    .arch = .{f},
        \\    .model = &std.Target.{f}.cpu.{f},
        \\    .features = std.Target.{f}.featureSet(&.{{
        \\
    , .{
        std.zig.fmtIdPU(@tagName(target.abi)),
        std.zig.fmtIdPU(@tagName(target.cpu.arch)),
        std.zig.fmtIdPU(arch_family_name),
        std.zig.fmtIdPU(target.cpu.model.name),
        std.zig.fmtIdPU(arch_family_name),
    });

    for (target.cpu.arch.allFeaturesList(), 0..) |feature, index_usize| {
        const index: std.Target.Cpu.Feature.Set.Index = @intCast(index_usize);
        if (target.cpu.features.isEnabled(index)) {
            try buffer.print("        .{f},\n", .{std.zig.fmtIdPU(feature.name)});
        }
    }
    try buffer.print(
        \\    }}),
        \\}};
        \\pub const os: std.Target.Os = .{{
        \\    .tag = .{f},
        \\    .version_range = .{{
    , .{std.zig.fmtIdPU(@tagName(target.os.tag))});

    switch (target.os.versionRange()) {
        .none => try buffer.appendSlice(" .none = {} },\n"),
        .semver => |semver| try buffer.print(
            \\ .semver = .{{
            \\        .min = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\        .max = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\    }}}},
            \\
        , .{
            semver.min.major, semver.min.minor, semver.min.patch,
            semver.max.major, semver.max.minor, semver.max.patch,
        }),
        .linux => |linux| try buffer.print(
            \\ .linux = .{{
            \\        .range = .{{
            \\            .min = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\            .max = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\        }},
            \\        .glibc = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\        .android = {},
            \\    }}}},
            \\
        , .{
            linux.range.min.major, linux.range.min.minor, linux.range.min.patch,
            linux.range.max.major, linux.range.max.minor, linux.range.max.patch,
            linux.glibc.major,     linux.glibc.minor,     linux.glibc.patch,
            linux.android,
        }),
        .hurd => |hurd| try buffer.print(
            \\ .hurd = .{{
            \\        .range = .{{
            \\            .min = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\            .max = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\        }},
            \\        .glibc = .{{ .major = {}, .minor = {}, .patch = {} }},
            \\    }}}},
            \\
        , .{
            hurd.range.min.major, hurd.range.min.minor, hurd.range.min.patch,
            hurd.range.max.major, hurd.range.max.minor, hurd.range.max.patch,
            hurd.glibc.major,     hurd.glibc.minor,     hurd.glibc.patch,
        }),
        .windows => |windows| try buffer.print(
            \\ .windows = .{{ .min = {f}, .max = {f} }}}},
            \\
        , .{ windows.min, windows.max }),
    }
    try buffer.print(
        \\}};
        \\pub const object_format: std.Target.ObjectFormat = .{f};
        \\pub const target: std.Target = .{{
        \\    .cpu = cpu,
        \\    .os = os,
        \\    .abi = abi,
        \\    .ofmt = object_format,
        \\
    , .{std.zig.fmtIdPU(@tagName(target.ofmt))});

    if (target.dynamic_linker.get()) |dl| {
        try buffer.print("    .dynamic_linker = .init(\"{s}\"),\n}};\n", .{dl});
    } else {
        try buffer.appendSlice("    .dynamic_linker = .none,\n};\n");
    }

    return buffer.toOwnedSliceSentinel(0);
}

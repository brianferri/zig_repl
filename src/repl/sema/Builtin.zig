const std = @import("std");
const Allocator = std.mem.Allocator;
const native = @import("builtin");

pub fn generate(gpa: Allocator) Allocator.Error![:0]u8 {
    const target = native.target;
    const arch_family_name = @tagName(target.cpu.arch.family());

    var buffer: std.array_list.Managed(u8) = .init(gpa);
    defer buffer.deinit();

    @setEvalBranchQuota(4000);
    try buffer.print(
        \\const std = @import("std");
        \\pub const zig_version = std.SemanticVersion.parse(zig_version_string) catch unreachable;
        \\pub const zig_version_string = "{s}";
        \\pub const zig_backend = std.lang.CompilerBackend.{f};
        \\pub const output_mode: std.lang.OutputMode = .{f};
        \\pub const link_mode: std.lang.LinkMode = .{f};
        \\pub const unwind_tables: std.lang.UnwindTables = .{f};
        \\pub const is_test = {};
        \\pub const single_threaded = {};
        \\pub const abi: std.Target.Abi = .{f};
        \\pub const cpu: std.Target.Cpu = .{{
        \\    .arch = .{f},
        \\    .model = &std.Target.{f}.cpu.{f},
        \\    .features = std.Target.{f}.featureSet(&.{{
        \\
    , .{
        native.zig_version_string,
        std.zig.fmtIdPU(@tagName(native.zig_backend)),
        std.zig.fmtIdPU(@tagName(native.output_mode)),
        std.zig.fmtIdPU(@tagName(native.link_mode)),
        std.zig.fmtIdPU(@tagName(native.unwind_tables)),
        native.is_test,
        native.single_threaded,
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
    try buffer.appendSlice(
        \\};
        \\pub const target: std.Target = .{
        \\    .cpu = cpu,
        \\    .os = os,
        \\    .abi = abi,
        \\    .ofmt = object_format,
        \\
    );

    if (target.dynamic_linker.get()) |dl| {
        try buffer.print("    .dynamic_linker = .init(\"{s}\"),\n}};\n", .{dl});
    } else {
        try buffer.appendSlice("    .dynamic_linker = .none,\n};\n");
    }

    try buffer.print(
        \\pub const object_format: std.Target.ObjectFormat = .{f};
        \\pub const mode: std.lang.OptimizeMode = .{f};
        \\pub const link_libc = {};
        \\pub const link_libcpp = {};
        \\pub const have_error_return_tracing = {};
        \\pub const valgrind_support = {};
        \\pub const sanitize_thread = {};
        \\pub const fuzz = {};
        \\pub const position_independent_code = {};
        \\pub const position_independent_executable = {};
        \\pub const strip_debug_info = {};
        \\pub const code_model: std.lang.CodeModel = .{f};
        \\pub const omit_frame_pointer = {};
        \\
    , .{
        std.zig.fmtIdPU(@tagName(target.ofmt)),
        std.zig.fmtIdPU(@tagName(native.mode)),
        native.link_libc,
        native.link_libcpp,
        native.have_error_return_tracing,
        native.valgrind_support,
        native.sanitize_thread,
        native.fuzz,
        native.position_independent_code,
        native.position_independent_executable,
        native.strip_debug_info,
        std.zig.fmtIdPU(@tagName(native.code_model)),
        native.omit_frame_pointer,
    });

    return buffer.toOwnedSliceSentinel(0);
}

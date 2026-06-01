const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const repl_module = b.addModule("zig_repl", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    const exe_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "zig_repl", .module = repl_module },
        },
    });
    exe_module.link_libc = true;

    if (target.result.os.tag == .windows) {
        exe_module.linkSystemLibrary("kernel32", .{});
    }

    const exe = b.addExecutable(.{
        .name = "zig_repl",
        .root_module = exe_module,
    });
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run the REPL");
    run_step.dependOn(&run_cmd.step);

    const docs_obj = b.addObject(.{
        .name = "zig_repl",
        .root_module = repl_module,
    });
    const install_docs = b.addInstallDirectory(.{
        .source_dir = docs_obj.getEmittedDocs(),
        .install_dir = .prefix,
        .install_subdir = "docs",
    });
    const docs_step = b.step("docs", "Generate library documentation");
    docs_step.dependOn(&install_docs.step);

    const module_tests = b.addTest(.{ .root_module = repl_module });
    const exe_tests = b.addTest(.{ .root_module = exe_module });
    const run_module_tests = b.addRunArtifact(module_tests);
    const run_exe_tests = b.addRunArtifact(exe_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_module_tests.step);
    test_step.dependOn(&run_exe_tests.step);
}

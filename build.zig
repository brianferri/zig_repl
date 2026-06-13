const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const repl = b.createModule(.{
        .root_source_file = b.path("src/repl/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    // The input-device vocabulary (`Device`, `Event`, `Color`) -- a leaf that
    // depends only on `std`, so frontends build on it without the tty stack.
    const device = b.createModule(.{
        .root_source_file = b.path("src/device/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    // The raw-mode terminal input stack, built on `device`. Separate from the
    // repl so the wasm frontend -- which never touches the tty -- omits it.
    const terminal = b.createModule(.{
        .root_source_file = b.path("src/terminal/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    terminal.addImport("device", device);

    const tty = b.createModule(.{
        .root_source_file = b.path("src/repl/drivers/tty/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    tty.addImport("repl", repl);
    tty.addImport("terminal", terminal);
    tty.addImport("device", device);

    const exe_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "repl", .module = repl },
            .{ .name = "tty", .module = tty },
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
        .root_module = repl,
    });
    const install_docs = b.addInstallDirectory(.{
        .source_dir = docs_obj.getEmittedDocs(),
        .install_dir = .prefix,
        .install_subdir = "docs",
    });
    const docs_step = b.step("docs", "Generate library documentation");
    docs_step.dependOn(&install_docs.step);

    const wasm_target = b.resolveTargetQuery(.{ .cpu_arch = .wasm32, .os_tag = .freestanding });

    const repl_wasm = b.createModule(.{
        .root_source_file = b.path("src/repl/root.zig"),
        .target = wasm_target,
        .optimize = optimize,
        .single_threaded = true,
        .link_libc = false,
    });
    const drivers_wasm = b.createModule(.{
        .root_source_file = b.path("src/repl/drivers/wasm/root.zig"),
        .target = wasm_target,
        .optimize = optimize,
        .single_threaded = true,
        .link_libc = false,
    });
    drivers_wasm.addImport("repl", repl_wasm);

    const wasm = b.addExecutable(.{
        .name = "zig_repl",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/wasm.zig"),
            .target = wasm_target,
            .optimize = optimize,
            .single_threaded = true,
            .link_libc = false,
            .imports = &.{
                .{ .name = "repl", .module = repl_wasm },
                .{ .name = "drivers_wasm", .module = drivers_wasm },
            },
        }),
    });
    wasm.rdynamic = true;
    wasm.entry = .disabled;

    const install_wasm = b.addInstallArtifact(wasm, .{
        .dest_dir = .{ .override = .{
            .custom = "web",
        } },
    });
    const install_web = b.addInstallDirectory(.{
        .source_dir = b.path("web/public"),
        .install_dir = .prefix,
        .install_subdir = "web",
    });
    const wasm_step = b.step("wasm", "Build the wasm REPL + web frontend");
    wasm_step.dependOn(&install_wasm.step);
    wasm_step.dependOn(&install_web.step);

    const repl_tests = b.addTest(.{ .root_module = repl });
    const tty_tests = b.addTest(.{ .root_module = tty });
    const exe_tests = b.addTest(.{ .root_module = exe_module });
    const device_tests = b.addTest(.{ .root_module = device });
    const terminal_tests = b.addTest(.{ .root_module = terminal });
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&b.addRunArtifact(repl_tests).step);
    test_step.dependOn(&b.addRunArtifact(tty_tests).step);
    test_step.dependOn(&b.addRunArtifact(exe_tests).step);
    test_step.dependOn(&b.addRunArtifact(device_tests).step);
    test_step.dependOn(&b.addRunArtifact(terminal_tests).step);
}

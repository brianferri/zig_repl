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

    const editor = b.createModule(.{
        .root_source_file = b.path("src/editor/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    editor.addImport("device", device);

    const tty = b.createModule(.{
        .root_source_file = b.path("src/repl/drivers/tty/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    tty.addImport("repl", repl);
    tty.addImport("terminal", terminal);
    tty.addImport("editor", editor);
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
    run_cmd.addPassthruArgs();
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
    // The device vocabulary, terminal parser, and line editor, rebuilt for the
    // wasm target so the wasm frontend reuses the same input + editing stack the
    // tty does (the `Terminal` platform backends are never referenced, so they
    // do not compile here).
    const device_wasm = b.createModule(.{
        .root_source_file = b.path("src/device/root.zig"),
        .target = wasm_target,
        .optimize = optimize,
        .single_threaded = true,
        .link_libc = false,
    });
    const terminal_wasm = b.createModule(.{
        .root_source_file = b.path("src/terminal/root.zig"),
        .target = wasm_target,
        .optimize = optimize,
        .single_threaded = true,
        .link_libc = false,
    });
    terminal_wasm.addImport("device", device_wasm);
    const editor_wasm = b.createModule(.{
        .root_source_file = b.path("src/editor/root.zig"),
        .target = wasm_target,
        .optimize = optimize,
        .single_threaded = true,
        .link_libc = false,
    });
    editor_wasm.addImport("device", device_wasm);
    const drivers_wasm = b.createModule(.{
        .root_source_file = b.path("src/repl/drivers/wasm/root.zig"),
        .target = wasm_target,
        .optimize = optimize,
        .single_threaded = true,
        .link_libc = false,
    });
    drivers_wasm.addImport("repl", repl_wasm);
    drivers_wasm.addImport("terminal", terminal_wasm);
    drivers_wasm.addImport("editor", editor_wasm);
    drivers_wasm.addImport("device", device_wasm);

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

    const pack_tool = b.addExecutable(.{
        .name = "tar_gz",
        .root_module = b.createModule(.{
            .root_source_file = b.path("tools/tar_gz.zig"),
            .target = b.resolveTargetQuery(.{}),
            .optimize = .ReleaseFast,
        }),
    });
    const pack_std = b.addRunArtifact(pack_tool);
    pack_std.addArg(zigStdDir(b));
    const std_targz = pack_std.addOutputFileArg("std.tar.gz");
    wasm.root_module.addAnonymousImport("embedded_std", .{ .root_source_file = std_targz });

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

    // The compliance tests load real `std`; the build hands them its path so they
    // need not search for it. Scoped to a test-only module so the production
    // `repl` (exe/tty/docs) never carries a build-machine path.
    const test_options = b.addOptions();
    test_options.addOption([]const u8, "zig_std_dir", zigStdDir(b));
    // Knobs for the randomized stress suite (src/fuzz). Deterministic per
    // seed, so a failure reproduces with the same `-Dfuzz-seed`; `-Dfuzz-iterations`
    // scales a run from a quick pass to an overnight soak.
    test_options.addOption(usize, "fuzz_iterations", b.option(usize, "fuzz-iterations", "Randomized stress iterations (default 256; raise for a real fuzzing run)") orelse 256);
    test_options.addOption(u64, "fuzz_seed", b.option(u64, "fuzz-seed", "Seed for the randomized stress suite (default 0)") orelse 0);
    test_options.addOption(bool, "reject_oracle", b.option(bool, "reject-oracle", "Cross-check every .reject compliance case against the real zig compiler") orelse false);
    test_options.addOption([]const u8, "zig_exe", b.graph.zig_exe);
    const repl_test_module = b.createModule(.{
        .root_source_file = b.path("src/repl/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    repl_test_module.addOptions("build_options", test_options);
    const repl_tests = b.addTest(.{ .root_module = repl_test_module, .use_llvm = true });
    const tty_tests = b.addTest(.{ .root_module = tty, .use_llvm = true });
    const exe_tests = b.addTest(.{ .root_module = exe_module, .use_llvm = true });
    const device_tests = b.addTest(.{ .root_module = device, .use_llvm = true });
    const terminal_tests = b.addTest(.{ .root_module = terminal, .use_llvm = true });
    const editor_tests = b.addTest(.{ .root_module = editor, .use_llvm = true });
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&b.addRunArtifact(repl_tests).step);
    test_step.dependOn(&b.addRunArtifact(tty_tests).step);
    test_step.dependOn(&b.addRunArtifact(exe_tests).step);
    test_step.dependOn(&b.addRunArtifact(device_tests).step);
    test_step.dependOn(&b.addRunArtifact(terminal_tests).step);
    test_step.dependOn(&b.addRunArtifact(editor_tests).step);

    // The fuzz suite is a standalone module that imports `repl` by name, so it is fully decoupled
    // from the interpreter's internals. It holds a `std.testing.fuzz` target (coverage-guided when
    // driven by `zig build fuzz --fuzz`) plus a deterministic corpus-mutation stress loop scaled by
    // `-Dfuzz-iterations` and reproduced with `-Dfuzz-seed`.
    const fuzz_module = b.createModule(.{
        .root_source_file = b.path("src/fuzz/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{.{ .name = "repl", .module = repl }},
    });
    fuzz_module.addOptions("build_options", test_options);
    // Coverage instrumentation (the program-counter table `--fuzz` slices to guide mutation) is only
    // emitted by the LLVM backend; under the self-hosted backend the table is empty and the fuzzer
    // panics slicing it. Force LLVM until self-hosted fuzz coverage lands.
    //   https://codeberg.org/ziglang/zig/issues/30655
    const fuzz_tests = b.addTest(.{ .root_module = fuzz_module, .use_llvm = true });
    const fuzz_step = b.step("fuzz", "Stress-test the interpreter (scale with -Dfuzz-iterations, reproduce with -Dfuzz-seed)");
    fuzz_step.dependOn(&b.addRunArtifact(fuzz_tests).step);
}

/// The running compiler's `std` source directory. Reuses the compiler's own
/// discovery (`std.zig.findZigLibDirFromSelfExe`): walk up from the `zig`
/// executable testing for `lib/zig/std/std.zig` then `lib/std/std.zig`, so it is
/// layout-agnostic across system installs and unpacked tarballs. Resolved at
/// configure time and injected as a build option the tests read.
fn zigStdDir(b: *std.Build) []const u8 {
    const io = b.graph.io;
    const cwd = std.zig.getResolvedCwd(io, b.allocator) catch @panic("cannot resolve cwd");
    const lib_dir = std.zig.findZigLibDirFromSelfExe(b.allocator, io, cwd, b.graph.zig_exe) catch
        @panic("cannot locate zig lib dir from zig executable");
    return b.pathJoin(&.{ lib_dir.path.?, "std" });
}

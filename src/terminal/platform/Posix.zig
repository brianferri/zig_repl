//! POSIX terminal backend. Owns `/dev/tty`, manipulates termios for
//! raw mode, installs SIGINT/SIGTERM/SIGHUP handlers that restore
//! cooked mode before the process dies.
//!
//! Selected at compile time by `Terminal.zig` via `builtin.os.tag`.
//! No vtable layer: the target is comptime-known, so the platform
//! contract is a direct concrete type. `Terminal` calls the methods
//! by name; cross-platform variation lives in the choice of file,
//! not in runtime dispatch.
//!
//! Single-instance constraint: termios save state and signal-prior
//! handlers live in file-local statics because POSIX signal handlers
//! carry no userdata. `init` enforces this with the `live` flag --
//! attempting a second instance fails with `error.AlreadyLive`.

const std = @import("std");
const assert = std.debug.assert;
const posix = std.posix;
const linux = std.os.linux;

const Posix = @This();

pub const Error = error{
    AlreadyLive,
    OpenTtyFailed,
    GetAttrFailed,
    SetAttrFailed,
    ReadFailed,
};

const probe_timeout_dsecs: u8 = 5;

/// Saved across the backend's lifetime AND across signal delivery.
/// File-local because POSIX signal handlers carry no userdata. Only
/// one Posix backend may live at a time.
var saved_termios: ?posix.termios = null;
var saved_termios_fd: posix.fd_t = 0;
var prior_sigint: posix.Sigaction = undefined;
var prior_sigterm: posix.Sigaction = undefined;
var prior_sighup: posix.Sigaction = undefined;
var live: bool = false;

io: std.Io,
tty_fd: posix.fd_t,
original: posix.termios,
signals_installed: bool,

pub fn init(_: std.mem.Allocator, io: std.Io) Error!Posix {
    assert(@intFromPtr(io.vtable) != 0);
    if (live) return error.AlreadyLive;
    assert(saved_termios == null);

    const tty_fd = posix.openat(posix.AT.FDCWD, "/dev/tty", .{ .ACCMODE = .RDWR }, 0) catch
        return error.OpenTtyFailed;
    errdefer closeFd(io, tty_fd);

    const original = posix.tcgetattr(tty_fd) catch return error.GetAttrFailed;

    saved_termios = original;
    saved_termios_fd = tty_fd;
    live = true;
    installSignalHandlers();

    return .{
        .io = io,
        .tty_fd = tty_fd,
        .original = original,
        .signals_installed = true,
    };
}

pub fn deinit(self: *Posix, _: std.mem.Allocator) void {
    assert(@intFromPtr(self) != 0);
    self.restore();
    closeFd(self.io, self.tty_fd);
    self.* = undefined;
}

/// `phase` is comptime so each call site monomorphizes -- the
/// switch resolves at compile time, leaving one specialized
/// function per phase with no runtime branch.
pub fn setRawMode(self: *Posix, comptime phase: enum { probe, interactive }) Error!void {
    assert(@intFromPtr(self) != 0);
    assert(live);
    var raw = self.original;
    clearCookedFlags(&raw);
    switch (phase) {
        .probe => {
            raw.cc[@intFromEnum(linux.V.MIN)] = 0;
            raw.cc[@intFromEnum(linux.V.TIME)] = probe_timeout_dsecs;
        },
        .interactive => {
            raw.cc[@intFromEnum(linux.V.MIN)] = 1;
            raw.cc[@intFromEnum(linux.V.TIME)] = 0;
        },
    }
    posix.tcsetattr(self.tty_fd, .FLUSH, raw) catch return error.SetAttrFailed;
}

pub fn restore(self: *Posix) void {
    assert(@intFromPtr(self) != 0);
    if (saved_termios) |orig| {
        // Cleanup-path swallow: failing tcsetattr during deinit
        // would only leak raw-mode state into the user's shell.
        // Panicking instead would do strictly worse -- the shell
        // is now both broken AND we've aborted with no diagnostic.
        posix.tcsetattr(saved_termios_fd, .NOW, orig) catch {};
        saved_termios = null;
    }
    if (self.signals_installed) {
        restoreSignalHandlers();
        self.signals_installed = false;
    }
    live = false;
}

pub fn read(self: *Posix, buf: []u8) Error!usize {
    assert(@intFromPtr(self) != 0);
    assert(buf.len > 0);
    return posix.read(self.tty_fd, buf) catch error.ReadFailed;
}

fn clearCookedFlags(raw: *posix.termios) void {
    assert(@intFromPtr(raw) != 0);
    raw.iflag.IGNBRK = false;
    raw.iflag.BRKINT = false;
    raw.iflag.PARMRK = false;
    raw.iflag.INLCR = false;
    raw.iflag.IGNCR = false;
    raw.iflag.ICRNL = false;
    raw.iflag.INPCK = false;
    raw.iflag.ISTRIP = false;
    raw.iflag.IXON = false;
    // OPOST stays ON: we want the kernel's ONLCR to translate bare
    // `\n` to `\r\n` on output so existing writers (commands, Sema
    // diagnostics) print readably without each one having to emit
    // CR explicitly. Raw mode on the INPUT side doesn't require raw
    // output -- they're independent flag sets.
    raw.oflag.OPOST = true;
    raw.lflag.ECHO = false;
    raw.lflag.ECHONL = false;
    raw.lflag.ICANON = false;
    raw.lflag.IEXTEN = false;
    raw.lflag.ISIG = false;
    raw.cflag.PARENB = false;
    raw.cflag.CSIZE = .CS8;
}

/// Wrap a raw fd as a `std.Io.File` so close goes through the Io
/// vtable. The new stdlib removed `posix.close`; File.close is the
/// canonical path.
fn closeFd(io: std.Io, fd: posix.fd_t) void {
    const file: std.Io.File = .{ .handle = fd, .flags = .{ .nonblocking = false } };
    std.Io.File.close(file, io);
}

fn installSignalHandlers() void {
    var act: posix.Sigaction = .{
        .handler = .{ .handler = onTerminationSignal },
        .mask = posix.sigemptyset(),
        .flags = 0,
    };
    posix.sigaction(posix.SIG.INT, &act, &prior_sigint);
    posix.sigaction(posix.SIG.TERM, &act, &prior_sigterm);
    posix.sigaction(posix.SIG.HUP, &act, &prior_sighup);
}

fn restoreSignalHandlers() void {
    posix.sigaction(posix.SIG.INT, &prior_sigint, null);
    posix.sigaction(posix.SIG.TERM, &prior_sigterm, null);
    posix.sigaction(posix.SIG.HUP, &prior_sighup, null);
}

fn onTerminationSignal(sig: posix.SIG) callconv(.c) void {
    // Restore termios before exit so the user's shell isn't left in
    // raw mode. POSIX convention: exit with 128 + signal so a parent
    // shell can read the cause. We swallow tcsetattr failure here
    // because we're inside a signal handler about to call exit(2);
    // there's no caller to receive an error and no recovery path.
    if (saved_termios) |orig| {
        posix.tcsetattr(saved_termios_fd, .NOW, orig) catch {};
    }
    std.process.exit(@as(u8, @intCast(128 + @intFromEnum(sig))));
}

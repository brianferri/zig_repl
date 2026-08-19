//! POSIX terminal backend. Owns `/dev/tty`, drives termios for raw mode, and
//! installs SIGINT/SIGTERM/SIGHUP handlers that restore cooked mode before the process dies.
//!
//! Single-instance: termios save state and prior signal handlers live in
//! file-local statics because POSIX signal handlers carry no userdata; `init`
//! enforces this with the `live` flag (`error.AlreadyLive` otherwise).

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
const posix = std.posix;

const Posix = @This();

pub const Error = error{
    AlreadyLive,
    OpenTtyFailed,
    GetAttrFailed,
    SetAttrFailed,
    ReadFailed,
};

const probe_timeout_dsecs: u8 = 5;

// UPSTREAM-WORKAROUND(std.os.linux.V): use `@intFromEnum(std.os.linux.V.MIN /
// .TIME)` once that enum compiles again. On Zig 0.17 its `arch_bits == .alpha`
// branch is ill-typed, so any reference to `linux.V` (and its `posix.V` / `c.V`
// aliases) fails to build. VTIME is index 5 on non-alpha; VMIN is 6, or 4 on mips.
const vmin_index: usize = switch (builtin.cpu.arch) {
    .mips, .mipsel, .mips64, .mips64el => 4,
    .sparc, .sparc64 => @compileError("VMIN cc index unverified for sparc; see std.os.linux.V"),
    else => 6,
};
const vtime_index: usize = switch (builtin.cpu.arch) {
    .sparc, .sparc64 => @compileError("VTIME cc index unverified for sparc; see std.os.linux.V"),
    else => 5,
};

/// File-local because signal handlers carry no userdata; only one backend lives at a time.
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
    self.restore();
    closeFd(self.io, self.tty_fd);
    self.* = undefined;
}

pub fn setRawMode(self: *Posix, comptime phase: enum { probe, interactive }) Error!void {
    assert(live);
    var raw = self.original;
    clearCookedFlags(&raw);
    switch (phase) {
        .probe => {
            raw.cc[vmin_index] = 0;
            raw.cc[vtime_index] = probe_timeout_dsecs;
        },
        .interactive => {
            raw.cc[vmin_index] = 1;
            raw.cc[vtime_index] = 0;
        },
    }
    posix.tcsetattr(self.tty_fd, .FLUSH, raw) catch return error.SetAttrFailed;
}

pub fn restore(self: *Posix) void {
    if (saved_termios) |orig| {
        // A cleanup-path panic would strand the shell in raw mode with no
        // diagnostic; swallow instead.
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
    assert(buf.len > 0);
    return posix.read(self.tty_fd, buf) catch error.ReadFailed;
}

fn clearCookedFlags(raw: *posix.termios) void {
    raw.iflag.IGNBRK = false;
    raw.iflag.BRKINT = false;
    raw.iflag.PARMRK = false;
    raw.iflag.INLCR = false;
    raw.iflag.IGNCR = false;
    raw.iflag.ICRNL = false;
    raw.iflag.INPCK = false;
    raw.iflag.ISTRIP = false;
    raw.iflag.IXON = false;
    // OPOST stays ON so the kernel's ONLCR keeps translating `\n` to `\r\n`;
    // raw input and raw output are independent, and writers emit bare `\n`.
    raw.oflag.OPOST = true;
    raw.lflag.ECHO = false;
    raw.lflag.ECHONL = false;
    raw.lflag.ICANON = false;
    raw.lflag.IEXTEN = false;
    raw.lflag.ISIG = false;
    raw.cflag.PARENB = false;
    raw.cflag.CSIZE = .CS8;
}

/// stdlib has no `posix.close`; close through `File.close` / the Io vtable.
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
    // Restore cooked mode before exiting 128 + signal (POSIX convention);
    // swallow failure, as a signal handler about to exit(2) has no recovery path.
    if (saved_termios) |orig| {
        posix.tcsetattr(saved_termios_fd, .NOW, orig) catch {};
    }
    std.process.exit(@as(u8, @intCast(128 + @backingInt(sig))));
}

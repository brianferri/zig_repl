//! Windows console backend. Puts the host in virtual-terminal mode
//! so the upstream Parser / Protocol layers see the same ANSI
//! escape sequence stream they do on POSIX.
//!
//! Handle acquisition goes through the PEB (`hStdInput` /
//! `hStdOutput`), the same path `std/Io/Threaded.zig` uses --
//! avoids loading kernel32 just to call `GetStdHandle`. Console
//! mode and CtrlHandler ARE done via kernel32 because the codeberg
//! issue tracking the kernel32 -> ntdll migration explicitly
//! exempts console APIs (zig issue #31131).

const std = @import("std");
const assert = std.debug.assert;
const windows = std.os.windows;

const Windows = @This();

pub const Error = error{
    AlreadyLive,
    GetConsoleModeFailed,
    SetConsoleModeFailed,
    ReadFailed,
};

const Handle = windows.HANDLE;
const Dword = windows.DWORD;
const Bool = windows.BOOL;

const ENABLE_PROCESSED_INPUT: Dword = 0x0001;
const ENABLE_LINE_INPUT: Dword = 0x0002;
const ENABLE_ECHO_INPUT: Dword = 0x0004;
const ENABLE_VIRTUAL_TERMINAL_INPUT: Dword = 0x0200;
const ENABLE_PROCESSED_OUTPUT: Dword = 0x0001;

const CP_UTF8: c_uint = 65001;

extern "kernel32" fn GetConsoleMode(hConsoleHandle: Handle, lpMode: *Dword) callconv(.winapi) Bool;
extern "kernel32" fn SetConsoleMode(hConsoleHandle: Handle, dwMode: Dword) callconv(.winapi) Bool;
extern "kernel32" fn GetConsoleOutputCP() callconv(.winapi) c_uint;
extern "kernel32" fn SetConsoleOutputCP(wCodePageID: c_uint) callconv(.winapi) Bool;
extern "kernel32" fn ReadFile(
    hFile: Handle,
    lpBuffer: [*]u8,
    nNumberOfBytesToRead: Dword,
    lpNumberOfBytesRead: *Dword,
    lpOverlapped: ?*anyopaque,
) callconv(.winapi) Bool;
extern "kernel32" fn SetConsoleCtrlHandler(
    HandlerRoutine: ?*const fn (Dword) callconv(.winapi) Bool,
    Add: Bool,
) callconv(.winapi) Bool;

/// File-local because Win32 console-control handlers carry no
/// userdata, mirroring the POSIX backend's signal-handler constraint.
var saved_input_mode: ?Dword = null;
var saved_output_mode: ?Dword = null;
var saved_codepage: ?c_uint = null;
var saved_stdin: Handle = undefined;
var saved_stdout: Handle = undefined;
var live: bool = false;

stdin_handle: Handle,
stdout_handle: Handle,
original_input_mode: Dword,
original_output_mode: Dword,
original_codepage: c_uint,
ctrl_handler_installed: bool,

pub fn init(_: std.mem.Allocator, _: std.Io) Error!Windows {
    if (live) return error.AlreadyLive;
    assert(saved_input_mode == null);

    const params = windows.peb().ProcessParameters;
    const stdin_h = params.hStdInput;
    const stdout_h = params.hStdOutput;

    var input_mode: Dword = 0;
    if (GetConsoleMode(stdin_h, &input_mode) == .FALSE) return error.GetConsoleModeFailed;
    var output_mode: Dword = 0;
    if (GetConsoleMode(stdout_h, &output_mode) == .FALSE) return error.GetConsoleModeFailed;
    const codepage = GetConsoleOutputCP();

    saved_input_mode = input_mode;
    saved_output_mode = output_mode;
    saved_codepage = codepage;
    saved_stdin = stdin_h;
    saved_stdout = stdout_h;
    live = true;
    const installed = SetConsoleCtrlHandler(onCtrlEvent, .TRUE) != .FALSE;

    return .{
        .stdin_handle = stdin_h,
        .stdout_handle = stdout_h,
        .original_input_mode = input_mode,
        .original_output_mode = output_mode,
        .original_codepage = codepage,
        .ctrl_handler_installed = installed,
    };
}

pub fn deinit(self: *Windows, _: std.mem.Allocator) void {
    self.restore();
    self.* = undefined;
}

/// `phase` is comptime so the body monomorphizes per call site.
/// Windows has no equivalent of POSIX VMIN/VTIME -- both phases set
/// identical mode bits; probe-vs-interactive timing folds into the
/// caller's read loop. Kept in the signature for API parity with
/// `Posix.setRawMode`.
pub fn setRawMode(self: *Windows, comptime phase: enum { probe, interactive }) Error!void {
    assert(live);
    _ = phase;

    const new_input = (self.original_input_mode &
        ~(ENABLE_PROCESSED_INPUT | ENABLE_LINE_INPUT | ENABLE_ECHO_INPUT)) |
        ENABLE_VIRTUAL_TERMINAL_INPUT;
    if (SetConsoleMode(self.stdin_handle, new_input) == .FALSE) return error.SetConsoleModeFailed;

    const new_output = self.original_output_mode |
        ENABLE_PROCESSED_OUTPUT |
        windows.ENABLE_VIRTUAL_TERMINAL_PROCESSING;
    if (SetConsoleMode(self.stdout_handle, new_output) == .FALSE) return error.SetConsoleModeFailed;

    // UTF-8 output so renderers can emit multibyte sequences. A
    // legacy code page is harmless -- bytes still pass through.
    _ = SetConsoleOutputCP(CP_UTF8);
}

pub fn restore(self: *Windows) void {
    if (saved_input_mode) |m| _ = SetConsoleMode(self.stdin_handle, m);
    if (saved_output_mode) |m| _ = SetConsoleMode(self.stdout_handle, m);
    if (saved_codepage) |cp| _ = SetConsoleOutputCP(cp);
    saved_input_mode = null;
    saved_output_mode = null;
    saved_codepage = null;
    if (self.ctrl_handler_installed) {
        _ = SetConsoleCtrlHandler(onCtrlEvent, .FALSE);
        self.ctrl_handler_installed = false;
    }
    live = false;
}

pub fn read(self: *Windows, buf: []u8) Error!usize {
    assert(buf.len > 0);
    var n: Dword = 0;
    if (ReadFile(self.stdin_handle, buf.ptr, @intCast(buf.len), &n, null) == .FALSE) {
        return error.ReadFailed;
    }
    return @intCast(n);
}

fn onCtrlEvent(_: Dword) callconv(.winapi) Bool {
    if (saved_input_mode) |m| _ = SetConsoleMode(saved_stdin, m);
    if (saved_output_mode) |m| _ = SetConsoleMode(saved_stdout, m);
    if (saved_codepage) |cp| _ = SetConsoleOutputCP(cp);
    return .FALSE;
}

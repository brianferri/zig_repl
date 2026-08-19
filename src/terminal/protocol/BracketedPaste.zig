//! Bracketed-paste protocol (DECSET 2004): pasted text arrives framed as
//! `CSI 200 ~ <bytes> CSI 201 ~`, and bytes between the markers are literal even
//! when they look like escape sequences. Stateful -- from `CSI 200 ~` onward
//! every token's bytes are accumulated and claimed via `Result.consumed` so no
//! other protocol interprets keystrokes inside the paste, until `CSI 201 ~`
//! emits one `Event.paste`. Storage is a fixed file-scope buffer; pastes past
//! the cap are silently truncated, and static storage keeps `known_protocols` a
//! `const` with no allocator threading.

const std = @import("std");
const assert = std.debug.assert;
const Protocol = @import("../Protocol.zig");
const Standard = @import("../Standard.zig");

const Event = @import("device").Event;
const Csi = @import("../standard/Csi.zig");

const BracketedPaste = @This();

const paste_buffer_bytes: u32 = 64 * 1024;

interface: Protocol = .{
    .name = "bracketedPaste",
    .query_sequence = "",
    .setup_sequence = "\x1b[?2004h",
    .teardown_sequence = "\x1b[?2004l",
    .vtable = &.{
        .tryInterpret = vtableTryInterpret,
        .detectSupport = Protocol.alwaysSupported,
    },
},
storage: [paste_buffer_bytes]u8 = @splat(0),
len: u32 = 0,
in_paste: bool = false,

pub var instance: BracketedPaste = .{};

pub fn protocol() *Protocol {
    return &instance.interface;
}

fn vtableTryInterpret(p: *Protocol, token: Standard.Token) Protocol.Result {
    const self: *BracketedPaste = @fieldParentPtr("interface", p);
    assert(@intFromPtr(self) == @intFromPtr(&instance));
    return self.handle(token);
}

fn handle(self: *BracketedPaste, token: Standard.Token) Protocol.Result {
    assert(self.len <= paste_buffer_bytes);
    if (!self.in_paste) {
        if (isPasteStart(token)) {
            self.in_paste = true;
            self.len = 0;
            return .consumed;
        }
        return .not_mine;
    }
    if (isPasteEnd(token)) {
        self.in_paste = false;
        return .{ .event = .{ .paste = self.storage[0..self.len] } };
    }
    self.append(token);
    return .consumed;
}

fn isPasteStart(token: Standard.Token) bool {
    return matchCsiPaste(token, 200);
}

fn isPasteEnd(token: Standard.Token) bool {
    return matchCsiPaste(token, 201);
}

fn matchCsiPaste(token: Standard.Token, param: u32) bool {
    if (token != .csi) return false;
    const csi = token.csi;
    if (csi.final != '~') return false;
    if (csi.intermediates_count != 0) return false;
    return csi.params_count >= 1 and csi.params[0] == param;
}

fn append(self: *BracketedPaste, token: Standard.Token) void {
    assert(self.in_paste);
    switch (token) {
        .ground => |b| self.pushByte(b),
        // Escape sequences inside a paste are literal; rebuild the on-the-wire
        // form so the editor sees exactly what was pasted.
        .csi => |csi| self.reconstructCsi(csi),
        .ss3 => |ss3| {
            self.pushBytes("\x1bO");
            self.pushByte(ss3.final);
        },
        .escape_alt => |b| {
            self.pushByte(0x1b);
            self.pushByte(b);
        },
        .bare_escape => self.pushByte(0x1b),
        .osc => |bytes| {
            self.pushBytes("\x1b]");
            self.pushBytes(bytes);
            self.pushByte(0x07);
        },
    }
}

fn pushByte(self: *BracketedPaste, b: u8) void {
    assert(self.len <= paste_buffer_bytes);
    if (self.len >= paste_buffer_bytes) return;
    self.storage[self.len] = b;
    self.len += 1;
}

fn pushBytes(self: *BracketedPaste, bytes: []const u8) void {
    assert(self.len <= paste_buffer_bytes);
    for (bytes) |b| self.pushByte(b);
}

fn reconstructCsi(self: *BracketedPaste, csi: Csi.Sequence) void {
    assert(Csi.isFinal(csi.final));
    assert(csi.params_count <= Csi.max_params);
    self.pushBytes("\x1b[");
    var num_buf: [10]u8 = undefined;
    var i: u32 = 0;
    while (i < csi.params_count) : (i += 1) {
        if (i > 0) self.pushByte(';');
        self.pushNumber(csi.params[i], &num_buf);
        var s: u32 = 0;
        while (s < csi.subparams_count[i]) : (s += 1) {
            self.pushByte(':');
            self.pushNumber(csi.subparams[i][s], &num_buf);
        }
    }
    self.pushBytes(csi.intermediates[0..csi.intermediates_count]);
    self.pushByte(csi.final);
}

fn pushNumber(self: *BracketedPaste, n: u32, num_buf: []u8) void {
    assert(num_buf.len >= 10); // "4294967295" fits any u32
    const slice = std.fmt.bufPrint(num_buf, "{d}", .{n}) catch return;
    self.pushBytes(slice);
}

test "bracketedPaste: start + middle + end emits one paste event" {
    instance = .{};

    var start: Csi.Sequence = .{ .final = '~' };
    start.params[0] = 200;
    start.params_count = 1;
    try std.testing.expect(instance.handle(.{ .csi = start }) == .consumed);

    try std.testing.expect(instance.handle(.{ .ground = 'h' }) == .consumed);
    try std.testing.expect(instance.handle(.{ .ground = 'i' }) == .consumed);

    var end: Csi.Sequence = .{ .final = '~' };
    end.params[0] = 201;
    end.params_count = 1;
    const r = instance.handle(.{ .csi = end });
    try std.testing.expect(r == .event);
    try std.testing.expectEqualStrings("hi", r.event.paste);
}

test "bracketedPaste: ignored when not in a paste" {
    instance = .{};
    try std.testing.expect(instance.handle(.{ .ground = 'a' }) == .not_mine);
}

test "bracketedPaste: embedded CSI sequence preserved as bytes" {
    instance = .{};
    var start: Csi.Sequence = .{ .final = '~' };
    start.params[0] = 200;
    start.params_count = 1;
    _ = instance.handle(.{ .csi = start });

    var embedded: Csi.Sequence = .{ .final = 'A' };
    embedded.params[0] = 1;
    embedded.params[1] = 5;
    embedded.params_count = 2;
    _ = instance.handle(.{ .csi = embedded });

    var end: Csi.Sequence = .{ .final = '~' };
    end.params[0] = 201;
    end.params_count = 1;
    const r = instance.handle(.{ .csi = end });
    try std.testing.expectEqualStrings("\x1b[1;5A", r.event.paste);
}

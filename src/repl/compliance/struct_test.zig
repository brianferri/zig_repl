const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @offsetOf and @bitOffsetOf report field layout" {
    try compliance.check(a, &.{
        .{ .src = &.{"@offsetOf(extern struct { a: u8, b: u32 }, \"b\")"}, .want = compliance.want(@offsetOf(extern struct { a: u8, b: u32 }, "b")) },
        .{ .src = &.{"@offsetOf(struct { a: u8, b: u32 }, \"b\")"}, .want = compliance.want(@offsetOf(struct { a: u8, b: u32 }, "b")) },
        .{ .src = &.{"@bitOffsetOf(packed struct { a: u4, b: u4 }, \"b\")"}, .want = compliance.want(@bitOffsetOf(packed struct { a: u4, b: u4 }, "b")) },
        .{ .src = &.{"@bitOffsetOf(packed struct { a: u1, b: u3, c: u4 }, \"c\")"}, .want = compliance.want(@bitOffsetOf(packed struct { a: u1, b: u3, c: u4 }, "c")) },
        .{ .src = &.{"@bitOffsetOf(extern struct { a: u8, b: u32 }, \"b\")"}, .want = compliance.want(@bitOffsetOf(extern struct { a: u8, b: u32 }, "b")) },
    });
}

test "compliance: anonymous struct (.{ .a = ... }) field access" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const p = .{ .a = 1, .b = 2 }; break :blk p.a + p.b; }"},
            .want = compliance.want(blk: {
                const p = .{ .a = 1, .b = 2 };
                break :blk p.a + p.b;
            }),
        },
        // Anon struct fields are all comptime, so the type carries no runtime layout (size 0).
        // Exercises resolveStructLayout on a reified struct that has field defaults.
        .{ .src = &.{"@sizeOf(@TypeOf(.{ .a = 1, .b = 2 }))"}, .want = compliance.want(@sizeOf(@TypeOf(.{ .a = 1, .b = 2 }))) },
        .{
            .src = &.{"blk: { const p = .{ .x = @as(u8, 5), .y = true }; break :blk p.x; }"},
            .want = compliance.want(blk: {
                const p = .{ .x = @as(u8, 5), .y = true };
                break :blk p.x;
            }),
        },
        .{
            .src = &.{"blk: { const p = .{ .x = @as(u8, 5), .z = .{ .w = 3 } }; break :blk p.x + p.z.w; }"},
            .want = compliance.want(blk: {
                const p = .{ .x = @as(u8, 5), .z = .{ .w = 3 } };
                break :blk p.x + p.z.w;
            }),
        },
        .{
            .src = &.{"blk: { const p = .{ .a = 1, .b = 2 }; const q = &p.b; break :blk q.*; }"},
            .want = compliance.want(blk: {
                const p = .{ .a = 1, .b = 2 };
                const q = &p.b;
                break :blk q.*;
            }),
        },
        .{
            .src = &.{ "const anon = .{ .a = 10, .b = 20 };", "anon.a + anon.b" },
            .want = compliance.want(blk: {
                const anon = .{ .a = 10, .b = 20 };
                break :blk anon.a + anon.b;
            }),
        },
        .{
            .src = &.{"blk: { const T = @TypeOf(.{ .a = 1, .b = 2 }); break :blk @hasField(T, \"b\"); }"},
            .want = compliance.want(blk: {
                const T = @TypeOf(.{ .a = 1, .b = 2 });
                break :blk @hasField(T, "b");
            }),
        },
        .{
            .src = &.{"blk: { const T = @TypeOf(.{ .a = 1 }); break :blk @hasField(T, \"c\"); }"},
            .want = compliance.want(blk: {
                const T = @TypeOf(.{ .a = 1 });
                break :blk @hasField(T, "c");
            }),
        },
        .{
            .src = &.{"blk: { const T = @TypeOf(.{ .a = 1 }); break :blk @hasField(T, \"a\"); }"},
            .want = compliance.want(blk: {
                const T = @TypeOf(.{ .a = 1 });
                break :blk @hasField(T, "a");
            }),
        },
        .{
            .src = &.{"blk: { const T = @TypeOf(.{ 10, 20 }); break :blk @hasField(T, \"a\"); }"},
            .want = compliance.want(blk: {
                const T = @TypeOf(.{ 10, 20 });
                break :blk @hasField(T, "a");
            }),
        },
        .{
            .src = &.{"blk: { const p = .{ .a = 1 }; break :blk p.missing; }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const p = .{ .a = 1, .a = 2 }; break :blk p.a; }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const p = .{ .a = 1 }; const q = &p.a; q.* = 5; break :blk q.*; }"},
            .reject = true,
        },
    });
}

// An anon literal is comptime-known, so `&anon.field` points to a comptime field; a
// global holding that pointer is rejected by the compiler ("global variable contains
// reference to comptime var"). The comptime-only REPL has no runtime-escape notion, so
// it reads the field -- a deliberate divergence, pinned with `.rendered`.
test "divergence: global pointer to a comptime anon-struct field" {
    try compliance.check(a, &.{
        .{
            .src = &.{ "const anon = .{ .m = 7, .n = 8 };", "const r = &anon.n;", "r.*" },
            .rendered = "8",
        },
        .{
            .src = &.{ "const anon = .{ .m = @as(u8, 7), .n = @as(u8, 8) };", "const r = &anon.n;", "r.*" },
            .rendered = "8",
        },
    });
}

test "compliance: struct init and field access" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { a: u8, b: u16 }; const p: P = .{ .b = 8, .a = 7 }; break :blk p.a; }"},
            .want = compliance.want(blk: {
                const P = struct { a: u8, b: u16 };
                const p: P = .{ .b = 8, .a = 7 };
                break :blk p.a;
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { a: u8, b: u16 }; const p: P = .{ .b = 8, .a = 7 }; break :blk p.b; }"},
            .want = compliance.want(blk: {
                const P = struct { a: u8, b: u16 };
                const p: P = .{ .b = 8, .a = 7 };
                break :blk p.b;
            }),
        },
        .{
            .src = &.{"blk: { const Q = struct { x: u32, y: u32 }; const q: Q = .{ .x = 10, .y = 32 }; break :blk q.x + q.y; }"},
            .want = compliance.want(blk: {
                const Q = struct { x: u32, y: u32 };
                const q: Q = .{ .x = 10, .y = 32 };
                break :blk q.x + q.y;
            }),
        },
        .{
            .src = &.{"blk: { const R = struct { a: u8 }; const r: R = .{ .a = 250 }; break :blk r.a + 5; }"},
            .want = compliance.want(blk: {
                const R = struct { a: u8 };
                const r: R = .{ .a = 250 };
                break :blk r.a + 5;
            }),
        },
        // An omitted default is stored through the field pointer; when the init target is
        // itself a field (a nested init), that pointer's base is not a comptime alloc.
        .{
            .src = &.{"blk: { const Inner = struct { x: u8, y: u8 = 9 }; const Outer = struct { inner: Inner, z: u8 = 3 }; const o: Outer = .{ .inner = .{ .x = 1 } }; break :blk o.inner.y + o.z; }"},
            .want = compliance.want(blk: {
                const Inner = struct { x: u8, y: u8 = 9 };
                const Outer = struct { inner: Inner, z: u8 = 3 };
                const o: Outer = .{ .inner = .{ .x = 1 } };
                break :blk o.inner.y + o.z;
            }),
        },
    });
}

// A comptime field is never written through its (standalone) comptime-field pointer, so a mutable
// variable's storage never holds it; the value is read from the type default, and a whole-value
// materialization carries it -- the compiler guarantees a struct value is complete.
test "compliance: a comptime struct field survives a mutable variable" {
    const S = "const S = struct { comptime x: u32 = 7, y: u32 = 0 };";
    try compliance.check(a, &.{
        .{ .src = &.{ S, "blk: { var s: S = .{ .y = 3 }; s.y = 5; break :blk s.x; }" }, .want = compliance.want(@as(u32, 7)) },
        .{ .src = &.{ S, "blk: { var s: S = .{ .y = 3 }; s.y = 5; break :blk s.x + s.y; }" }, .want = compliance.want(@as(u32, 12)) },
        .{ .src = &.{ S, "blk: { var s: S = .{ .y = 3 }; s.y = 5; const t = s; break :blk t.x; }" }, .want = compliance.want(@as(u32, 7)) },
        .{ .src = &.{ S, "blk: { var s: S = .{ .y = 3 }; s.y = 5; break :blk s; }" }, .rendered = ".{ .x = 7, .y = 5 }" },
    });
}

test "compliance: a struct type exposes its member declarations (P.decl)" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { fn id(v: u8) u8 { return v; } }; break :blk @TypeOf(P.id); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    fn id(v: u8) u8 {
                        return v;
                    }
                };
                break :blk @TypeOf(P.id);
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { const K: u8 = 5; }; break :blk P.K; }"},
            .want = compliance.want(blk: {
                const P = struct {
                    const K: u8 = 5;
                };
                break :blk P.K;
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { const K: u8 = 5; }; break :blk P.K + 1; }"},
            .want = compliance.want(blk: {
                const P = struct {
                    const K: u8 = 5;
                };
                break :blk P.K + 1;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { const A = struct { const y: u8 = 5; }; }; break :blk S.A.y; }"},
            .want = compliance.want(blk: {
                const S = struct {
                    const A = struct {
                        const y: u8 = 5;
                    };
                };
                break :blk S.A.y;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { const A = struct { const B = struct { const z: u8 = 7; }; }; }; break :blk S.A.B.z; }"},
            .want = compliance.want(blk: {
                const S = struct {
                    const A = struct {
                        const B = struct {
                            const z: u8 = 7;
                        };
                    };
                };
                break :blk S.A.B.z;
            }),
        },
    });
}

test "compliance: calling a struct's namespace declaration (P.decl(args))" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { fn id(v: u8) u8 { return v; } }; break :blk P.id(7); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    fn id(v: u8) u8 {
                        return v;
                    }
                };
                break :blk P.id(7);
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { fn add(a2: u8, b: u8) u8 { return a2 + b; } }; break :blk P.add(40, 2); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    fn add(a2: u8, b: u8) u8 {
                        return a2 + b;
                    }
                };
                break :blk P.add(40, 2);
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { fn sq(x: u16) u16 { return x * x; } }; break :blk P.sq(9); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    fn sq(x: u16) u16 {
                        return x * x;
                    }
                };
                break :blk P.sq(9);
            }),
        },
    });
}

test "compliance: a struct value method binds the receiver (p.method())" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { x: u8, fn get(self: @This()) u8 { return self.x; } }; const p: P = .{ .x = 9 }; break :blk p.get(); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    x: u8,
                    fn get(self: @This()) u8 {
                        return self.x;
                    }
                };
                const p: P = .{ .x = 9 };
                break :blk p.get();
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { x: u8, fn addk(self: @This(), k: u8) u8 { return self.x + k; } }; const p: P = .{ .x = 10 }; break :blk p.addk(5); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    x: u8,
                    fn addk(self: @This(), k: u8) u8 {
                        return self.x + k;
                    }
                };
                const p: P = .{ .x = 10 };
                break :blk p.addk(5);
            }),
        },
        // A method whose receiver is already a pointer (`self: *T`) calls a sibling method on
        // that pointer; resolution peels the pointer to the container (the iterator pattern).
        .{
            .src = &.{"blk: { const P = struct { x: u8, fn peek(self: *@This()) u8 { return self.x; } fn next(self: *@This()) u8 { return self.peek(); } }; var p: P = .{ .x = 7 }; break :blk p.next(); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    x: u8,
                    fn peek(self: *@This()) u8 {
                        return self.x;
                    }
                    fn next(self: *@This()) u8 {
                        return self.peek();
                    }
                };
                var p: P = .{ .x = 7 };
                break :blk p.next();
            }),
        },
    });
}

test "compliance: a body resolves a bare sibling declaration in its container" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { a: u8, b: u8, fn sum2(x: u8, y: u8) u8 { return x + y; } fn total(self: @This()) u8 { return sum2(self.a, self.b); } }; const s: S = .{ .a = 20, .b = 22 }; break :blk s.total(); }"},
            .want = compliance.want(blk: {
                const S = struct {
                    a: u8,
                    b: u8,
                    fn sum2(x: u8, y: u8) u8 {
                        return x + y;
                    }
                    fn total(self: @This()) u8 {
                        return sum2(self.a, self.b);
                    }
                };
                const s: S = .{ .a = 20, .b = 22 };
                break :blk s.total();
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { fn a2() u8 { return 7; } fn b() u8 { return a2() + 1; } }; break :blk P.b(); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    fn a2() u8 {
                        return 7;
                    }
                    fn b() u8 {
                        return a2() + 1;
                    }
                };
                break :blk P.b();
            }),
        },
    });
}

test "compliance: a nested container resolves an enclosing container's decl" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { const x: u8 = 9; const A = struct { const y: u8 = x; }; }; break :blk S.A.y; }"},
            .want = compliance.want(blk: {
                const S = struct {
                    const x: u8 = 9;
                    const A = struct {
                        const y: u8 = x;
                    };
                };
                break :blk S.A.y;
            }),
        },
        .{
            .src = &.{"blk: { const Outer = struct { const shared: u8 = 42; const Inner = struct { fn get() u8 { return shared; } }; }; break :blk Outer.Inner.get(); }"},
            .want = compliance.want(blk: {
                const Outer = struct {
                    const shared: u8 = 42;
                    const Inner = struct {
                        fn get() u8 {
                            return shared;
                        }
                    };
                };
                break :blk Outer.Inner.get();
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { const k: u8 = 5; fn mk() type { return struct { const v: u8 = k; }; } }; break :blk S.mk().v; }"},
            .want = compliance.want(blk: {
                const S = struct {
                    const k: u8 = 5;
                    fn mk() type {
                        return struct {
                            const v: u8 = k;
                        };
                    }
                };
                break :blk S.mk().v;
            }),
        },
    });
}

test "compliance: declaration and field access do not cross" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { fn id(v: u8) u8 { return v; } }; break :blk P.nope; }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const P = struct { x: u8 }; break :blk P.x; }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const P = struct { x: u8, fn id(v: u8) u8 { return v; } }; const p: P = .{ .x = 1 }; break :blk p.id; }"},
            .reject = true,
        },
    });
}

test "compliance: struct field defaults and missing-field validation" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { a: u8, b: u16 = 99 }; const p: P = .{ .a = 7 }; break :blk p.b; }"},
            .want = compliance.want(blk: {
                const P = struct { a: u8, b: u16 = 99 };
                const p: P = .{ .a = 7 };
                break :blk p.b;
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { a: u8, b: u16 = 99 }; const p: P = .{ .a = 7, .b = 5 }; break :blk p.b; }"},
            .want = compliance.want(blk: {
                const P = struct { a: u8, b: u16 = 99 };
                const p: P = .{ .a = 7, .b = 5 };
                break :blk p.b;
            }),
        },
        .{
            .src = &.{"blk: { const Q = struct { a: u8, b: u16 }; const q: Q = .{ .a = 7 }; break :blk q.a; }"},
            .reject = true,
        },
    });
}

test "compliance: explicit-type struct init (T{ ... })" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { a: u8, b: u8 }; const s = S{ .a = 1, .b = 2 }; break :blk s.a + s.b; }"},
            .want = compliance.want(blk: {
                const S = struct { a: u8, b: u8 };
                const s = S{ .a = 1, .b = 2 };
                break :blk s.a + s.b;
            }),
        },
        .{
            .src = &.{"blk: { const D = struct { a: u8, b: u16 = 99 }; const d = D{ .a = 7 }; break :blk d.b; }"},
            .want = compliance.want(blk: {
                const D = struct { a: u8, b: u16 = 99 };
                const d = D{ .a = 7 };
                break :blk d.b;
            }),
        },
        .{
            .src = &.{"blk: { const E = struct { a: u8 = 3, b: u8 = 4 }; const e = E{}; break :blk e.a + e.b; }"},
            .want = compliance.want(blk: {
                const E = struct { a: u8 = 3, b: u8 = 4 };
                const e = E{};
                break :blk e.a + e.b;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { a: u8, b: u8 }; break :blk (S{ .a = 5, .b = 6 }).b; }"},
            .want = compliance.want(blk: {
                const S = struct { a: u8, b: u8 };
                break :blk (S{ .a = 5, .b = 6 }).b;
            }),
        },
        .{
            .src = &.{"blk: { const S = struct { a: u8, b: u8 }; const s = S{ .a = 1 }; break :blk s.a; }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const Q = struct { a: u8 }; const q = Q{ .a = 1, .b = 2 }; break :blk q.a; }"},
            .reject = true,
        },
        .{
            .src = &.{"blk: { const Q = struct { a: u8 }; const q = Q{ .a = 300 }; break :blk q.a; }"},
            .reject = true,
        },
        // The type position of `T{}` must be a type; a value there is rejected,
        // not passed on to a layout query.
        .{
            .src = &.{"blk: { const x = 5; break :blk x{}; }"},
            .reject = true,
        },
    });
}

test "compliance: field pointers (&x.field and chained access)" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { x: u8, y: u8 }; var p: P = .{ .x = 7, .y = 8 }; const px = &p.x; break :blk px.*; }"},
            .want = compliance.want(blk: {
                const P = struct { x: u8, y: u8 };
                var p: P = .{ .x = 7, .y = 8 };
                const px = &p.x;
                break :blk px.*;
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { x: u8, y: u8 }; var p: P = .{ .x = 7, .y = 8 }; const px = &p.x; px.* = 20; break :blk p.x; }"},
            .want = compliance.want(blk: {
                const P = struct { x: u8, y: u8 };
                var p: P = .{ .x = 7, .y = 8 };
                const px = &p.x;
                px.* = 20;
                break :blk p.x;
            }),
        },
        .{
            .src = &.{ "const P = struct { x: u8, y: u8 };", "const Line = struct { a: P, b: P };", "const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } };", "l.a.x + l.b.y" },
            .want = compliance.want(blk: {
                const P = struct { x: u8, y: u8 };
                const Line = struct { a: P, b: P };
                const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } };
                break :blk l.a.x + l.b.y;
            }),
        },
        .{
            .src = &.{ "const P = struct { x: u8, y: u8, fn sum(self: @This()) u8 { return self.x + self.y; } };", "const Line = struct { a: P, b: P };", "const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } };", "l.a.sum() + l.b.sum()" },
            .want = compliance.want(blk: {
                const P = struct {
                    x: u8,
                    y: u8,
                    fn sum(self: @This()) u8 {
                        return self.x + self.y;
                    }
                };
                const Line = struct { a: P, b: P };
                const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } };
                break :blk l.a.sum() + l.b.sum();
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { x: u8 }; const p: P = .{ .x = 9 }; const px = &p.x; px.* = 1; break :blk p.x; }"},
            .reject = true,
        },
    });
}

test "compliance: a member body takes the address of a sibling declaration" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const S = struct { const k: u8 = 7; fn go() u8 { const p = &k; return p.*; } }; break :blk S.go(); }"},
            .want = compliance.want(blk: {
                const S = struct {
                    const k: u8 = 7;
                    fn go() u8 {
                        const p = &k;
                        return p.*;
                    }
                };
                break :blk S.go();
            }),
        },
    });
}

test "compliance: nested struct types capture an enclosing local (closure_get)" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const P = struct { x: u8 }; const W = struct { p: P }; const w = W{ .p = P{ .x = 42 } }; break :blk w.p.x; }"},
            .want = compliance.want(blk: {
                const P = struct { x: u8 };
                const W = struct { p: P };
                const w = W{ .p = P{ .x = 42 } };
                break :blk w.p.x;
            }),
        },
        .{
            .src = &.{"blk: { const T = u16; const Box = struct { v: T }; const b = Box{ .v = 500 }; break :blk b.v; }"},
            .want = compliance.want(blk: {
                const T = u16;
                const Box = struct { v: T };
                const b = Box{ .v = 500 };
                break :blk b.v;
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { x: u8 }; const N = struct { inner: P }; const M = struct { mid: N }; const m = M{ .mid = N{ .inner = P{ .x = 7 } } }; break :blk m.mid.inner.x; }"},
            .want = compliance.want(blk: {
                const P = struct { x: u8 };
                const N = struct { inner: P };
                const M = struct { mid: N };
                const m = M{ .mid = N{ .inner = P{ .x = 7 } } };
                break :blk m.mid.inner.x;
            }),
        },
        .{
            .src = &.{"blk: { const P = struct { x: u8, y: u8, fn sum(self: @This()) u8 { return self.x + self.y; } }; const Line = struct { a: P, b: P }; const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } }; break :blk l.a.sum() + l.b.sum(); }"},
            .want = compliance.want(blk: {
                const P = struct {
                    x: u8,
                    y: u8,
                    fn sum(self: @This()) u8 {
                        return self.x + self.y;
                    }
                };
                const Line = struct { a: P, b: P };
                const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } };
                break :blk l.a.sum() + l.b.sum();
            }),
        },
    });
}

test "compliance: a struct type declared inside a function body" {
    try compliance.check(a, &.{
        .{
            .src = &.{ "fn mk() type { return struct { v: u8 }; }", "const m: mk() = .{ .v = 5 };", "m.v" },
            .want = compliance.want(blk: {
                const mk = struct {
                    fn mk() type {
                        return struct { v: u8 };
                    }
                }.mk;
                const m: mk() = .{ .v = 5 };
                break :blk m.v;
            }),
        },
        .{
            .src = &.{ "fn Box(comptime T: type) type { return struct { v: T }; }", "const b: Box(u16) = .{ .v = 500 };", "b.v" },
            .want = compliance.want(blk: {
                const Box = struct {
                    fn Box(comptime T: type) type {
                        return struct { v: T };
                    }
                }.Box;
                const b: Box(u16) = .{ .v = 500 };
                break :blk b.v;
            }),
        },
        .{
            .src = &.{ "fn Box(comptime T: type) type { return struct { v: T }; }", "const p: Box(u8) = .{ .v = 1 };", "const q: Box(u16) = .{ .v = 500 };", "q.v" },
            .want = compliance.want(blk: {
                const Box = struct {
                    fn Box(comptime T: type) type {
                        return struct { v: T };
                    }
                }.Box;
                const p: Box(u8) = .{ .v = 1 };
                _ = p;
                const q: Box(u16) = .{ .v = 500 };
                break :blk q.v;
            }),
        },
    });
}

test "named struct renders with the session-qualified `repl.` prefix" {
    try compliance.check(a, &.{
        .{
            .src = &.{ "const P = struct { x: i32 };", "P" },
            .rendered = "repl.P",
        },
        .{
            .src = &.{ "const P = struct { x: i32 };", "*P" },
            .rendered = "*repl.P",
        },
    });
}

test "compliance: methods compose -- call each other and take struct args" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const V = struct { n: u8, fn base(self: @This()) u8 { return self.n; } fn p1(self: @This()) u8 { return self.base() + 1; } fn p2(self: @This()) u8 { return self.p1() + 1; } }; const v: V = .{ .n = 40 }; break :blk v.p2(); }"}, .want = compliance.want(blk: {
            const V = struct {
                n: u8,
                fn base(self: @This()) u8 {
                    return self.n;
                }
                fn p1(self: @This()) u8 {
                    return self.base() + 1;
                }
                fn p2(self: @This()) u8 {
                    return self.p1() + 1;
                }
            };
            const v: V = .{ .n = 40 };
            break :blk v.p2();
        }) },
        .{ .src = &.{"blk: { const Vec = struct { x: u8, y: u8, fn dot(self: @This(), o: @This()) u8 { return self.x * o.x + self.y * o.y; } }; const p: Vec = .{ .x = 2, .y = 3 }; const q: Vec = .{ .x = 4, .y = 5 }; break :blk p.dot(q); }"}, .want = compliance.want(blk: {
            const Vec = struct {
                x: u8,
                y: u8,
                fn dot(self: @This(), o: @This()) u8 {
                    return self.x * o.x + self.y * o.y;
                }
            };
            const p: Vec = .{ .x = 2, .y = 3 };
            const q: Vec = .{ .x = 4, .y = 5 };
            break :blk p.dot(q);
        }) },
    });
}

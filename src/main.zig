const std = @import("std");
const ArrayList = std.ArrayList;
const Allocator = std.mem.Allocator;

const syms_txt = @embedFile("resources/symbols.txt");
const precs_txt = @embedFile("resources/precedence.txt");

// Hilariously, all the stuff below is initalization stuff. This was easier in Rust/Nim since it's mostly filtering strings/arrays at comptime, which is a lot easier to express with FPisms

const syms: []const []const u8 = collectTokenize(u8, syms_txt, '\n');

const wspaces = blk: {
    const z = collectTokenize(u8, syms[2], ',');
    var res: [z.len]u8 = undefined;

    for (0..z.len) |i| {
        res[i] = z[i][0];
    }

    break :blk res;
};

const punc = blk: {
    const z = collectTokenize(u8, syms[0], ',');
    var res: [z.len + 1]u8 = undefined;

    for (0..z.len) |i| {
        res[i] = z[i][0];
    }
    res[z.len] = ',';

    break :blk res;
};

const end_word = [_]u8{','} ++ wspaces;
const pref_ops = blk: {
    const z = collectTokenize(u8, syms[4], ',');
    var res: [z.len]u8 = undefined;

    for (0..z.len) |i| {
        res[i] = z[i][0];
    }

    break :blk res;
};

const ops = blk: {
    const z = collectTokenize(u8, replaceRet(u8, precs_txt, &[_]u8{'\n'}, &[_]u8{','}), ',');

    var res: [z.len]u8 = undefined;

    for (0..z.len) |i| {
        res[i] = z[i][0];
    }

    break :blk res;
};

const lex_stop = blk: {
    const a = &[_]u8{ ',', '\n' };
    const b = blk1: {
        const z = collectTokenize(u8, syms[1], ',');
        var resb: [z.len]u8 = undefined;

        for (0..z.len) |i| {
            resb[i] = z[i][0];
        }

        break :blk1 resb;
    };

    break :blk a ++ b ++ ops ++ pref_ops;
};

fn collectTokenize(comptime T: type, inp: []const T, sptor: T) []const []const T { // Doesn't work properly if T is an array type
    var res: []const []const T = &[_]([]const T){};

    var spl_It = std.mem.tokenize(T, inp, &[_]T{sptor});

    while (spl_It.next()) |s| {
        res = res ++ .{s};
    }

    return res;
}

fn replaceRet(comptime T: type, haystack: []const T, needle: []const T, new_needle: []const T) []const T {
    var res: [std.mem.replacementSize(T, haystack, needle, new_needle)]T = undefined;
    _ = std.mem.replace(T, haystack, needle, new_needle, &res);
    return &res;
}

fn precs(u: u8) !u8 {
    return switch (u) {
        '^' => 3,
        '*', '/' => 2,
        '%', '\'' => 1,
        '+', '-' => 0,
        else => error.InvalidOperator,
    };
}

fn contains(comptime T: type, haystack: []T, needle: T) bool {
    for (haystack) |e| {
        if (e == needle) {
            return true;
        }
    }
    return false;
}

fn constContains(comptime T: type, haystack: []const T, needle: T) bool {
    for (haystack) |e| {
        if (e == needle) {
            return true;
        }
    }
    return false;
}

// Rewriting the parser completely:

// The details are in the Notes

// We'll structure it by having one main "entrypoint" function, parseExpr, and see what happens from there

pub const TKind = enum {
    IntLit,
    FloatLit,
    Ident,
    WSpace,
    StrLit,
    Punc,
    Op,
    PrefOp,

    pub fn format(self: TKind, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = fmt;
        _ = options;

        const name: []const u8 = switch (self) {
            TKind.IntLit => "IntLit",
            TKind.FloatLit => "FloatLit",
            TKind.Ident => "Ident",
            TKind.WSpace => "WSpace",
            TKind.StrLit => "StrLit",
            TKind.Punc => "Punc",
            TKind.Op => "Op",
            TKind.PrefOp => "PrefOp",
        };

        try writer.print("{s}", .{name});
    }
};

pub const Token = struct {
    kind: TKind,
    val: []const u8,

    pub fn format(self: Token, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = fmt;
        _ = options;

        if (self.val.len == 0) {
            try writer.print("{} Empty", .{self.kind});
        } else {
            try writer.print("{} {s}", .{ self.kind, self.val });
        }
    }
};

pub const Parser = struct {
    syms: []const u8,
    wspaces: []const u8,
    punc: []const u8,
    end_word: []const u8,
    pref_ops: []const u8,
    ops: []const u8,

    inp: []const u8,
    lx: []const Token,
};

pub const NKind = enum {
    Int, Float, Str, Ident, Call,
};

pub const ASTNode = struct {
    kind : NKind = undefined,
    val: union(enum) {
        nval: union(enum) {
            ival: i32,
            fval: f32,
        },
        sval: []const u8,
    },
    kids: ArrayList(*ASTNode) = undefined,
    allocator: Allocator = undefined,

    pub fn init(self : *ASTNode, allocator : Allocator) void {
        self.allocator = allocator;
        self.kids = ArrayList(*ASTNode).init(self.allocator);
    }
    
    pub fn append(self: ASTNode, n: ASTNode) !ASTNode {
        self.kids.append(n);
        return self.kids[self.kids.len - 1];
    }

    pub fn parseToken(t : Token, allocator : Allocator) !ASTNode {
        var res = switch (t.kind) {
            TKind.FloatLit => ASTNode { .kind = NKind.Float, .val = .{ .nval = .{ .fval = try std.fmt.parseFloat(f32, t.val) } } },
            
            TKind.IntLit => ASTNode { .kind = NKind.Int, .val = .{ .nval = .{ .ival = try std.fmt.parseInt(i32, t.val, 10) } } },
            
            TKind.Ident => ASTNode { .kind = NKind.Ident, .val = .{ .sval = t.val } },
            
            TKind.Op => ASTNode { .kind = NKind.Call, .val = .{ .sval = t.val } },
            
            TKind.PrefOp => ASTNode { .kind = NKind.Call, .val = .{ .sval = t.val } },
            
            TKind.Punc => null,
            
            TKind.StrLit => ASTNode { .kind = NKind.Str, .val = .{ .sval = t.val[1..t.val.len - 1] } },
            
            TKind.WSpace => null
        };

        try res.init(allocator);
        return res;
    }
        
    pub fn parseExpr(self: *ASTNode, r: []const Token, allocator: Allocator) !void {
        var expr: []const []const Token = undefined;
        _ = self;

        if (std.mem.eql(u8, r[0].val, "(") and std.mem.eql(u8, r[r.len - 1].val, ")")) {
            expr = try sep(r[1 .. r.len - 1], allocator);
        } else {
            expr = try sep(r, allocator);
        }

        var op_st = ArrayList(Token).init(allocator);
        defer op_st.deinit();
        var out_st = ArrayList(?[]const Token).init(allocator); // Null means that we should look at app_after
        defer out_st.deinit();

        var app_after = ArrayList(*ASTNode).init(allocator);
        defer app_after.deinit();

        for (expr) |clmp| {
            if (clmp.len == 1 and clmp[0].kind == TKind.Op) {
                if (try precs(clmp[0].val[0]) < try precs(clmp[clmp.len - 1].val[0])) {

                    var op_n = try parseToken(clmp[0], allocator);
                    op_n.parseExpr(out_st[out_st.len - 1]);
                    op_n.parseExpr(out_st[out_st.len - 1]);
                    try app_after.append(&op_n);
                    try out_st.append(null);
                    
                } else {
                    try op_st.append(clmp[0]);
                }
            } else {
                try out_st.append(clmp);
            }
        }

        while (op_st.len > 0) {
            
            for (0..2) |_| {

                if (out_st[out_st.len - 1] == null) {
                    op_st[op_st.len - 1].kids.append(app_after.pop());
                    _ = out_st.pop();
                } else {
                    op_st[op_st.len - 1].parseExpr(out_st.pop().?);
                }
            }

            out_st.append(null);
            app_after.append(op_st.pop());
        }
    }

    pub fn print(n : ASTNode, d : u16) void {
        for (0..d) |_| {
            std.debug.print("    ", .{});
        }

        std.debug.print("{}", .{n});

        for (n.kids) |kid| {
            kid.print(d + 1);
        }
    }
};


pub fn partFile(inp: []const u8, allocator: Allocator) ![]const []const u8 {
    var result = ArrayList([]const u8).init(allocator);
    defer result.deinit();

    var st: u32 = 0;

    for (inp, 0..) |c, i| {
        if (constContains(u8, lex_stop, c)) {
            if (st != i) {
                try result.append(inp[st..i]);
            }
            // checking that nothing too insane is occuring
            if (st > i) {
                unreachable;
            }
            try result.append(inp[i .. i + 1]);
            st = @truncate(u32, i + 1);
        }
    }

    if (st < inp.len and !constContains(u8, lex_stop, inp[st])) {
        try result.append(inp[st..]);
    }

    return result.toOwnedSlice();
}

pub fn lex(inp: []const []const u8, allocator: Allocator) ![]const Token {
    var result = ArrayList(Token).init(allocator);

    for (0..inp.len) |i| {
        if ('0' <= inp[i][0] and inp[i][0] <= '9') {
            if (constContains(u8, inp[i], '.')) {
                try result.append(Token{ .kind = TKind.FloatLit, .val = inp[i] });
            } else {
                try result.append(Token{ .kind = TKind.IntLit, .val = inp[i] });
            }
        } else if (inp[i][0] == '\"' and inp[i][inp[i].len - 1] == '\"') {
            try result.append(Token{ .kind = TKind.StrLit, .val = inp[i][1..inp.len] });
        } else if (constContains(u8, &punc, inp[i][0])) {
            try result.append(Token{ .kind = TKind.Punc, .val = inp[i] });
        } else if (constContains(u8, &ops, inp[i][0])) {
            try result.append(Token{ .kind = TKind.Op, .val = inp[i] });
        } else if (constContains(u8, &pref_ops, inp[i][0])) {
            try result.append(Token{ .kind = TKind.PrefOp, .val = inp[i] });
        } else if (!constContains(u8, &wspaces, inp[i][0])) {
            try result.append(Token{ .kind = TKind.Ident, .val = inp[i] });
        }
    }

    return result.toOwnedSlice();
}

pub fn sep(inp: []const Token, allocator: Allocator) ![]const []const Token { // Free the returned value, heap allocator
    var res = ArrayList([]const Token).init(allocator);

    var st: u32 = 0;
    for (inp, 0..) |tk, i| {
        if (constContains(u8, lex_stop, tk.val[0])) {
            try res.append(inp[st .. i + 1]);
            try res.append(inp[i + 1 .. i + 2]);
        }
    }

    return res.toOwnedSlice();
}

pub fn main() !void {
}

test "comptime arrays" {
    std.debug.print("{s}\n{d}\n{s}\n{d}\n{s}\n{s}\n", .{ syms, wspaces, punc, end_word, pref_ops, ops });
}

test "Token" {
    const inp = "shjadjsakdjsajdlskjalkdsjads\n".*;
    const tkn = Token{
        .kind = TKind.IntLit,
        .val = inp[0..3],
    };
    std.debug.print("{}\n", .{tkn});
}

test "lex and partFile and parseExpr" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const gpallocator = gpa.allocator();

    var inp = "x*8 + 81*x^3 + 10*x^2";

    const pf = try partFile(inp, gpallocator);
    defer gpallocator.free(pf);
    const slc = try lex(pf, gpallocator);
    defer gpallocator.free(slc);
    var rt = ASTNode { .val = .{ .sval = "" } };
    rt.init(gpallocator);
    try rt.parseExpr(slc, gpallocator);
    std.debug.print("{s} =>\n", .{pf});
    std.debug.print("{s}", .{slc});
    rt.print(0);
}

const std = @import("std");
const ArrayList = std.ArrayList;
const Allocator = std.mem.Allocator;

var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const gpallocator = gpa.allocator();

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
    const a = &[_]u8{',', '\n'};
    const b = blk1: {
        const z = collectTokenize(u8, syms[1], ',');
        var resb : [z.len]u8 = undefined;

        for (0..z.len) |i| {
            resb[i] = z[i][0];
        }

        break :blk1 resb;
    };

    break :blk a ++ b ++ ops ++ pref_ops;
};
        

fn collectTokenize(comptime T: type, inp: []const T, sep: T) []const []const T { // Doesn't work properly if T is an array type
    var res: []const []const T = &[_]([]const T){};

    var spl_It = std.mem.tokenize(T, inp, &[_]T{sep});

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

fn precs(u: u8) u8 {
    return switch (u) {
        '^' => 3,
        '*', '/' => 2,
        '%', '\'' => 1,
        '+', '-' => 0,
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
    None,
};

pub const Token = struct {
    kind: TKind,
    val: []const u8,
};


pub fn partFile(inp : []const u8) ![]const []const u8 {
    var result = ArrayList([]const u8).init(gpallocator);
    var c_word = ArrayList(u8).init(gpallocator);
    defer c_word.deinit();
    defer result.deinit();

    for (inp) |c| {
        if (constContains(u8, lex_stop, c)) {
            if (c_word.items.len > 0) {
                try result.append(try c_word.toOwnedSlice());
                c_word = ArrayList(u8).init(gpallocator); // empties c_word
            }
            try result.append(&[_]u8{c});
        } else {
            try c_word.append(c);
        }
    }

    if (c_word.items.len > 0 and !constContains(u8, lex_stop, c_word.items[0] )) {
        try result.append(try c_word.toOwnedSlice());
    }

    return result.toOwnedSlice();
}

pub fn lex(inp : []const []const u8) ![]const Token {
    var result = ArrayList(Token).init(gpallocator);
    
    for (0..inp.len) |i| {
        if ('0' <= inp[i][0] and inp[i][0] <= '9') {
            if (constContains(u8, inp[i], '.')) {
                try result.append(Token {.kind = TKind.FloatLit, .val = inp[i]});
            } else {
                try result.append(Token {.kind = TKind.FloatLit, .val = inp[i]});
            }
        } else if (inp[i][0] == '\"' and inp[i][inp[i].len - 1] == '\"') {
            try result.append(Token {.kind = TKind.StrLit, .val = inp[i][1..inp.len]});
        } else if (constContains(u8, &punc, inp[i][0])) {
            try result.append(Token {.kind = TKind.Punc, .val = inp[i]});
        } else if (constContains(u8, &pref_ops, inp[i][0])) {
            try result.append(Token {.kind = TKind.PrefOp, .val = inp[i]});
        } else if (constContains(u8, &wspaces, inp[i][0])) {
            try result.append(Token {.kind = TKind.Ident, .val = inp[i]});
        }
    }

    return result.toOwnedSlice();
}


pub const ASTNode = struct {
    val: union(enum) {
        nval: union(enum) {
            ival: i32,
            fval: f32,
        },
        sval: []u8,
    },
    kids: ArrayList(ASTNode),

    pub fn parseExpr(self: ASTNode, inp: []Token) void {
        _ = inp;
        _ = self;
    }
};

pub fn main() !void {}

test "comptime arrays" {
    std.debug.print("{s}\n{d}\n{s}\n{d}\n{s}\n{s}", .{ syms, wspaces, punc, end_word, pref_ops, ops });
}

test "Token" {
    const inp = "shjadjsakdjsajdlskjalkdsjads".*;
    const tkn = Token{
        .kind = TKind.IntLit,
        .val = inp[0..3],
    };
    std.debug.print("{}", .{tkn});
}

test "Tokenize" {
    var inp = "x*8 + 81*x^3 + 10*x^2";

    std.debug.print("{any}", .{try lex(try partFile(inp))});
}

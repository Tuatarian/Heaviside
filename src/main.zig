const std = @import("std");

const syms_txt = @embedFile("../resources/symbols.txt");
const precs_txt = @embedFile("../resources/precedence.txt");


// Hilariously, all the stuff below is initalization stuff. This was easier in Rust/Nim since it's mostly filtering strings/arrays at comptime, which is a lot easier to express with FPisms

const syms : []const []const u8 = collectTokenize(u8, syms_txt, '\n');

const wspaces = blk: {
    const z = collectTokenize(u8, syms[2], ',');
    var res : [z.len]u8 = undefined;
    
    for (0..z.len) |i| {
        res[i] = z[i][0];
    }

    break :blk res;
};

const punc = blk: {
    const z = collectTokenize(u8, syms[0], ',');
    var res : [z.len + 1]u8 = undefined;

    for (0..z.len) |i| {
        res[i] = z[i][0];
    }
    res[z.len] = ',';

    break :blk res;
};

const end_word = [_]u8{','} ++ wspaces;
const pref_ops = blk: {
    const z = collectTokenize(u8, syms[4], ',');
    var res : [z.len]u8 = undefined;

    for (0..z.len) |i| {
        res[i] = z[i][0];
    }

    break :blk res;
};

const ops = blk: {
    const z = collectTokenize(u8, replaceRet(u8, precs_txt, &[_]u8{'\n'}, &[_]u8{','}), ',');

    var res : [z.len]u8 = undefined;

    for (0..z.len) |i| {
        res[i] = z[i][0];
    }

    break :blk res;
};

fn collectTokenize(comptime T : type, inp : []const T, sep : T) []const []const T { // Doesn't work properly if T is an array type
    var res : []const []const T = &[_]([]const T){};
    
    var spl_It = std.mem.tokenize(T, inp, &[_]T{sep});

    while (spl_It.next()) |s| {
        res = res ++ .{s};
    }

    return res;
}

fn replaceRet(comptime T : type, haystack : []const T, needle : []const T, new_needle : []const T) []const T {
    var res : [std.mem.replacementSize(T, haystack, needle, new_needle)]T = undefined;
    _ = std.mem.replace(T, haystack, needle, new_needle, &res);
    return &res;
}

fn precs(u : u8) u8 {
    return switch (u) {
        '^' => 3,
        '*', '/' => 2,
        '%', '\'' => 1,
        '+', '-' => 0
    };
}


pub fn main() !void {
    std.debug.print("{s}\n{d}\n{s}\n{d}\n{s}\n{s}", .{syms, wspaces, punc, end_word, pref_ops, ops});
}

import os, strutils, sequtils, sugar

const syms = readFile("./symbols.txt").splitLines

const lexStop = @[',', '\n'] & syms[1].split(',').toSeq.map(x => x[0])
echo lexStop

type TKind = enum
    TkNumLit, TkIdent, TkWSpace

type NKind = enum
    NkIdent, NkCall

type Token = object
    kind : TKind
    val : string

type ASTNode = object
    kind : NKind
    name : string
    left, right : int

func `$`(n : ASTNode) : string = n.name

func `$$`(n : ASTNode : char = n.name[0]

let inp = readFile(commandLineParams()[0])
echo inp

proc partFile(inp : string) : seq[string] =
    var cWord : string
    for c in inp:
        if c in lexStop:
            if cWord.len != 0:
                result.add cWord
            result.add $$c
            cWord = ""
        else: cWord.add c

proc tokenize(inp : seq[string]) : seq[Token] =
    for i in 0..<inp.len:
        case inp[i]:
            of inp[i] in [' ', '\n']:
                result.add Token(kind : TkWSpace, val : inp[i])
            of inp[i][0] in '0'..'9':
                result.add Token(kind : TkNumLit, val : inp[i])
            of inp[i] in lexStop

func parseCall(lex : seq[ASTNode], beg : int, inx : var int) : seq[(nType, string)] =
    # Assume beg opens at the call
    # We remove exactly one node from the beginning (paren)
    if $$lex[beg - 1] notin lexStop and $$lex[beg - 1] != ' ':
        result.add ASTNode(kind : Call, name : $lex[beg - 1])
    var i = beg + 1
    while $$lex[i] != ')':
        if $$lex[i] == '(':
            var enx : int
            result.add lex.parseCall(i, enx)
            result[^1].left = beg - 1
        if $$lex[i + 1] == ',':
            result.add ASTNode(kind : Ident, name : $lex[i])
        lex[i].left = 0



func findCalls(lex : var seq[ASTNode], start : int) : seq[ASTNode] =
    # Assume start opens at a paren, then we should get a paren then args


echo partFile(inp)

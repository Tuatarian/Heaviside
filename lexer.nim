import os, strutils, sequtils, sugar, zero_functional, strformat

const syms = readFile("./symbols.txt").splitLines

const lexStop = @[',', '\n'] & syms[1].split(',').toSeq.map(x => x[0])
const whitespaces = syms[2].split(',').toSeq.map(x => x[0])
const punc = ',' & syms[0].split(',').toSeq.map(x => x[0])

type TKind = enum
    TkNumLit, TkIdent, TkWSpace, TkStrLit, TkPunc

type NKind = enum
    NkIdent, NkCall, NkNumLit, NkStrLit

type Token = object
    kind : TKind
    val : string

type ASTNode = object
    kind : NKind
    val : string
    left, right : int

func `!`(n : ASTNode) : string = n.val
func `!`(n : Token) : string = n.val

func `$`(n : ASTNode) : string = &"({n.kind} {!n} : ({n.left},{n.right}))"
  
func `$$`(n : ASTNode) : char = n.val[0]
func `$$`(n : Token) : char = n.val[0]

func shift(n : var ASTNode, i : SomeInteger) =
    n.left += i
    n.right += i

proc print(n : seq[ASTNode]) =
    var depth : int
    var rights : seq[int]
    for i in 0..<n.len:
        depth += -rights.count(i)
        for i in 0..<depth: stdout.write("    ")
        echo &"{n[i].kind} {!n[i]}"
        if n[i].kind == NkCall:
            depth += 1
            rights.add n[i].right

let inp = readFile(commandLineParams()[0]).splitLines[4]
echo inp

proc partFile(inp : string) : seq[string] =
    var cWord : string
    for c in inp:
        if c in lexStop:
            if cWord.len != 0:
                result.add cWord
            result.add $c
            cWord = ""
        else: cWord.add c

proc tokenize(inp : seq[string]) : seq[Token] =
    for i in 0..<inp.len:
        if inp[i][0] in '0'..'9':
            result.add Token(kind : TkNumLit, val : inp[i])
        elif inp[i][0] == '\"' and inp[i][^1] == '\"':
            result.add Token(kind : TkStrLit, val : inp[i])
        elif inp[i][0] in punc:
            result.add Token(kind : TkPunc, val : inp[i])
        elif inp[i][0] notin whitespaces:
            result.add Token(kind : TkIdent, val : inp[i])

# func findPrevIndNode(s : seq[ASTNode], beg : int) : int = ## We're assuming here that beg is a call
#     for i in beg - 1..0:
#         if s[i].kind.isNested

proc delete[T](s : var seq[T], r : Slice[Natural]) = ## Delete all items in a..b
    for i in 0..<r.len:
        s.delete(r[0])

func recDescent(inp : seq[Token], beg : int) : (seq[ASTNode], int) =
    # assuming beg is at the call
    var i = beg + 2
    var nextLeft : int
    result[0].add ASTNode(kind : NkCall, val : !inp[beg])
    while $$inp[i] != ')':
        if $$inp[i + 1] == '(' and inp[i].kind == TkIdent:
            var (newTree, enx) = recDescent(inp, i)
            for i in 1..<newTree.len: newTree[i].shift(result[0].len)
            newTree[0].right += result[0].len
            i = enx
            nextLeft = result[0].len
            result[0] &= newTree
            if i >= inp.len: break
        else:
            case inp[i].kind:
                of TkIdent:
                    result[0].add ASTNode(kind : NkIdent, val : !inp[i], left : nextLeft, right : result[0].len + 1)
                of TkNumLit:
                    result[0].add ASTNode(kind : NkNumLit, val : !inp[i], left : nextLeft, right : result[0].len + 1)
                of TkStrLit:
                    result[0].add ASTNode(kind : NkStrLit, val : !inp[i], left : nextLeft, right : result[0].len + 1)
                of TkPunc: discard
                of TkWSpace: discard
                else: raise newException(Defect, "Unrecognized Token Kind : This should never happen")
            nextLeft = result[0].len - 1
            i += 1
    result[0][0].right = result[0].len
    debugEcho i + 1
    if i + 1 < inp.len: debugEcho inp[i + 1]
    else: debugEcho inp.len
    debugEcho result[0][0], result[0]
    return (result[0], i + 1)

func parse(inp : seq[Token]) : seq[ASTNode] =
    var i : int
    while i in 0..<inp.len:
        if $$inp[i + 1] == '(':
            let shift = i - result.len
            var newTree : seq[ASTNode]
            (newTree, i) = inp.recDescent i
            for i in 0..<newTree.len: newTree[i].shift(result.len)
            result &= newTree
            continue
        i += 1

# func parseCall(lex : seq[ASTNode], beg : int, inx : var int) : seq[(nType, string)] =
#     # Assume beg opens at the call
#     # We remove exactly one node from the beginning (paren)
#     if $$lex[beg - 1] notin lexStop and $$lex[beg - 1] != ' ':
#         result.add ASTNode(kind : Call, name : $lex[beg - 1])
#     var i = beg + 1
#     while $$lex[i] != ')':
#         if $$lex[i] == '(':
#             var enx : int
#             result.add lex.parseCall(i, enx)
#             result[^1].left = beg - 1
#         if $$lex[i + 1] == ',':
#             result.add ASTNode(kind : Ident, name : $lex[i])
#         lex[i].left = 0



# func findCalls(lex : var seq[ASTNode], start : int) : seq[ASTNode] =
    # Assume start opens at a paren, then we should get a paren then
echo "-"
echo inp.partFile
echo inp.partFile.tokenize().map(x => !x), inp.partFile.tokenize().map(x => !x).len
print inp.partFile.tokenize().parse
let tree = inp.partFile.tokenize().parse 
echo tree.map(n => $n & &" : ({tree.find(n)} {n.left} {n.right}), ")

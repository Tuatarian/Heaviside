import os, strutils, sequtils, sugar, zero_functional, strformat

const syms = readFile("./symbols.txt").splitLines
const whitespaces = syms[2].split(',').toSeq.map(x => x[0])
const punc = ',' & syms[0].split(',').toSeq.map(x => x[0])
const endWord = ',' & whitespaces
const ops = syms[3].split(',').map(x => x[0])
const prefOps = syms[4].split(',').map(x => x[0])
const lexStop = (@[',', '\n'] & syms[1].split(',').toSeq.map(x => x[0])) & ops & prefOps

type TKind = enum
    TkNumLit, TkIdent, TkWSpace, TkStrLit, TkPunc, TkOp, TkPrefOp

type NKind = enum
    NkIdent, NkCall, NkNumLit, NkStrLit, NkOp, NkRt

type Token = object
    kind : TKind
    val : string

type ASTNode = ref object
    kind : NKind
    val : string
    kids : seq[ASTNode]
    parentalUnit : ASTNode

func `!`(n : ASTNode) : string = n.val
func `!`(n : Token) : string = n.val
  
func `$$`(n : ASTNode) : char = n.val[0]
func `$$`(n : Token) : char = n.val[0]

proc print(n : ASTNode, d : int = -1) =
    if n.kind != NkRt:
        echo &"""{"    ".repeat(d)}{n.kind} {!n}"""
    for kid in n.kids:
        print(kid, d + 1)
            
proc partFile(inp : string) : seq[string] =
    var cWord : string
    for c in inp:
        if c in lexStop:
            if cWord.len != 0:
                result.add cWord
            result.add $c
            cWord = ""
        else: cWord.add c
    if cWord.len > 0 and cWord[0] notin lexStop:
        result.add cWord

proc tokenize(inp : seq[string]) : seq[Token] =
    for i in 0..<inp.len:
        if inp[i][0] in '0'..'9':
            result.add Token(kind : TkNumLit, val : inp[i])
        elif inp[i][0] == '\"' and inp[i][^1] == '\"':
            result.add Token(kind : TkStrLit, val : inp[i])
        elif inp[i][0] in punc:
            result.add Token(kind : TkPunc, val : inp[i])
        elif inp[i][0] in ops:
            result.add Token(kind : TkOp, val : inp[i])
        elif inp[i][0] in prefOps:
            result.add Token(kind : TkPrefOp, val : inp[i])
        elif inp[i][0] notin whitespaces:
            result.add Token(kind : TkIdent, val : inp[i])

# func findPrevIndNode(s : seq[ASTNode], beg : int) : int = ## We're assuming here that beg is a call
#     for i in beg - 1..0:
#         if s[i].kind.isNested

proc delete[T](s : var seq[T], r : Slice[Natural]) = ## Delete all items in a..b
    for i in 0..<r.len:
        s.delete(r[0])

proc add(n : var ASTNode, n1 : ASTNode) = n.kids.add n1

template `[]`(n : ASTNode, i : untyped) : ASTNode = n.kids[i]

proc pushInto[T](e : T, s : var seq[T], frm : int) =
    s.add e
    for i in frm + 1..<s.len:
        swap(s[frm], s[i])

#---------------------------#
#    ACTUAL PARSING CODE    #
#---------------------------#

var lastNode : ASTNode # This is global state, should be updated as each node is added
# The intention right now is to use this for infix operator parsing

proc parseExpr(rt : var ASTNode, inp : seq[Token])
                    
proc parseCall(rt : var ASTNode, inp : seq[Token]) =
    # Again, assuming beg is the start of the call, seq[Token] also should end at the end
    # We want to count the number of arguements, but we can't use naive splitting by ',', since some args may be function calls like d(a, c)
    # I'm thinking to accomplish this by doing a short loop before the main parsing loop where we basically go through and split the inp at each ',' not surrounded by ()
    # We can determine if the arg is surrounded by () by keeping track of a "nesting number", which will simply store how many ( deep we are
  
    # Rt is the parent of the call, so we just make a new kid for the call
    rt.add ASTNode(kind : NkCall, val : !inp[0])
    # This is rt.kids[^1], which is a ref, so we can mutate a passed version and not worry

    var nestCount : int
    var args : seq[seq[Token]]
    var imedArg : seq[Token]

    var i = 2
    while nestCount >= 0:
        if $$inp[i] == '(':
            nestCount += 1
        elif $$inp[i] == ')':
            nestCount += -1

        if $$inp[i] != ',':
            imedArg.add inp[i]
        elif nestCount <= 0:
            args.add imedArg
            iMedArg = @[]
        i += 1
    args.add iMedArg

    for arg in args:
        rt[^1].parseExpr(arg)

    lastNode = rt[^1]
                    
proc parseExpr(rt : var ASTNode, inp : seq[Token]) =
    var i : int

    # Parsing operators, what a pain
    # We can pretty easily parse prefix operators as function calls

    var inPrefix : bool
    
    while i in 0..<inp.len:
        if (i + 1 < inp.len and $$inp[i + 1] == '(') or inp[i].kind == TkOp:
            var nestCount : int
            var slice = (i, -1)

            if inp[i].kind == TkOp:
                i += 1
            else: i += 2
            
            while nestCount >= 0:
                if $$inp[i] == '(':
                    nestCount += 1
                elif $$inp[i] == ')':
                    nestCount += -1
                i += 1
            slice[1] = i - 1

            rt.parseCall(inp[slice[0]..slice[1]])
        elif inp[i].kind == TkPrefOp:
              if inPrefix:
                  lastNode.add ASTNode(kind : NkCall, val : !inp[i])
                  lastNode = lastNode[^1]
              else:
                  rt.add ASTNode(kind : NkCall, val : !inp[i])
                  lastNode = rt[^1]
                  inPrefix = true
        elif inp[i].kind == TkIdent:
            if inPrefix:
                inPrefix = false

                lastNode.add ASTNode(kind : NkIdent, val : !inp[i], parentalUnit : lastNode)
                lastNode = lastNode[^1]
            else:
                rt.add ASTNode(kind : NkIdent, val : !inp[i], parentalUnit : rt)
                lastNode = rt[^1]
        i += 1

var rt = ASTNode(kind : NkRt)
let inp = readFile(commandLineParams()[0]).splitLines[6]
echo inp
echo "-"
echo inp.partFile.tokenize().map(x => !x), inp.partFile.tokenize().map(x => !x).len
rt.parseExpr(inp.partFile.tokenize())
print rt

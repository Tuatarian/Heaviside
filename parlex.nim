import os, strutils, sequtils, sugar, zero_functional, strformat, tables

const syms = readFile("./symbols.txt").splitLines
const whitespaces = syms[2].split(',').toSeq.map(x => x[0])
const punc = ',' & syms[0].split(',').toSeq.map(x => x[0])
const endWord = ',' & whitespaces
const prefOps = syms[4].split(',').map(x => x[0])
const precLines = readfile("./precedence.txt").splitLines
const ops = readFile("./precedence.txt").replace("\n", ",").split(",").toSeq.filter(x => x.len > 0).map(x => x[0])


const precs = block:
    var precs = initTable[string, int]()
    for i in 0..<precLines.len:
        for o in precLines[i].split(','):
            if o.len >= 0:
                precs[o] = precLines.len - i
    precs

const lexStop = (@[',', '\n'] & syms[1].split(',').toSeq.map(x => x[0])) & ops & prefOps

type TKind = enum
    TkNumLit, TkIdent, TkWSpace, TkStrLit, TkPunc, TkOp, TkPrefOp, TkNull

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

proc add(n : ASTNode, n1 : ASTNode) =
      n.kids.add n1

template `[]`(n : ASTNode, i : untyped) : ASTNode = n.kids[i]

proc pushInto[T](e : T, s : var seq[T], frm : int) =
    s.add e
    for i in frm + 1..<s.len:
        swap(s[frm], s[i])

proc reparentTo(n : ASTNode, p : ASTNode) =
    p.add n
    n.parentalUnit.kids.delete(n.parentalUnit.kids.find(n))
    n.parentalUnit = p
        
#---------------------------#
#    ACTUAL PARSING CODE    #
#---------------------------#

var lastNode : ASTNode # This is global state, should be updated as each node is added
# The intention right now is to use this for infix operator parsing

proc parseArg(rt : ASTNode, inp : seq[Token]) # Forward decl, unfortunately this is necessary in nim for now
proc parseExpr(rt : ASTNode, inp : seq[Token])
                    
proc parseCall(rt : ASTNode, inp : seq[Token]) =
    # Again, assuming beg is the start of the call, seq[Token] also should end at the end
    # We want to count the number of arguements, but we can't use naive splitting by ',', since some args may be function calls like d(a, c)
    # I'm thinking to accomplish this by doing a short loop before the main parsing loop where we basically go through and split the inp at each ',' not surrounded by ()
    # We can determine if the arg is surrounded by () by keeping track of a "nesting number", which will simply store how many ( deep we are
  
    # Rt is the parent of the call, so we just make a new kid for the call
    rt.add ASTNode(kind : NkCall, val : !inp[0], parentalUnit : rt)
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
        rt[^1].parseExpr(arg) # incase it has operators

    lastNode = rt[^1]
                    
proc parseArg(rt : ASTNode, inp : seq[Token]) =
    var i : int

    # Parsing operators, what a pain
    # We can pretty easily parse prefix operators (described below)

    var inOp : bool

    # If we're in an operator, we should add to lastNode instead of to rt
    # The logic for doing this with a prefix operator is detailed below
    # This function no longer deals with infix operators 
    
    while i in 0..<inp.len:
        if (i + 1 < inp.len and $$inp[i + 1] == '('):
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

            if inOp:
                var tmpLastNode = lastNode
                tmpLastNode.parseCall(inp[slice[0]..slice[1]])
                inOp = false
            else:
                rt.parseCall(inp[slice[0]..slice[1]])
        elif inp[i].kind == TkPrefOp:
            # The idea here is to append to the most recently appended node if we're in a prefix, and otherwise append to rt
            # The logic being @&a = @(&(a)), so @ should append to rt, & should append to @ and a should append to &
            # This may get messy, but I am not sure if there's a better way
            if inOp:
                lastNode.add ASTNode(kind : NkCall, val : !inp[i], parentalUnit : lastNode)
                lastNode = lastNode[^1]
            else:
                rt.add ASTNode(kind : NkCall, val : !inp[i], parentalUnit : rt)
                lastNode = rt[^1]
                inOp = true
        elif inp[i].kind == TkIdent:
            if inOp:
                inOp = false
                
                lastNode.add ASTNode(kind : NkIdent, val : !inp[i], parentalUnit : lastNode)
                lastNode = lastNode[^1]
            else:
                rt.add ASTNode(kind : NkIdent, val : !inp[i], parentalUnit : rt)
                lastNode = rt[^1]
        i += 1

proc parseExpr(rt : ASTNode, inp : seq[Token]) =
    # We iterate over the expr, we split it into the operators and the not operators
    # We process the args (so something like f(a) + g(b) gets processed correctly) then pass them to the operators
    # Handling operators nested in calls : we pass each arg back to parseExpr recursively, and if it contains no operators, we give it to parseArg
    # Eventually, we get to (possibly deeply nested) exprs which are arguement free, and the algorithm will converge

    var args : seq[seq[Token]]
    var imedArg : seq[Token]

    # We have to do a similar thing with keeping count of nesting that parseCall does (since we're parsing the args recursively)
    # To see why, think about f(a + b) * c

    var nestCount : int
    for t in inp:
        if $$t == '(':
            nestCount += 1
        elif $$t == ')':
            nestCount += -1
          
        if nestCount == 0 and t.kind == TkOp:
            args.add imedArg
            args.add @[t]
            imedArg = @[]
        else:
            imedArg.add t
    args.add imedArg


    # Search through args and find all the indices of operators with the highest precedence
    var cPrec = 0
    var cOps : seq[int]
    for i in 0..<args.len:
        if args[i].len == 1 and args[i][0].kind == TkOp:
            if precs[!args[i][0]] == cPrec:
                cOps.add i
            elif precs[!args[i][0]] > cPrec:
                cOps = @[i]
                cPrec = precs[!args[i][0]]
            

    for i in 0..<cOps.len:
        if i == 0:
            rt.add ASTNode(kind : NkCall, val : !inp[cOps[i]], parentalUnit : rt)
            rt[^1].parseExpr(args[cOps[i] - 1])
            rt[^1].parseExpr(args[cOps[i] + 1])
        else:
            rt.add ASTNode(kind : NkCall, val : !inp[cOps[i]], parentalUnit : rt)          
            if cOps[i] - 2 in cOps:
                rt[^2].reparentTo rt[^1]
                rt[^1].parseExpr(args[cOps[i] + 1])
            else:
                rt[^1].parseExpr(args[cOps[i] - 1])
                rt[^1].parseExpr(args[cOps[i] + 1])              

            
    if cOps.len == 0:
        if args.len > 1:
            debugEcho args
            assert args.len == 1
        rt.parseArg args[0]
    
        
var rt = ASTNode(kind : NkRt)
lastNode = rt
let inp = readFile(commandLineParams()[0]).splitLines[6]
echo inp
echo "-"
echo inp.partFile.tokenize().map(x => !x), inp.partFile.tokenize().map(x => !x).len
rt.parseExpr(inp.partFile.tokenize())
print rt

import os, strutils, sequtils, sugar, zero_functional, strformat

const syms = readFile("./symbols.txt").splitLines
l
const lexStop = @[',', '\n'] & syms[1].split(',').toSeq.map(x => x[0])
const whitespaces = syms[2].split(',').toSeq.map(x => x[0])
const punc = ',' & syms[0].split(',').toSeq.map(x => x[0])
const endWord = ',' & whitespaces
const ops = syms[3].split(',').map(x => x[0])
const prefOps = syms[4].split(',').map(x => x[0])

type TKind = enum
    TkNumLit, TkIdent, TkWSpace, TkStrLit, TkPunc, TkOp

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

# func `$`(n : ASTNode) : string = &"({n.kind} {!n} : ({n.left},{n.right}))"
  
func `$$`(n : ASTNode) : char = n.val[0]
func `$$`(n : Token) : char = n.val[0]

# func shift(n : var ASTNode, i : SomeInteger) =
#     n.left += i
#     n.right += i

# proc print(n : seq[ASTNode]) =
#     var depth : int
#     var rights : seq[int]
#     for i in 0..<n.len:
#         depth += -rights.count(i)
#         for i in 0..<depth: stdout.write("    ")
#         echo &"{n[i].kind} {!n[i]}"
#         if n[i].kind == NkCall:
#             depth += 1
#             rights.add n[i].right

proc print(n : ASTNode, d : int = -1) =
    if n.kind != NkRt:
        echo &"""{"    ".repeat(d)}{n.kind} {!n}"""
    for kid in n.kids:
        print(kid, d + 1)
            
# func debugPrint(n : seq[ASTNode]) =
#     var depth : int
#     var rights : seq[int]
#     for i in 0..<n.len:
#         depth += -rights.count(i)
#         var preTab : string
#         for i in 0..<depth: preTab &= "    "
#         debugEcho &"{preTab}{n[i].kind} {!n[i]}"
#         if n[i].kind == NkCall:
#             depth += 1
#             rights.add n[i].right
            
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
        
# func recDescent(inp : seq[Token], beg : int) : (seq[ASTNode], int) =
#     # assuming beg is at the call
#     var i = beg + 2
#     var nextLeft : int
#     result[0].add ASTNode(kind : NkCall, val : !inp[beg])
#     while $$inp[i] != ')':
#         if $$inp[i + 1] == '(' and inp[i].kind == TkIdent:
#             var (newTree, enx) = recDescent(inp, i)
#             for i in 1..<newTree.len: newTree[i].shift(result[0].len)
#             newTree[0].right += result[0].len
#             i = enx
#             nextLeft = result[0].len
#             result[0] &= newTree
#             if i >= inp.len: break
#         else:
#             case inp[i].kind:
#                 of TkIdent:
#                     result[0].add ASTNode(kind : NkIdent, val : !inp[i], left : beg, right : result[0].len + 1)
#                 of TkNumLit:
#                     result[0].add ASTNode(kind : NkNumLit, val : !inp[i], left : beg, right : result[0].len + 1)
#                 of TkStrLit:
#                     result[0].add ASTNode(kind : NkStrLit, val : !inp[i], left : beg, right : result[0].len + 1)
#                 of TkPunc: discard
#                 of TkOp:
#                     var  inp[i..^1]
                    
#                     for i in 0..<toParse.len:
#                       toParse[i].left += beg
#                       toParse[i].right += result[0].len
#                 of TkWSpace: discard
#                 else: raise newException(Defect, "Unrecognized Token Kind : This should never happen")
#             nextLeft = result[0].len - 1
#             i += 1
#     result[0][0].right = result[0].len
#     return (result[0], i + 1)

func parseExpr(rt : var ASTNode, inp : seq[Token])
        
# func parseCall_old(inp : seq[Token]) : seq[ASTNode] =
#     # Again, assuming beg is the start of the call, seq[Token] also should end at the end
#     # We want to count the number of arguements, but we can't use naive splitting by ',', since some args may be function calls like d(a, c)
#     # I'm thinking to accomplish this by doing a short loop before the main parsing loop where we basically go through and split the inp at each ',' not surrounded by ()
#     # We can determine if the arg is surrounded by () by keeping track of a "nesting number", which will simply store how many ( deep we are

#     result.add ASTNode(kind : NkCall, val : !inp[0], left : -1, right : 1)

#     var nestCount : int
#     var args : seq[seq[Token]]
#     var imedArg : seq[Token]

#     var i = 2
#     while nestCount >= 0:
#         if $$inp[i] == '(':
#             nestCount += 1
#         elif $$inp[i] == ')':
#             nestCount += -1

#         if $$inp[i] != ',':
#             imedArg.add inp[i]
#         elif nestCount <= 0:
#             args.add imedArg
#             iMedArg = @[]
#         i += 1
#     args.add iMedArg

#     for arg in args:
#         var pArg = parseExpr arg
#         for i in 1..<pArg.len: pArg[i].left += result.len
#         result &= pArg

#     result[0].right = result.len
#     for i in 1..<result.len:
#         if result[i].left <= 0:
#             for j in i + 1..<result.len:
#                 if result[j].left == 0:
#                     result[i].right = j
#                     break
#                 elif j == result.len - 1:
#                     result[i].right = -1
                    
func parseCall(rt : var ASTNode, inp : seq[Token]) =
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
                    
func parseExpr(rt : var ASTNode, inp : seq[Token]) =
    var i : int
    var lastNode : ASTNode

    # Parsing operators, what a pain
    # We can pretty easily parse prefix operators as function calls
    
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
        elif inp[i].kind == TkIdent:
            rt.kids.add ASTNode(kind : NkIdent, val : !inp[i], parentalUnit : rt)
        i += 1
        
                    
# func parseExpr_old(inp : seq[Token]) : seq[ASTNode] =
#     var i : int
#     var lastTop : (int, int, int) # (inx, left, right)
#     var prevOps : seq[(int, int, int)]
#     var inOp : int
#     while i in 0..<inp.len:
#         if i + 1 < inp.len and $$inp[i + 1] == '(':
#             let shift = i - result.len
#             var newTree : seq[ASTNode]
            
#             var slice = (i, -1)
#             var nestCount : int
#             i += 2

#             while nestCount >= 0:
#                 if $$inp[i] == '(':
#                     nestCount += 1
#                 elif $$inp[i] == ')':
#                     nestCount += -1
#                 i += 1
#             slice[1] = i - 1
            
#             newTree = parseCall inp[slice[0]..slice[1]]
#             for j in 0..<newTree.len: newTree[j].shift(result.len)
#             if prevOps.len > 0:
#                 result[prevOps[^1][0]].right = result.len + newTree.len
#                 for j in 0..<prevOps.len:
#                     result[prevOps[j][0]].right = result.len + 1
#                     if i == prevOps[j][2]: prevOps.delete i
#                 inOp += -1
#             lastTop = (result.len, newTree[0].left, newTree[0].right)
#             result &= newTree
#             continue
#         elif $$inp[i] in ops:
#             inOp += 1
#             ASTNode(kind : NkCall, val : !inp[i], left : lastTop[1], right : -1).pushInto(result, lastTop[0])
#             prevOps.add lastTop
#             for j in lastTop[0] + 1..<result.len:
#                 result[j].left += -1
#                 result[j].left = max(result[j].left, 0)
#                 result[j].right += 1
#         elif $$inp[i] == ')': return result
#         elif inp[i].kind == TkIdent:
#             result.add ASTNode(kind : NkIdent, val : !inp[i], left : lastTop[0], right : result.len + 1)
#             if prevOps.len > 0:
#                 for j in 0..<prevOps.len:
#                     result[prevOps[j][0]].right = result.len + 1
#                     if i == prevOps[j][2]: prevOps.delete i
#                 inOp += -1
#             lastTop = (i, result[^1].left, result[^1].right)
#         var shift : int
#         for j in 1..<prevOps.len:
#             if prevOps[j][2] < result.len:
#                 prevOps.delete j - shift
#                 shift += 1
#         i += 1
          

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
    # Assume start opens at a paren, then we should get a paren

var rt = ASTNode(kind : NkRt)
let inp = readFile(commandLineParams()[0]).splitLines[5]
echo inp
echo "-"
echo inp.partFile.tokenize().map(x => !x), inp.partFile.tokenize().map(x => !x).len
rt.parseExpr(inp.partFile.tokenize())
print rt

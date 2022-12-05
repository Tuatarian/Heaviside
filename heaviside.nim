import strutils, sequtils, tables, zero_functional, strformat, parlex, macros

## We're using an object variant here since I (obviously) don't want to make the user decide whether a number should be a float or an int in a CAS
## Also, we're going to require significantly different handling for ints than floats, for example 3/4 should not be converted to 0.75

type HvType = enum
    Num, Expr

type HvNum = object
    case isInt : bool
    of true: iVal : int
    of false: fVal : float

type HvExpr = ASTNode

type HvVal = object  # Using this for things who's types are unknown (like unevaluated parameters)
    case kind : HvType
    of Num: nVal : HvNum
    of Expr: eVal : HvExpr

#-------Convenience funcs-------#)

func `$`(p : pointer) : string = "0x" & cast[int](p).toHex

template makenum(b : int | float) : untyped =
    when b is int:
        HvNum(isInt : true, iVal : b)
    else:
        HvNum(isInt : false, fVal : b)

template val(h : HvNum) : untyped =
    if h.isInt:
        h.iVal
    else:
        h.fVal

func `-`(a : HvNum) : HvNum =
    if a.isInt: return makenum(-a.iVal)
    else: return makenum(-a.fVal)

template makeval(h : HvNum) : untyped = HvVal(kind : Num, nVal : h)
template makeval(e : HvExpr) : untyped = HvVal(kind : Expr, eVal : e)

template val(v : HvVal) : untyped =
    when v.kind == Num:
        v.nVal.val
    elif v.kind == Expr:
        v.eVal 

template apply(n: HvNum, act : untyped) : untyped =
    if n.isInt:
        act(n.iVal)
    else:
        act(n.fVal) 

func `$`(n : HvNum) : string = 
    if n.isInt: return $n.iVal
    else: return $n.fVal

func `$`(v : HvVal) : string =
    case v.kind:
    of Num: $v.nVal
    of Expr: !v.eVal

proc print(v : HvVal) =
    case v.kind:
    of Num: echo v.nVal
    of Expr: print v.eVal

#---------Tree Transformation Functions---------#

#-------HvFuncs-------#
# We'll prefix the versions of functions used by heaviside with hv to avoid confusion, so `/` (division) will be hvDiv, etc

# Also, to make my life easier, we'll overload everything so that I can use the same syntax for casting down the line

# Perhaps the sum function should be different, maybe variadic, so I'll call the `+` operator as hvPlus for now
func hvPlus(a, b : HvNum) : HvNum =
    if a.isInt and b.isInt:
        return makenum(a.iVal + b.iVal)
    elif a.isInt:
        return makenum(b.fVal + a.iVal.float)
    elif b.isInt:
        return makenum(b.iVal.float + a.fVal)
    return makenum(b.fVal + a.fVal)
# This doesn't handle exprs, we'll need to do that differently

func hvMinus(a, b : HvNum) : HvNum = hvPlus(a, -b)

func hvTimes(a, b : HvNum) : HvNum =
    if a.isInt and b.isInt:
        return makenum(a.iVal * b.iVal)
    elif a.isInt:
        return makenum(a.iVal.float * b.fVal)
    elif b.isInt:
        return makenum(a.fVal * a.iVal.float)
    return makenum(a.fVal * b.fVal)

#-------Building the Function Table-------#

# We're (probably) gonna need 3 tables
# These are all also going to be comptime. I will have to resolve user defined functions in some other way

macro bldFuncTable(t : typed, s : static[string]) : untyped = ## This doesn't work with generics (can extend if needed, but for now I'll just avoid using generic in hvFuncs)
    result = newNimNode(nnkPrefix)
    result.add ident("@")
    result.add newNimNode(nnkBracket)
    case t.kind
    of nnkSym:
        let res = repr t.getType[1]
        var argL : seq[NimNode]
        var args : string
        
        for i in 2..<t.getType.len:
            args &= &"{repr t.getType[i]} "
            argL.add(newIdentDefs(ident("a" & $(i - 2)), ident(repr t.getType[i]), newEmptyNode()))

        result[1].add newNimNode(nnkTupleConstr).add(
            newLit(&"{s} {args}"), newNimNode(nnkCommand).add(
                ident("pointer"), newNimNode(nnkPar).add(
                    newNimNode(nnkCall).add(
                        newNimNode(nnkPar).add(
                            newNimNode(nnkProcTy).add(
                                newNimNode(nnkFormalParams).add(
                                    ident(res))))))))
        for arg in argL:
            result[1][0][1][1][0][0][0][0].add arg
        
        result[1][0][1][1][0][0][0].add newNimNode(nnkPragma).add ident("nimcall")
        result[1][0][1][1][0].add ident(repr t)

    of nnkOpenSymChoice, nnkClosedSymChoice:
        var counter : int
        for x in t:
            let res = repr x.getType[1]
            var args : string

            for i in 2..<x.getType.len:
                    args &= &"{repr x.getType[i]} "

            result[1].add newNimNode(nnkTupleConstr).add(
                newLit(&"{s} {args}"), newNimNode(nnkCommand).add(
                    ident("pointer"), newNimNode(nnkPar).add(
                        newNimNode(nnkCall).add(
                            newNimNode(nnkPar).add(
                                newNimNode(nnkProcTy).add(
                                    newNimNode(nnkFormalParams).add(
                                        ident(res))))))))
            
            result[1][counter][1][1][0][0][0].add newNimNode(nnkPragma).add ident("nimcall")
            result[1][counter][1][1][0].add ident(repr t)

            counter += 1
    else:
        error("Did not get a proc, probably a bug", t)

macro bldRetTable(t : typed, s : static[string]) : untyped =
    result = newNimNode(nnkPrefix)
    result.add ident("@")
    result.add newNimNode(nnkBracket)
    case t.kind
    of nnkSym:
        let res = repr t.getType[1]
        var args : string
        
        for i in 2..<t.getType.len:
            args &= &"{repr t.getType[i]} "

        result[1].add newNimNode(nnkTupleConstr).add(
            newLit(&"{s} {args}"), newLit(&"{s} {res} {args}"))

    of nnkOpenSymChoice, nnkClosedSymChoice:
        for x in t:
            let res = repr x.getType[1]
            var args : string

            for i in 2..<x.getType.len:
                args &= &"{repr x.getType[i]} "

            result[1].add newNimNode(nnkTupleConstr).add(
                newLit(&"{s} {args}"), newLit(&"{s} {res} {args}"))
    else:
        error("Did not get a proc, probably a bug", t)

macro retreieveProc(desc : seq[string]) : untyped =
    result = newNimNode(nnkCall).add(
        newNimNode(nnkCast).add(
            newNimNode(nnkProcTy).add(
                newNimNode(nnkFormalParams).add(
                    ident($desc[0])
                ), newNimNode(nnkPragma).add(ident("nimcall"))
            )
        )
    )

var fnTable : Table[string, pointer] = toTable(
    bldFuncTable(hvMinus, "-") &
    bldFuncTable(hvPlus, "+") &
    bldFuncTable(hvTimes, "*")
)

var retTable : Table[string, string] = toTable(
    bldRetTable(hvMinus, "-") &
    bldRetTable(hvPlus, "+") &
    bldRetTable(hvTimes, "*")
)

func callMagicFunc(id : string, args : seq[HvVal]) : HvExpr | HvNum =
    case id:
    of "+ HvNum HvNum ":
        debugEcho hvPlus(args[0].nVal, args[1].nVal)
        return hvPlus(args[0].nVal, args[1].nVal)
    of "- HvNum HvNum ":
        return hvMinus(args[0].nVal, args[1].nVal)
    of "* HvNum HvNum ":
        return hvTimes(args[0].nVal, args[1].nVal)


#----------Tree Walking Code----------#
  
# General idea for this part

# DFS to go down the tree
# At each call, the child nodes are either HvNums or Exprs
# If we have an ident, then it is by default an expr
# If we have a NumLit, it is by default an HvNum
# If we have a node with children, then we recursively do the above to that node
# At the end, we'd need to have a way to pass that up
# For now, I'll do this by returning a tuple of (ASTNode, HvType)
    # The ASTNode is the result of applying the function to the node (quite possibly an expr)
    # The type is the type of the node (NumLit or Expr)
    # This might move onto the tree itself at some point in the future

proc evalAST(rt : ASTNode) : (HvVal, HvType) =
    if rt.kind == NkCall:
        var params : seq[HvVal]
        var paramTypes = !rt & " "

        for k in rt.kids:
            case k.kind:
            of NkIdent:
                paramTypes &= "HvExpr "
                params.add HvVal(kind : Expr, eVal : HvExpr k)
            of NkIntLit:
                paramTypes &= "HvNum "
                params.add HvVal(kind : Num, nVal : makenum(parseInt !k))
            of NkFloatLit:
                paramTypes &= "HvNum "
                params.add HvVal(kind : Num, nVal : makenum(parseFloat !k))
            of NkCall:
                let res = evalAST k
                case res[1]:
                of Num:
                    paramTypes &= "HvNum "
                of Expr:
                    paramTypes &= "HvExpr "
                params.add res[0]
            else:
                echo "Unexpected Node Kind in tree evaluation"
                writeStackTrace()
        
        result[0] = makeval callMagicFunc(paramTypes, params)
        result[1] = result[0].kind

var rt = ASTNode(kind : NkRt)
parseExpr(rt, tokenize partFile readFile("./symbols.txt").splitLines[6])
print rt
print evalAST(rt[0])[0]
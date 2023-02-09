import strutils, tables, zero_functional, strformat, parlex, math, algorithm

## We're using an object variant here since I (obviously) don't want to make the user decide whether a number should be a float or an int in a CAS
## Also, we're going to require significantly different handling for ints and floats, for example 3/4 should not be converted to 0.75

type HvType* = enum
    Num, Expr, Str

type HvExpr* = ASTNode

type HvVal* = object  # Using this for things who's types are unknown (like unevaluated parameters)
    case kind* : HvType
    of Num: nVal* : HvNum
    of Expr: eVal* : HvExpr
    of Str: sVal* : string

#-------Convenience funcs-------#)

func `$`*(p : pointer) : string = "0x" & cast[int](p).toHex

func nType*(n : HvNum) : NKind =
    if n.isInt: return NkIntLit
    else: return NkFloatLit

template hvType*(n : NKind) : HvType =
    case n:
    of NkIntLit, NkFloatLit: Num
    of NkStrLit: Str
    else: Expr

func `-`*(a : HvNum) : HvNum =
    if a.isInt: return makenum(-a.iVal)
    else: return makenum(-a.fVal)

template makeval*(h : HvNum) : untyped = HvVal(kind : Num, nVal : h)
template makeval*(e : HvExpr) : untyped = HvVal(kind : Expr, eVal : e)

template val*(v : HvVal) : untyped =
    when v.kind == Num:
        v.nVal.val
    elif v.kind == Expr:
        v.eVal 

template apply*(n: HvNum, act : untyped) : untyped =
    if n.isInt:
        act(n.iVal)
    else:
        act(n.fVal)

func `$`*(v : HvVal) : string =
    case v.kind:
    of Num: $v.nVal
    of Expr: !v.eVal
    of Str: v.sVal

proc print*(v : HvVal) =
    case v.kind:
    of Num: echo v.nVal
    of Expr: print(v.eVal, 0)
    of Str: echo v.sVal

func makeExpr*(a : HvNum, p : HvExpr = nil) : HvExpr = 
    if a.isInt:
        return HvExpr(kind : NkIntLit, nVal : a, parentalUnit : p)
    else:
        return HvExpr(kind : NkFloatLit, nVal : a, parentalUnit : p)

func makeExpr*(k : NKind, v : string = "", n : HvNum = makenum 0, p : HvExpr = nil, childs : seq[HvExpr] = @[]) : HvExpr {.inline.} =
    result = HvExpr(kind : k, kids : childs, parentalUnit : p)
    if result.kind in numerics:
        result.nVal = n
    else:
        result.val = v

func makeExpr*(n : int | float) : HvExpr = makeExpr makenum n

func makeExpr*(v : HvVal) : HvExpr =
    if v.kind == Num:
        return makeExpr v.nVal
    else: return v.eVal

func `==`*(a, b : HvNum) : bool =
    if a.isInt:
        if b.isInt:
            return a.iVal == b.iVal
        let (bi, bf) = splitDecimal b.fVal
        return bf.trunc.almostEqual(0.0) and bi.int == a.iVal
    else:
        if b.isInt:
            let (ai, af) = splitDecimal a.fVal
            return ai.int == b.iVal and af.almostEqual 0.0
        return b.fVal.almostEqual a.fVal

func `==`*(a : HvNum, b : int | float) : bool = a == makenum b

func `===`*(e, e1 : HvExpr) : bool = ## Strict and stupid equality, not the same as checking if an expression is equal to another
    if e.kind == e1.kind:
        if e.kind in numerics:
            return e.nVal == e1.nVal
        elif e.val == e1.val and e.kids.len == e1.kids.len:
            for i in 0..<e.kids.len:
                if not (e[i] === e1[i]):
                    return false
            return true
    return false

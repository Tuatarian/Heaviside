import strutils, sequtils, tables, zero_functional, strformat, parlex, macros, sugar, typeinfo

## We're using an object variant here since I (obviously) don't want to make the user decide whether a number should be a float or an int in a CAS
## Also, we're going to require significantly different handling for ints than floats, for example 3/4 should not be converted to 0.75

type HvType = enum
    Num, Expr

type HvExpr = ASTNode

type HvVal = object  # Using this for things who's types are unknown (like unevaluated parameters)
    case kind : HvType
    of Num: nVal : HvNum
    of Expr: eVal : HvExpr

#-------Convenience funcs-------#)

func `$`(p : pointer) : string = "0x" & cast[int](p).toHex

func nType(n : HvNum) : NKind =
    if n.isInt: return NkIntLit
    else: return NkFloatLit

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

func `$`(v : HvVal) : string =
    case v.kind:
    of Num: $v.nVal
    of Expr: !v.eVal

proc print(v : HvVal) =
    case v.kind:
    of Num: echo v.nVal
    of Expr: print(v.eVal, 0)

func makeExpr(a : HvNum, p : ASTNode = nil) : HvExpr = 
    if a.isInt:
        return HvExpr(kind : NkIntLit, nVal : a, parentalUnit : p)
    else:
        return HvExpr(kind : NkFloatLit, nVal : a, parentalUnit : p)

func makeExpr(k : NKind, v : string = "", n : HvNum = makenum 0, p : HvExpr = nil, childs : seq[HvExpr] = @[]) : HvExpr {.inline.} =
    result = HvExpr(kind : k, kids : childs, parentalUnit : p)
    if result.kind in numerics:
        result.nVal = n
    else:
        result.val = v

func `===`(e, e1 : HvExpr) : bool = ## Strict and stupid equality, not the same as checking if an expression is equal to another
    if e.kind == e1.kind and e.val == e1.val and e.kids.len == e1.kids.len:
        for i in 0..<e.kids.len:
            if not (e[i] === e1[i]):
                return false
        return true
    return false

#---------Tree Transformation Functions---------#

func likeTerms(e, e1 : HvExpr) : bool =
    if e.kind == NkCall and e1.kind == NkCall and !e == "*" and !e1 == "*":
        var terms : seq[HvExpr]
        for kid in e.kids:
            if kid.kind == NkIdent:
                terms.add kid

        for kid in e1.kids:
            if kid.kind == NkIdent:
                if terms.len == 0: return false
                for i in 0..<terms.len:
                    if terms[i] === kid:
                        terms.del(i)
                        break
                    if i == terms.len - 1: return false

        return terms.len == 0

#-------HvFuncs-------#
# We'll prefix the versions of functions used by heaviside with hv to avoid confusion, so `/` (division) will be hvDiv, etc

# Also, to make my life easier, we'll overload everything so that I can use the same syntax for casting down the line

# Perhaps the sum function should be different, maybe variadic, so I'll call the `+` operator as hvPlus for now
func hvPlus(a, b : HvNum) : HvExpr =
    if a.isInt and b.isInt:
        return makeExpr makenum(a.iVal + b.iVal)
    elif a.isInt:
        return makeExpr makenum(b.fVal + a.iVal.float)
    elif b.isInt:
        return makeExpr makenum(b.iVal.float + a.fVal)
    return makeExpr makenum(b.fVal + a.fVal)
# The above doesn't handle exprs, we'll need to do that differently

func hvPlus(a : HvNum, e : HvExpr) : HvExpr =
    result = HvExpr(kind : NkCall, val : "+")
    result.add makeExpr(a, result)
    e.reparentTo result

func hvPlus(e, e1 : HvExpr) : HvExpr =
    result = HvExpr(kind : NkCall, val : "+")
    reparentTo(e, e1, result)

func hvMinus(a, b : HvNum) : HvExpr {.inline.} = hvPlus(a, -b)

func hvMinus(l, r : HvExpr) : HvExpr =
    if l === r:
        return makeExpr makenum 0
    else:
        return hvPlus(l, r)

func hvMinus(a : HvNum, e : HvExpr) : HvExpr =
    result = makeExpr(NkCall, "-").add makeExpr(a, result)
    e.reparentTo result

func hvMinus(e : HvExpr, a : HvNum) : HvExpr = hvMinus(-a, makeExpr(NkCall, "-").add(makeExpr makenum 0, e))

func hvTimes(a, b : HvNum) : HvExpr =
    if a.isInt and b.isInt:
        return makeExpr makenum(a.iVal * b.iVal)
    elif a.isInt:
        return makeExpr makenum(a.iVal.float * b.fVal)
    elif b.isInt:
        return makeExpr makenum(a.fVal * a.iVal.float)
    return makeExpr makenum(a.fVal * b.fVal)

func hvTimes(e : HvExpr, a : HvNum) : HvExpr =
    result = HvExpr(kind : NkCall, val : "*")
    result.add makeExpr(a, result)
    e.reparentTo result

func hvTimes(a : HvNum, e : HvExpr) : HvExpr = hvTimes(e, a) # multiplication is commutative

func hvTimes(e, e1 : HvExpr) : HvExpr =
    result = HvExpr(kind : NkCall, val : "*")
    reparentTo(e, e1, result)

func hvPlus(e : HvExpr, a : HvNum) : HvExpr {.inline.} = hvPlus(a, e) # addition is commutative

#-------Building the Function Table-------#

func callMagicFunc(id : string, args : seq[HvVal]) : HvExpr =
    case id:
    of "+ HvNum HvNum ":
        return hvPlus(args[0].nVal, args[1].nVal)
    of "+ HvExpr HvNum ", "+ HvNum, HvExpr ":
        if args[0].kind == Num:
            return hvPlus(args[0].nVal, args[1].eVal)
        else:
            return hvPlus(args[0].eVal, args[1].nVal)
    of "- HvNum HvNum ":
        return hvMinus(args[0].nVal, args[1].nVal)
    of "- HvExpr HvExpr ":
        return hvMinus(args[0].eVal, args[1].eVal)
    of "- HvExpr HvNum ", "- HvNum HvExpr ":
        if args[0].kind == Num:
            return hvMinus(args[0].nVal, args[1].eVal)
        else:
            return hvMinus(args[0].eVal, args[1].nVal)
    of "* HvNum HvNum ":
        return hvTimes(args[0].nVal, args[1].nVal)
    of "* HvNum HvExpr ", "* HvExpr HvNum ":
        if args[0].kind == Num:
            return hvTimes(args[0].nVal, args[1].eVal)
        else:
            return hvTimes(args[0].eVal, args[1].nVal)

    else: raise newException(Defect, &"Undefined function {id}")


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

proc evalTree(rt : ASTNode) : (HvVal, HvType) =
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
                params.add HvVal(kind : Num, nVal : k.nVal)
            of NkFloatLit:
                paramTypes &= "HvNum "
                params.add HvVal(kind : Num, nVal : k.nVal)
            of NkCall:
                var res = evalTree k
                if res[0].eVal.kind in numerics:
                    params.add makeval res[0].eVal.nVal
                    paramTypes &= "HvNum "
                else:
                    paramTypes &= "HvExpr "
                    params.add res[0]
            else:
                echo "Unexpected Node Kind in tree evaluation"
                writeStackTrace()
        
        result[0] = makeval callMagicFunc(paramTypes, params)
        print result[0]
        debugEcho (paramTypes, params)
        echo "~~>"
        result[1] = result[0].kind

var rt = strParse readFile("./symbols.txt").splitLines[6]
print rt
echo "/============================/"
print evalTree(rt[0])[0]
echo likeTerms(strParse("ya * 8")[0], strParse("ay * 8")[0])
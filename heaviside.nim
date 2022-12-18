import strutils, tables, zero_functional, strformat, parlex, math

## We're using an object variant here since I (obviously) don't want to make the user decide whether a number should be a float or an int in a CAS
## Also, we're going to require significantly different handling for ints than floats, for example 3/4 should not be converted to 0.75

type HvType = enum
    Num, Expr, Str

type HvExpr = ASTNode

type HvVal = object  # Using this for things who's types are unknown (like unevaluated parameters)
    case kind : HvType
    of Num: nVal : HvNum
    of Expr: eVal : HvExpr
    of Str: sVal : string

#-------Convenience funcs-------#)

func `$`(p : pointer) : string = "0x" & cast[int](p).toHex

func nType(n : HvNum) : NKind =
    if n.isInt: return NkIntLit
    else: return NkFloatLit

template hvType(n : NKind) : HvType =
    case n:
    of NkIntLit, NkFloatLit: Num
    of NkStrLit: Str
    else: Expr

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
    of Str: v.sVal

proc print(v : HvVal) =
    case v.kind:
    of Num: echo v.nVal
    of Expr: print(v.eVal, 0)
    of Str: echo v.sVal

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

func makeExpr(n : int | float) : HvExpr = makeExpr makenum n

func `==`(a, b : HvNum) : bool =
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

func `==`(a : HvNum, b : int | float) : bool = a == makenum b

func `===`(e, e1 : HvExpr) : bool = ## Strict and stupid equality, not the same as checking if an expression is equal to another
    if e.kind == e1.kind:
        if e.kind in numerics:
            return e.nVal == e1.nVal
        elif e.val == e1.val and e.kids.len == e1.kids.len:
            for i in 0..<e.kids.len:
                if not (e[i] === e1[i]):
                    return false
            return true
    return false

#---------Tree Transformation Functions---------#

func isConst(e : HvExpr, wrt : string) : bool =
    if e.kind in numerics or e.kind == NkIdent and e.val != wrt: return true

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

# Also, to maintain sanity, also since it's just objectively a good idea, we'll overload definitions of different versions of the same operation

func hvTimes(a, b : HvNum) : HvExpr =
    if a == makenum 0:
        return makeExpr 0
    elif b == makenum 0:
        return makeExpr 0
    elif a == makenum 1:
        return makeExpr b
    elif b == makenum 1:
        return makeExpr a

    if a.isInt and b.isInt:
        return makeExpr makenum(a.iVal * b.iVal)
    elif a.isInt:
        return makeExpr makenum(a.iVal.float * b.fVal)
    elif b.isInt:
        return makeExpr makenum(a.fVal * a.iVal.float)
    return makeExpr makenum(a.fVal * b.fVal)

func hvTimes(e : HvExpr, a : HvNum) : HvExpr =
    if a == makenum 0:
        return makeExpr 0
    elif a == makenum 1:
        return e

    result = makeExpr(NkCall, "*").add(makeExpr a, e)

func hvTimes(a : HvNum, e : HvExpr) : HvExpr = hvTimes(e, a) # multiplication is commutative

func hvTimes(e, e1 : HvExpr) : HvExpr =
    if e.kind in numerics:
        if e.nVal == makenum 0:
            return makeExpr 0
        elif e.nVal == makenum 1:
            return e1
    elif e1.kind in numerics:
        if e1.nVal == makenum 0:
            return makeExpr 0
        elif e1.nVal == makenum 1:
            return e
    
    elif e === e1:
        return makeExpr(NkCall, "^").add(e, makeExpr 2)

    return makeExpr(NkCall, "*").add(e, e1)

# Perhaps the sum function should be different, maybe variadic, so I'll call the `+` operator hvPlus for now
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
    result = makeExpr(NkCall, "+").add(makeExpr a, e)

func hvPlus(e, e1 : HvExpr) : HvExpr =
    if e === e1:
        return hvTimes(makenum 2, e)

    result = HvExpr(kind : NkCall, val : "+")
    reparentTo(e, e1, result)


# Minus should be different to let elements of the expr tree die faster
func hvMinus(a, b : HvNum) : HvExpr {.inline.} = hvPlus(a, -b)

func hvMinus(l, r : HvExpr) : HvExpr =
    if l === r:
        return makeExpr makenum 0
    else:
        return makeExpr(NkCall, "-").add(l, r)

func hvMinus(a : HvNum, e : HvExpr) : HvExpr =
    result = makeExpr(NkCall, "-").add(makeExpr a, e)

func hvMinus(e : HvExpr, a : HvNum) : HvExpr =
    if a == 0:
        return e

    return makeExpr(NkCall, "-").add(e, makeExpr a)

func hvPlus(e : HvExpr, a : HvNum) : HvExpr {.inline.} = hvPlus(a, e) # addition is commutative

func hvDiv(a, b : HvNum) : HvExpr =
    if a.isInt and b.isInt:
        return makeExpr(NkCall, "/").add(makeExpr a, makeExpr b)
    elif a.isInt:
        return makeExpr a.iVal.float/b.fVal
    elif b.isInt:
        return makeExpr a.fVal/b.iVal.float
    else:
        return makeExpr a.fVal/b.fVal

func hvDiv(e, e1 : HvExpr) : HvExpr =
    if e === e1:
        return makeExpr 1
    else:
        return makeExpr(NkCall, "/").add(e, e1)

func hvDiv(a : HvNum, e : HvExpr) : HvExpr =
    return makeExpr(NkCall, "/").add(makeExpr a, e)

func hvDiv(e : HvExpr, a : HvNum) : HvExpr =
    return makeExpr(NkCall, "/").add(e, makeExpr a)

func hvPow(a, b : HvNum) : HvExpr =
    if b == makenum 0:
        return makeExpr 1
    elif a == makenum 0:
        return makeExpr 0

    elif b == 1:
        return makeExpr a
    elif a == 1:
        return makeExpr 1

    if a.isInt:
        if b.isInt:
            if b.iVal < 0:
                return makeExpr(NkCall, "/").add(makeExpr 1, makeExpr(a.iVal ^ abs(b.iVal)))
            return makeExpr a.iVal ^ b.iVal
        else:
            return makeExpr a.iVal.float.pow(b.fVal)
    else:
        if b.isInt:
            return makeExpr a.fVal.pow(b.iVal.float)
        else:
            return makeExpr a.fVal.pow(b.fVal)

func hvPow(a : HvNum, e : HvExpr) : HvExpr =
    if a == makenum 0:
        return makeExpr 0
    if a == makenum 1:
        return makeExpr 1
    
    return makeExpr(NkCall, "^").add(makeExpr a, e)

func hvPow(e : HvExpr, a : HvNum) : HvExpr =
    if a == 0:
        return makeExpr 1
    elif a == 1:
        return e

    return makeExpr(NkCall, "^").add(e, makeExpr a)

func hvPow(e, e1 : HvExpr) : HvExpr =
    return makeExpr(NkCall, "^").add(e, e1)




func hvExp(a : Hvnum) : HvExpr =
    if a == makenum 0:
        return makeExpr 1

    return makeExpr(NkCall, "exp").add(makeExpr a)

func hvExp(e : HvExpr) : HvExpr =
    if e === makeExpr 0:
        return makeExpr 1

    elif e.kind == NkCall and e.val == "ln":
        return e[0]

    else:
        return makeExpr(NkCall, "exp").add(e)

func hvLn(a : HvNum) : HvExpr =
    if op(a, makenum 0, `<=`):
        raise newException(Defect, "cannot take ln of a nonpositive value")

    return makeExpr(NkCall, "ln").add(makeExpr a)

func hvLn(e : HvExpr) : HvExpr =
    if e.kind == NkCall and e.val == "exp":
        return e[0]
    else:
        return makeExpr(NkCall, "ln").add(e)


#--------Differentiation---------#

func diff(e : HvExpr, wrt : string) : HvExpr =
    case e.kind:
    of NkIntLit, NkFloatLit: return makeExpr 0
    of NkIdent: 
        if !e == wrt: return makeExpr 1
        else: return makeExpr 0
    of NkCall:

        if e.val == "*":
            # This will be the product rule, but if either of these two terms is constant, we can save some space
            if e[0].isConst(wrt):
                if e[1].isConst(wrt):
                    return makeExpr 0
                return makeExpr(NkCall, "*").add(e[0], diff(e[1], wrt))
            elif e[1].isConst(wrt):
                return makeExpr(NkCall, "*").add(e[1], diff(e[0], wrt))
            else:
                # And this is the product rule
                return makeExpr(NkCall, "+").add(
                    makeExpr(NkCall, "*").add(
                        diff(e[0], wrt), e[1]
                    ), makeExpr(NkCall, "*").add(
                        e[0], diff(e[1], wrt)
                    )
                )

        elif e.val == "+":
            # We can save some space here by not doing an addition if any of the terms are constants
            if e[0].isConst(wrt):
                if e[1].isConst(wrt):
                    return makeExpr 0
                else:
                    return diff(e[1], wrt)
            elif e[1].isConst(wrt):
                return diff(e[0], wrt)
            else:
                # diff(a + b) = diff(a) + diff(b)
                return makeExpr(NkCall, "+").add(diff(e[0], wrt), diff(e[1], wrt))

        elif e.val == "-":
            # This is the same thing as addition, but I will leave it separate until I figure out how to handle negative numbers
            if e[0].isConst(wrt):
                # We only have the diff(e[1]) = 0 case since atm, -a is represented as 0 - a
                if e[1].isConst(wrt):
                    return makeExpr 0
                else:
                    return diff(e[0], wrt)
            else:
                # diff(a - b) = diff(a) - diff(b)
                return makeExpr(NkCall, "-").add(diff(e[0], wrt), diff(e[1], wrt))

        elif e.val == "/":
            if e[0].isConst(wrt):
                if e[1].isConst(wrt):
                    return makeExpr 0
                else:
                    return makeExpr(NkCall, "/").add(diff(e[0], wrt), e[1])
            elif e[1].isConst(wrt):

                # Reciprocal rule, subset of quotient rule, makes a smaller tree
                return makeExpr(NkCall, "*").add(
                    makeExpr(NkCall, "/").add(
                        diff(e[1], wrt), makeExpr(NkCall, "^").add(e[1], makeExpr 2)
                    ), makeExpr -e[0].nVal
                )
            else:

                # And this is the Quotient Rule, fairly messy
                return makeExpr(NkCall, "/").add(
                    makeExpr(NkCall, "-").add(
                        makeExpr(NkCall, "*").add(
                            diff(e[0], wrt), e[1]
                        ), makeExpr(NkCall, "*").add(
                            diff(e[1], wrt), e[0]
                        )
                    ), makeExpr(NkCall, "^").add(e[1], makeExpr 2)
                )
        
        elif e.val == "^":
            if e[1].isConst(wrt): # if g in f^g is constant
                if e[0].isConst(wrt):
                    return makeExpr 0
                
                elif e[0].kind == NkIdent: # Power/Monomial rule
                    
                    return makeExpr(NkCall, "*").add(
                        makeExpr e[1].nVal,
                        makeExpr(NkCall, "^").add(
                            e[0], makeExpr(e[1].nVal - 1)
                        )
                    )

                else: # General case when d(f) is not 1
                    return makeExpr(NkCall, "*").add(
                        makeExpr(NkCall, "*").add(
                            makeExpr e[1].nVal,
                            makeExpr(NkCall, "^").add(
                                e[0], makeExpr(e[1].nVal - 1)
                            )
                        ), diff(e[0], wrt)
                    )
            else:

                # Full exponent rule
                return makeExpr(NkCall, "*").add(
                    hvPow(e[0], e[1]),
                    makeExpr(NkCall, "+").add(
                        makeExpr(NkCall, "*").add(
                            diff(e[1], wrt), hvLn(e[0])
                        ), makeExpr(NKCall, "/").add(
                            makeExpr(NkCall, "*").add(e[1], diff(e[0], wrt)), e[0]
                        )
                    )
                )
                

            

    else: raise newException(Defect, &"Can't differentiate an {e.kind}")



#-------Calling builtin Functions-------#

proc evalTree(rt : ASTNode) : HvExpr # Forward decl, for immediate simplification of complex ops

proc callMagicFunc(id : string, args : seq[HvVal]) : HvExpr =
    case id:
    of "+ HvNum HvNum ":
        return hvPlus(args[0].nVal, args[1].nVal)
    of "+ HvExpr HvNum ", "+ HvNum HvExpr ":
        if args[0].kind == Num:
            return hvPlus(args[0].nVal, args[1].eVal)
        else:
            return hvPlus(args[0].eVal, args[1].nVal)
    of "+ HvExpr HvExpr ":
        return hvPlus(args[0].eVal, args[1].eVal)


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
    of "* HvExpr HvExpr ":
        return hvTimes(args[0].eVal, args[1].eVal)


    of "/ HvNum HvNum ":
        return hvDiv(args[0].nVal, args[1].nVal)
    of "/ HvNum HvExpr ", "/ HvExpr HvNum ":
        if args[0].kind == Num:
            return hvDiv(args[0].nVal, args[1].eVal)
        else:
            return hvDiv(args[0].eVal, args[1].nVal)
    of "/ HvExpr HvExpr ":
        return hvDiv(args[0].eVal, args[1].eVal)


    of "^ HvNum HvNum ":
        return hvPow(args[0].nVal, args[1].nVal)
    of "^ HvNum HvExpr ", "^ HvExpr HvNum ":
        if args[0].kind == Num:
            return hvPow(args[0].nVal, args[1].eVal)
        else:
            return hvPow(args[0].eVal, args[1].nVal)
    of "^ HvExpr HvExpr ":
        return hvPow(args[0].eVal, args[1].eVal)

    of "ln HvExpr ":
        return hvLn(args[0].eVal)
    of "ln HvNum ":
        return hvLn(args[0].nVal)

    of "exp HvExpr ":
        return hvExp(args[0].eVal)
    of "exp HvNum ":
        return hvExp(args[0].nVal)


    of "diff HvExpr Str ":
        return evalTree(diff(args[0].eVal, args[1].sVal))
    
    else:
        for arg in args:
            print arg
        raise newException(Defect, &"Undefined function {id}")


#----------Tree Walking Code----------#
  
# General idea for this part

# DFS to go down the tree
# At each call, the child nodes are either HvNums or Exprs or Str
# If we have an ident, then it is by default an expr
# If we have a NumLit, it is by default an HvNum
# If we have a node with children, then we recursively do the above to that node
# At the end, we'd need to have a way to pass that up
# For now, I'll do this by returning a tuple of (HvVal, HvType)
    # is the result of applying the function to the node (quite possibly an expr)
    # The type is the type of the node (NumLit or Expr)
    # This might move onto the tree itself at some point in the future

proc evalTree(rt : ASTNode) : HvExpr =
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
            of NkStrLit:
                paramTypes &= "Str "
                params.add HvVal(kind : Str, sVal : !k)
            of NkCall:
                var res = evalTree k
                if res.kind in numerics:
                    params.add makeval res.nVal
                    paramTypes &= "HvNum "
                else:
                    paramTypes &= "HvExpr "
                    params.add makeval res
            else:
                echo "Unexpected Node Kind in tree evaluation"
                writeStackTrace()
        
        # debugEcho (paramTypes, params)
        result = callMagicFunc(paramTypes, params)
        # print result
        # echo "~~>"
    else:
        result = deepCopy rt

var rt = strParse readFile("./symbols.txt").splitLines[6]
print rt
echo "/============================/"
print evalTree(rt[0])
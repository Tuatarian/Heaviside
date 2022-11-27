import strutils, sequtils, tables, zero_functional, strformat, parlex, macros


## We're using an object variant here since I (obviously) don't want to amke the user decide whether a number should be a float or an int
## Also, we're going to require significantly different handling for ints than floats, for example 3/4 should not be converted to 0.75

type HvType = enum
    NumLit, Expr

type HvNum = object
    case isInt : bool
    of true: iVal : int
    of false: fVal : float

type HvExpr = ASTNode

#-------Convenience funcs-------#

func `$`(p : pointer) : string = "0x" & cast[int](p).toHex

template makenum(b : int | float) : untyped =
    when b is int:
        HvNum(isInt : true, iVal : b)
    else:
        HvNum(isInt : false, fVal : b)

func `-`(a : HvNum) : HvNum =
    if a.isInt: return makenum(-a.iVal)
    else: return makenum(-a.fVal)

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

macro bldFuncTable(t : typed) : untyped =
    result = newNimNode(nnkTableConstr)
    case t.kind
    of nnkSym:
        let res = repr t.getType[1]
        var argL : seq[NimNode]
        var args = "("
        
        for i in 2..<t.getType.len - 1:
            args &= &"{repr t.getType[i]}, "
            argL.add(newIdentDefs(ident("a" & $(i - 2)), ident(repr t.getType[i]), newEmptyNode()))
        args &= &"{repr t.getType[^1]})"
        argL.add(newIdentDefs(ident("a" & $(argL.len)), ident(repr t.getType[^1]), newEmptyNode()))

        result.add newNimNode(nnkExprColonExpr).add(
            newLit(&"{repr t}: {args} -> {res}"), newNimNode(nnkCommand).add(
                ident("pointer"), newNimNode(nnkPar).add(
                    newNimNode(nnkCall).add(
                        newNimNode(nnkPar).add(
                            newNimNode(nnkProcTy).add(
                                newNimNode(nnkFormalParams).add(
                                    ident(res))))))))
        for arg in argL:
            result[0][1][1][0][0][0][0].add arg
        
        result[0][1][1][0][0][0].add newNimNode(nnkPragma).add ident("nimcall")
        result[0][1][1][0].add ident(repr t)

    of nnkOpenSymChoice, nnkClosedSymChoice:
        var counter : int
        for x in t:
            let res = repr x.getType[1]
            var args = "("
            var argL : seq[NimNode]

            for i in 2..<x.getType.len - 1:
                args &= &"{repr x.getType[i]}, "
                argL.add(newIdentDefs(ident("a" & $(i - 2)), ident(repr x.getType[i])))
            args &= &"{repr x.getType[^1]})"
            argL.add(newIdentDefs(ident("a" & $(argL.len)), ident(repr x.getType[^1]), newEmptyNode()))

            result.add newNimNode(nnkExprColonExpr).add(
                newLit(&"{repr x}: {args} -> {res}"), newNimNode(nnkCommand).add(
                    ident("pointer"), newNimNode(nnkPar).add(
                        newNimNode(nnkCall).add(
                            newNimNode(nnkPar).add(
                                newNimNode(nnkProcTy).add(
                                    newNimNode(nnkFormalParams).add(
                                        ident(res))))))))

            for arg in argL:
                result[counter][1][1][0][0][0][0].add arg

            result[counter][1][1][0][0][0].add newNimNode(nnkPragma).add ident("nimcall")
            result[counter][1][1][0].add ident(repr x)
            counter += 1
    else:
        error("Did not get a proc, probably a bug", t)
    echo treeRepr result

echo toTable bldFuncTable(contains)

#----------Tree Walking Code----------#
  

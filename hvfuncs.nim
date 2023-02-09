import parlex, hvcore

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


func orderCmp(a, b : HvExpr) : int = ## 1 if a before b, -1 if a after b, 0 if of same order
    if int(a.kind) < int(b.kind):
        return 1
    elif int(a.kind) > int(b.kind):
        return -1
    else:
        if a.kind == NkIntLit or a.kind == NkFloatLit: return int(a.nVal < b.nVal) # sort ints, floats in descending order
        elif a.kind == NkIdent:
            if (!a).len == (!b).len: # if they're the same length
                for i in 0..<(!a).len: # Find the first char that isn't the same, return cmp of that (lowest first)
                    if (!a)[i] != (!b)[i]:
                        return system.cmp[char]((!a)[i], (!b)[i])
                    elif i == (!a).len - 1: # if chars are all the same
                        return 0
            else: return int((!a).len < (!b).len) # sort by length in descending order
        elif a.kind == NkCall:
            if !a == "^":
                if !b == "^":
                    if a[1] === b[1]:
                        return 0
                    else:
                        if a[1].kind in numerics and b[1].kind in numerics:
                            return int(a[1].nVal > b[1].nVal)
                        else:
                            return orderCmp(a[1], b[1])
                return 1
            elif !b == "^":
                return -1
            else:
                if !a == !b:
                    return 0
                return int(!a < !b)


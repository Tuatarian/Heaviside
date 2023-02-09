import strutils, tables, zero_functional, strformat, parlex, math, algorithm, hvcore

func isPoly*(e : HvExpr) : (bool, HvExpr) =

    var variable = ""
    let falseRet = (false, HvExpr())
    
    if e.kind == NkCall and !e == "+":
        for kid in e.kids:

            # Either a number, ident, or power

            if kid.kind in numerics: continue # numbers always fine

            elif kid.kind == NkIdent:
                if variable != "":
                    if !kid == variable:
                        continue # if the kid is the same value as the the variable we're checking if its a polynomial in, we're good
                    else:
                        return falseRet
                else:
                    variable = !kid
                    continue

            elif kid.kind == NkCall and !kid == "*" and kid.kids.len <= 2:

                # Unary products are not a thing, so kid.kids.len == 2

                if kid[0].kind notin numerics: return falseRet # The first thing should be a constant

                # kid[1] is either an Ident or a ^
                
                elif kid[1].kind == NkIdent:
                    if variable != "":
                        if !kid[1] == variable:
                            continue
                        else:
                            return falseRet
                    else:
                        variable = !kid[1]
                        continue

                elif kid[1].kind == NkCall and !kid[1] == "^":

                    # This should be an ^(Ident, int)

                    if kid[1][0].kind != NkIdent or kid[1][1].kind != NkIntLit: return falseRet

                    if variable != "":
                        if !kid[1][0] == variable:
                            continue
                        else:
                            return falseRet
                    else:
                        variable = !kid[1][0]
                        continue

            else: return falseRet

        return (true, makeExpr(NkIdent, variable))
            
    elif e.kind == NkCall and !e == "*":
    
            # Unary products are not a thing, so e.kids.len == 2

            if e[0].kind notin numerics: return falseRet # The first thing should be a constant

            # e[1] is either an Ident or a ^
            
            elif e[1].kind == NkIdent:
                return (true, makeExpr(NkIdent, !e[1]))

            elif e[1].kind == NkCall and !e[1] == "^":

                # This should be an ^(Ident, int)

                if e[1][0].kind != NkIdent or e[1][1].kind != NkIntLit: return falseRet

                else: return (true, makeExpr(NkIdent, !e[1][0]))

            else: return falseRet

    elif e.kind == NkIdent: return (true, makeExpr(NkIdent, !e))
    
    elif e.kind == NkCall and !e == "^":

        # This should be an ^(Ident, int)

        if e[0].kind != NkIdent or e[1].kind != NkIntLit: return falseRet

        else: return (true, makeExpr(NkIdent, !e[0]))

    else: return falseRet        

                                    

    
func pullCoeff(p : HvExpr) : (HvVal, int) = # (coeff, deg)
    discard
    


func extractPoly(p : HvExpr) : (seq[HvVal], HvExpr) = ## Assumes p is a polynomial, should return a (seq[coeffs], Ident - polynomial is in)
    discard

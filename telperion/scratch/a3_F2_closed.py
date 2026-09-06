"""
F2 CLOSED-FORM CRUX: single pendant leaf moved from hub u onto a LEAF-neighbor v (path extend).

Config, rooted so u is the root (root-invariance): u = node([v, w] + rest_u), where
  w = leaf (the pendant being moved), v = leaf (target, dv=1), rest_u = u's other children.
AFTER: u = node([ node([w]) ] + rest_u)  -- v extended into a stem carrying w.

Let the rest_u block summarize as: product P>0 of child Ztots, and Q = qSum(rest_u) >= 0,
and let n = |rest_u| (# other children).  BEFORE u has degree (root childcount) = n+2;
AFTER u has degree n+1.  We compute Aobj(u) = Ztot at root degree = childcount, via
   Aobj(node cs) = P_all * (1 + qSum(cs)/deg),  deg=childcount.

Leaf w: Ztot=1, Zopen=1, udeg=1, q-contrib = 1/1/1 = 1... wait udeg(leaf)=1 => qcontrib=
   Zopen/Ztot/udeg = 1/1/1 = 1.  Leaf v same.  node([w]) (a stem): childcount1,udeg=2,
   Ztot(dtSub stem)=3/2, Zopen=1 => qcontrib = 1/(3/2)/2 = 1/3.
"""
import sympy as sp
P, Q, n = sp.symbols('P Q n', positive=True)  # rest_u: product, qSum, count (n>=0; treat >0 general)
# BEFORE: children of root u = [v(leaf), w(leaf)] + rest_u ; childcount = n+2
# qSum_before = qcontrib(v)+qcontrib(w)+Q = 1 + 1 + Q = Q+2 ; P_before = 1*1*P = P
deg_b = n+2
Aobj_b = P*(1 + (Q+2)/deg_b)
# AFTER: children = [ stem=node([w]) ] + rest_u ; childcount = n+1
# qcontrib(stem)=1/3 ; Ztot(stem-as-child dtSub)=3/2 ; P_after = (3/2)*P
deg_a = n+1
Aobj_a = (sp.Rational(3,2)*P)*(1 + (sp.Rational(1,3)+Q)/deg_a)

delta = sp.simplify(Aobj_a - Aobj_b)
print("F2 single-pendant path-extension increment  Aobj_after - Aobj_before:")
print("  delta =", sp.factor(delta))
numer,denom = sp.fraction(sp.together(delta))
print("  numerator (expand) =", sp.expand(numer))
print("  denominator =", sp.factor(denom))
# positivity: n>=0 integer, Q>=0, P>0.  Check numerator >=0.
print("\nSign analysis (P>0 factored out):")
core = sp.factor(sp.expand(numer)/P) if (sp.expand(numer)/P).free_symbols<= {Q,n} else sp.expand(numer)
print("  numerator/P =", sp.expand(numer/P))
# is it >=0 for n>=0,Q>=0?  collect
poly = sp.Poly(sp.expand(numer/P), n, Q)
print("  as poly in (n,Q):", poly)
print("  coeffs:", poly.terms())
# minimal over n>=0,Q>=0: check corners and derivative sign
expr=sp.expand(numer/P)
print("  at n=0,Q=0:", expr.subs({n:0,Q:0}))
print("  at Q=0 general n:", sp.factor(expr.subs({Q:0})))
print("  d/dn at Q=0:", sp.diff(expr.subs({Q:0}),n))
print("  d/dQ:", sp.factor(sp.diff(expr,Q)))

# ---- numeric verification of the closed form against the exact engine ----
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, qSum as qSum_eng, P_of, LEAF
from fractions import Fraction as Fr
import random
def qcontrib_list(cs):
    from a3_derisk import qContrib
    return sum((qContrib(c) for c in cs), Fr(0))
rng=random.Random(0)
def rnd(depth):
    if depth<=0 or rng.random()<0.4: return LEAF
    return tuple(rnd(depth-1) for _ in range(rng.randint(1,3)))
ok=0
for _ in range(2000):
    restu=[rnd(3) for _ in range(rng.randint(0,4))]
    # BEFORE root u = [leaf(v), leaf(w)] + restu ; AFTER = [node([leaf])] + restu
    tb=tuple([LEAF, LEAF]+restu)
    ta=tuple([tuple([LEAF])]+restu)
    delta_eng = Aobj_node(ta)-Aobj_node(tb)
    Pv = P_of(restu); Qv = qcontrib_list(restu); nn=len(restu)
    delta_cf = Pv*(nn**2 + Qv*nn + 4*Qv)/(2*(nn+1)*(nn+2))
    assert delta_eng==delta_cf, (restu, delta_eng, delta_cf)
    ok+=1
print(f"\n[verify] F2 closed form == exact engine on {ok} random rest_u blocks.  OK")

"""GATE G-R2: Case-B symmetric base case, parametric straightening move.

k-star kstar = node[leaf x k] = tuple([()]*k)   (a SUBTREE / child)
T_before = node[kstar, kstar]                    root children = (kstar, kstar)
T_after: relocate one kstar onto a LEAF of the other; root gets single child.
   first kstar's children [()]*k -> replace one leaf () with a stem carrying
   the second kstar: node[kstar] = (kstar,).  modified subtree M =
      ((),)*(k-1) + ((kstar,),)
   root now has single child M:  cs_after = (M,)

We compute Aobj_node(cs) EXACTLY (fractions) for k = 2..12.
Verdict HOLDS iff dAobj = Aobj_after - Aobj_before == 0 for all k.
"""
from fractions import Fraction as Fr
from a3_derisk import Aobj_node

LEAF = ()

def kstar(k):
    return tuple([LEAF]*k)          # node[leaf x k] as a subtree

results = []
allzero = True
for k in range(2, 13):
    ks = kstar(k)
    # T_before: root with two k-star children
    cs_before = (ks, ks)
    # T_after: one leaf of first kstar replaced by node[kstar]=(kstar,);
    #          root has single child.
    M = tuple([LEAF]*(k-1)) + ((ks,),)   # modified first k-star
    cs_after = (M,)                       # root single child
    Ab = Aobj_node(cs_before)
    Aa = Aobj_node(cs_after)
    d  = Aa - Ab
    if d != 0:
        allzero = False
    results.append((k, Ab, Aa, d))

print("k  Aobj_before                          Aobj_after                           dAobj")
for k, Ab, Aa, d in results:
    print(f"{k:2d}  {str(Ab):34s} {str(Aa):34s} {d}")

print()
print(f"dAobj == 0 for all k in 2..12 ? {allzero}")

# Try to fit a closed form for Aobj(k) (they are equal before==after when tie holds)
print()
print("Closed-form attempt for Aobj_before(k):")
for k, Ab, Aa, d in results:
    # Aobj_before as exact fraction
    print(f"  k={k:2d}: before = {Ab}   (num={Ab.numerator}, den={Ab.denominator})")

# Guess: kstar as subtree at udeg=k+1. Two children each kstar.
# print numerators/denominators to spot a pattern
print()
print("Sanity: also verify with Ztot_at_degree cross-check import")
from a3_derisk import Ztot_at_degree
ok = all(Aobj_node(cs) == Ztot_at_degree(cs, len(cs))
         for cs in [(kstar(k),kstar(k)) for k in range(2,13)])
print(f"  Aobj_node matches Ztot_at_degree(len): {ok}")

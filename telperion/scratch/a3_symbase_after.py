"""Cavity pieces of the after tree, to plan the Lean proof."""
from fractions import Fraction as Fr
from a3_derisk import Aobj_node, Ztot_sub, Zopen_sub, LEAF, qSum, P_of, udeg

def kstar(k): return tuple([LEAF]*k)

for k in range(2,8):
    ks = kstar(k)
    stem = (ks,)                              # node[kstar k]
    first = tuple([LEAF]*(k-1) + [stem])      # node(replicate (k-1) leaf ++ [stem])
    # cavity of stem as a subtree
    print(f"--- k={k} ---")
    print(f" stem: udeg={udeg(stem)}(should be 2)  Ztot(dtSub stem)={Ztot_sub(stem)}  Zopen={Zopen_sub(stem)}")
    # stem = node[kstar k]. udeg=2. Its single child kstar k has Ztot(dtSub)= (2k+1)/(k+1), Zopen=1, udeg=k+1,
    # weight 1/(2*(k+1)). Popen = Ztot(dtSub kstar)=(2k+1)/(k+1). Matched = w*Zopen*1 = 1/(2(k+1)).
    # Ztot(dtSub stem) = (2k+1)/(k+1) + 1/(2(k+1)) = (2(2k+1)+1)/(2(k+1)) = (4k+3)/(2(k+1)). Zopen=(2k+1)/(k+1).
    print(f"   pred Ztot(dtSub stem)=(4k+3)/(2(k+1))={Fr(4*k+3,2*(k+1))}  Zopen pred=(2k+1)/(k+1)={Fr(2*k+1,k+1)}")
    # first = node(replicate(k-1) leaf ++ [stem]). udeg(first)=(k-1)+1+1 = k+1.
    print(f" first: udeg={udeg(first)}(should be k+1={k+1})  Ztot(dtSub first)={Ztot_sub(first)}  Zopen={Zopen_sub(first)}")
    print(f" Aobj(after)={Aobj_node((first,))}  target (4k+2)/(k+1)={Fr(4*k+2,k+1)}")

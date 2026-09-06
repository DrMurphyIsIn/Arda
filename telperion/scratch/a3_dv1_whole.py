"""Directly verify: dv=1 path-extension reparent is ALWAYS whole-tree Aobj-positive.
Also measure whether the isolated dZtot(u) ever goes negative in REALIZABLE trees, and if so
whether dZopen(u) (parent dressing) rescues it -- to state the correct A3 for dv=1."""
import random, sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Ztot_sub, Zopen_sub, Aobj_node, LEAF

def rnd(depth,rng):
    if depth<=0 or rng.random()<0.4: return LEAF
    return tuple(rnd(depth-1,rng) for _ in range(rng.randint(1,3)))

def run(trials=20000, seed=3):
    rng=random.Random(seed)
    pos=neg=zero=0; dztot_neg=0; dztot_neg_but_whole_pos=0; worst=None
    for _ in range(trials):
        # u has: v(=leaf), B(nonleaf preferred), rest_u; global extra root children
        restu=[rnd(3,rng) for _ in range(rng.randint(0,5))]   # allow many => large nu
        B=rnd(3,rng)
        if B==LEAF: B=(LEAF,)*rng.randint(1,2)
        extra=[rnd(2,rng) for _ in range(rng.randint(0,3))]
        # BEFORE: u=node([leaf, B]+restu); AFTER: v extended: u=node([node([B])]+restu)
        u_b=tuple([LEAF, B]+restu)
        u_a=tuple([tuple([B])]+restu)
        tb=tuple([u_b]+extra); ta=tuple([u_a]+extra)
        m=Aobj_node(ta)-Aobj_node(tb)
        if m>0:pos+=1
        elif m<0:
            neg+=1
            if worst is None or m<worst: worst=m
        else:zero+=1
        dzt=Ztot_sub(u_a)-Ztot_sub(u_b)
        if dzt<0:
            dztot_neg+=1
            if m>=0: dztot_neg_but_whole_pos+=1
    print(f"dv=1 path-extension whole-tree: pos={pos} neg={neg} zero={zero} worst_neg={worst}")
    print(f"  isolated dZtot(u)<0 count: {dztot_neg}  (of those, whole-tree still >=0: {dztot_neg_but_whole_pos})")

if __name__=="__main__":
    run()

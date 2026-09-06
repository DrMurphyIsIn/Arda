"""Pin the EXACT positive family.  The discriminate table clean column was:
   v adjacent to u, du>dv, MOVED w is a single LEAF, and dv=1 (v a leaf).
i.e. relocate ONE LEAF from hub u (deg du) onto a leaf-neighbor v (deg 1), extending a path.
Test that precise move with B = single leaf, and require du>dv=1 (du>=2)."""
import random, sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Ztot_sub, Zopen_sub, Aobj_node, LEAF

def rnd(depth,rng):
    if depth<=0 or rng.random()<0.4: return LEAF
    return tuple(rnd(depth-1,rng) for _ in range(rng.randint(1,3)))

def run(trials=30000, seed=5, B_is_leaf=True, require_du_gt_dv=True):
    rng=random.Random(seed)
    pos=neg=zero=0; worst=None; negex=[]
    for _ in range(trials):
        restu=[rnd(3,rng) for _ in range(rng.randint(0,5))]
        B=LEAF if B_is_leaf else (rnd(3,rng) or (LEAF,))
        extra=[rnd(2,rng) for _ in range(rng.randint(0,3))]
        # v is a leaf (dv=1).  BEFORE u has children [v=leaf, B]+restu; du = len+... 
        # NOTE: as a subtree u has udeg=childcount+1; but the *graph degree* of u = childcount
        #  +1(parent). For 'du>dv' with dv=1(leaf graph degree=1) we need graph-deg(u)=
        #  childcount(u)+1 >= 2 always true.  BEFORE childcount(u)=2+|restu|.
        u_b=tuple([LEAF, B]+restu)
        u_a=tuple([tuple([B])]+restu)   # v extended into node([B])
        tb=tuple([u_b]+extra); ta=tuple([u_a]+extra)
        # graph degrees for the equalizing precondition (root not a leaf here; u is a child of root)
        du_graph = len(u_b)+1  # +parent
        dv_graph = 1           # v is a leaf
        if require_du_gt_dv and not (du_graph>dv_graph): continue
        m=Aobj_node(ta)-Aobj_node(tb)
        if m>0:pos+=1
        elif m<0:
            neg+=1
            if worst is None or m<worst: worst=m
            if len(negex)<3: negex.append((tb,ta,m))
        else:zero+=1
    print(f"[B_is_leaf={B_is_leaf}] leaf->leaf path-extend: pos={pos} neg={neg} zero={zero} worst={worst}")
    if negex:
        for tb,ta,m in negex: print("   NEG before=",tb," after=",ta," margin=",m)

if __name__=="__main__":
    run(B_is_leaf=True)
    run(B_is_leaf=False)

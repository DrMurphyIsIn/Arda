"""B = a SINGLE LEAF moved from u to v, du>dv, v ARBITRARY.  Is it unconditionally positive?
This is the pure 'relocate one pendant leaf from a higher-degree vertex to a lower-degree one'."""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, LEAF

def rnd(depth,rng):
    if depth<=0 or rng.random()<0.4: return LEAF
    return tuple(rnd(depth-1,rng) for _ in range(rng.randint(1,3)))

def run(trials=60000, seed=2):
    rng=random.Random(seed)
    by_gap={}; worst=None; negex=[]
    for _ in range(trials):
        B=LEAF
        restv=[rnd(2,rng) for _ in range(rng.randint(0,5))]
        restu=[rnd(2,rng) for _ in range(rng.randint(0,5))]
        extra=[rnd(2,rng) for _ in range(rng.randint(0,3))]
        v_b=tuple(restv)
        u_b=tuple([v_b, B]+restu)
        v_a=tuple(restv+[B])
        u_a=tuple([v_a]+restu)
        du=len(u_b)+1; dv=len(v_b)+1
        if not (du>dv): continue
        m=Aobj_node(tuple([u_b]+extra))-0
        tb=tuple([u_b]+extra); ta=tuple([u_a]+extra)
        m=Aobj_node(ta)-Aobj_node(tb)
        gap=du-dv
        b=by_gap.setdefault(gap,[0,0,0])
        if m>0:b[0]+=1
        elif m<0:
            b[1]+=1
            if worst is None or m<worst: worst=m
            if len(negex)<3: negex.append((du,dv,tb,ta,m))
        else:b[2]+=1
    print("B=single leaf, du>dv, [pos,neg,zero] by (du-dv) gap:")
    for k in sorted(by_gap): print(f"   gap={k}: {by_gap[k]}")
    print("  worst_neg=",worst)
    for du,dv,tb,ta,m in negex: print(f"   NEG du={du} dv={dv} margin={m}")
if __name__=="__main__":
    run()

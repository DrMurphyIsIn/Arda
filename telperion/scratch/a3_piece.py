"""Is 'move a PIECE B (leaf/cherry/arm) from u to v with du>dv' unconditionally Aobj-positive,
for ANY v (not just dv=1)?  Test B in {leaf, cherry, arm(2), arm(3)} and v arbitrary."""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, LEAF, isPiece

def rnd(depth,rng):
    if depth<=0 or rng.random()<0.4: return LEAF
    return tuple(rnd(depth-1,rng) for _ in range(rng.randint(1,3)))

def cherry(): return (LEAF,)
def arm(j): return tuple(cherry() for _ in range(j))

def run(trials=40000, seed=9):
    rng=random.Random(seed)
    buckets={}  # ('dv==1' or 'dv>1') -> [pos,neg,zero]
    worst={}
    for _ in range(trials):
        B=rng.choice([LEAF, cherry(), arm(2), arm(3), (cherry(),cherry())])
        assert isPiece(B)
        # v has some children (rest_v); B moves from u to v. du>dv required.
        restv=[rnd(2,rng) for _ in range(rng.randint(0,4))]
        restu=[rnd(2,rng) for _ in range(rng.randint(0,4))]
        extra=[rnd(2,rng) for _ in range(rng.randint(0,3))]
        v_b=tuple(restv)
        # BEFORE: u=node([v_b, B]+restu); AFTER: u=node([v_a]+restu), v_a=node(restv+[B])
        u_b=tuple([v_b, B]+restu)
        v_a=tuple(restv+[B])
        u_a=tuple([v_a]+restu)
        du_graph=len(u_b)+1
        dv_graph=len(v_b)+1
        if not (du_graph>dv_graph): continue
        tb=tuple([u_b]+extra); ta=tuple([u_a]+extra)
        m=Aobj_node(ta)-Aobj_node(tb)
        key='dv=1' if dv_graph==1 else 'dv>1'
        b=buckets.setdefault(key,[0,0,0])
        if m>0:b[0]+=1
        elif m<0:
            b[1]+=1
            if key not in worst or m<worst[key]: worst[key]=m
        else:b[2]+=1
    print("move a PIECE B, du>dv, [pos,neg,zero]:")
    for k in sorted(buckets):
        print(f"   {k}: {buckets[k]}   worst_neg={worst.get(k)}")

if __name__=="__main__":
    run()

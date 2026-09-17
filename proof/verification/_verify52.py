import os, sys
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join("..","..","telperion","scratch"))
# NOTE: a3_derisk.unrooted_Aobj is EXPONENTIAL (2^edges matching enumeration) and HANGS on n=52.
# Do NOT call it here.  Aobj_node (polynomial cavity) is root-invariant on these trees; we verify
# root-invariance cheaply via all_rerootings + Aobj_node instead.
from a3_derisk import Aobj_node, all_rerootings
LEAF=()
def cherry(): return (LEAF,)
def armL(L): return tuple(cherry() for _ in range(L))
def hub(a,b,c): return tuple([armL(5)]*a+[armL(4)]*b+[cherry()]*c)
def pant4(t):  # T(t,t,t,t): 4 core vertices each with t length-2 pendants
    def sub(i): 
        ch=[cherry() for _ in range(t)]
        return tuple(ch) if i==3 else tuple(ch+[sub(i+1)])
    return sub(0)
def sz(x): return 1+sum(sz(c) for c in x)
T=pant4(6); n=sz(T)
aT=Aobj_node(T)
# root-invariance sanity (polynomial): Aobj_node is identical across ALL rerootings of T.
reroots=list(all_rerootings(T))
rerooted_vals={Aobj_node(r) for r in reroots}
root_invariant = (rerooted_vals == {aT})
print(f"T(6,6,6,6): size={n}")
print(f"  Aobj_node        = {aT}  = {float(aT):.6f}")
print(f"  root-invariant across {len(reroots)} rerootings: {root_invariant}  ({len(rerooted_vals)} distinct value)")
# exact tieArgmax(52): max over single Balanced+Capped hubs of size 52
best=None; arg=None
for a in range(0,6):
    for b in range(0,7):
        if a+b<5: continue
        for c in range(0,6):
            if 1+11*a+9*b+2*c==n:
                v=Aobj_node(hub(a,b,c))
                if best is None or v>best: best=v; arg=(a,b,c)
print(f"  tieArgmax({n})    = {best}  = {float(best):.6f}  at (a,b,c)={arg}")
print(f"  EXACT: Aobj(T) - tie = {aT-best}  = {float(aT-best):.6f}")
print(f"  => T(6,6,6,6) {'STRICTLY EXCEEDS' if aT>best else 'does NOT exceed'} the tie -- conjecture1 {'FALSE at n=52' if aT>best else 'holds here'}")

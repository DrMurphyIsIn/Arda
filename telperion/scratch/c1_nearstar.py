"""
C1 supplement: reconcile against Lean nearStarTie (R47HdomBridge / R47NearStarValue).

Lean structures (R47HubState.lean):
  cherryU   = node[node[]]            (a cherry, 2 verts)
  armU j    = node(replicate j cherryU)   (an arm-hub carrying j cherries)
  backboneU [(arms, c)] = node( arms.map armU ++ replicate c cherryU )   (single hub)
  nearStarTie K = backboneU [(replicate K 5, 0)]
              = node(replicate K (armU 5))   -- K arms, EACH arm = a 5-cherry sub-hub
  usize = 1 + 11K ;  Aobj = (26/23)*(621/64)^K = (26/23)/rhoB * rhoB^(1+11K).

Compare against Aobj (root-invariant per(L)/prod(deg) = a3_derisk.Aobj_node/unrooted_Aobj).
"""
from fractions import Fraction as Fr
from a3_derisk import Aobj_node, unrooted_Aobj, Ztot_sub, LEAF
import math
RHOB = (621/64)**(1/11)
CHERRY = (LEAF,)                       # cherryU = node[leaf]
def armU(j): return tuple([CHERRY]*j)  # armU j = node(replicate j cherryU)
def nearStarTie(K): return tuple([armU(5)]*K)   # node(replicate K (armU 5))
def vsize(t): return 1+sum(vsize(c) for c in t)

print("=== EXACT Lean nearStarTie K = node(replicate K (armU 5)):  Aobj = (26/23)(621/64)^K ? ===")
for K in range(1,7):
    t = nearStarTie(K); n = vsize(t)
    A = Aobj_node(t)                       # root-invariant objective (per(L)/prod deg)
    pred = Fr(26,23)*Fr(621,64)**K
    r = float(A)**(1/n)
    amp = float(A)/(RHOB**n)               # Aobj / rhoB^n  -> should be (26/23)/rhoB
    print(f" K={K} n={n:3d}  Aobj={str(A):>22}  pred={str(pred):>22}  match={A==pred}  Aobj^(1/n)={r:.10f}  amp=Aobj/rhoB^n={amp:.10f}")
print(f"  target: rate rhoB={RHOB:.10f}  amplitude (26/23)/rhoB={(26/23)/RHOB:.10f}")

print("\n=== Does the near-star per-vertex RATE -> rhoB EXACTLY as K->inf? ===")
for K in [1,2,5,10,50,200]:
    t=nearStarTie(K); n=vsize(t)
    A=Aobj_node(t); r=float(A)**(1/n)
    print(f" K={K:4d} n={n:5d}  Aobj^(1/n)={r:.12f}  (rhoB={RHOB:.12f}, diff={r-RHOB:+.2e})")

print("\n=== FAMILY QUESTION: near-star (load-5 arms) vs uniform cherry-caterpillar vs single 5-cherry hub ===")
# uniform cherry-caterpillar: spine of m verts, 1 cherry each (classical Pant family)
def caterpillar(m,a=1):
    node=None
    for i in reversed(range(m)):
        arms=tuple([CHERRY]*a)
        node=arms if node is None else arms+(node,)
    return node
# single 5-cherry hub (my earlier 'a=5'): node(replicate 5 cherry) == armU(5)!
single5 = armU(5)
print(f" single 5-cherry hub (=armU 5): n={vsize(single5)} Aobj={Aobj_node(single5)}={float(Aobj_node(single5)):.6f} Aobj^(1/n)={float(Aobj_node(single5))**(1/vsize(single5)):.10f}")
print(f"   Ztot_sub(armU 5)={Ztot_sub(single5)} (=621/64? {Ztot_sub(single5)==Fr(621,64)})  -- note: this is Ztot_sub NOT Aobj")
print(" uniform cherry-caterpillar Aobj^(1/n) (a=1) as m grows -> sqrt(3/2)=%.10f:" % math.sqrt(1.5))
for m in [5,10,20,40]:
    t=caterpillar(m,1); n=vsize(t); print(f"   m={m:2d} n={n:3d} Aobj^(1/n)={float(Aobj_node(t))**(1/n):.10f}")
print(" near-star (load-5 arms) Aobj^(1/n) -> rhoB=%.10f (ABOVE caterpillar's sqrt(3/2))" % RHOB)
for K in [5,10,20,40]:
    t=nearStarTie(K); n=vsize(t); print(f"   K={K:2d} n={n:3d} Aobj^(1/n)={float(Aobj_node(t))**(1/n):.10f}")

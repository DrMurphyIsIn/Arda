"""
C1 part 2: exact arm-count optimum, leaf-vs-cherry, non-uniform search, and the
single-hub closed form Ztot_sub(hub with a cherries) and its per-vertex rate.
"""
from fractions import Fraction as Fr
from a3_derisk import Ztot_sub, Zopen_sub, unrooted_Aobj, Aobj_node, LEAF

RHOB = (621/64)**(1/11)
CHERRY = (LEAF,)
def vsize(t): return 1 + sum(vsize(c) for c in t)

print("=== SINGLE-HUB (m=1) with a CHERRY arms: exact Ztot_sub closed form ===")
# hub degree = a (a children, each a cherry). udeg(hub)=a+1.
# cherry child: udeg=2, Ztot_sub(cherry)=? cherry=node[leaf]: Popen=Ztot(leaf)=1, Matched=w*Zo*1, w=1/(2*1).
#   Actually cherry realized as child of hub at edge weight 1/((a+1)*2). But Ztot_sub(cherry) is intrinsic:
#   cherry=node[leaf], udeg=2: Popen=1 (leaf Ztot=1), Matched=1/(2*1)*1*1=1/2 -> Ztot_sub=3/2, Zopen=1.
# hub with a cherries at degree a+1: Popen=(3/2)^a, Matched via Matched_factor:
#   qContrib per cherry = Zopen(cherry)/Ztot(cherry)/udeg(cherry) = 1/(3/2)/2 = 1/3
#   Ztot_hub = (3/2)^a * (1 + (1/(a+1))*(a*(1/3))) = (3/2)^a * (1 + a/(3(a+1)))
def Zhub_cherry(a):
    return Fr(3,2)**a * (1 + Fr(a, 3*(a+1)))
for a in range(1, 12):
    hub = tuple([CHERRY]*a)
    n = vsize(hub)  # = 1 + 2a
    exact = Ztot_sub(hub)
    pred = Zhub_cherry(a)
    zr = float(exact)**(1/n)
    star = ' <-- rhoB' if abs(zr-RHOB)<1e-12 else ''
    print(f" a={a:2d} n={n:2d} Ztot_sub={str(exact):>12} pred={str(pred):>12} match={exact==pred}  ^(1/n)={zr:.12f}{star}")

print("\n=== arm-count optimum: maximize f(a)=Ztot_sub^(1/(2a+1)) over a, single cherry-hub ===")
best=None
for a in range(1,30):
    z=Zhub_cherry(a); n=1+2*a; r=float(z)**(1/n)
    if best is None or r>best[0]: best=(r,a,n,z)
print(f"  optimum a*={best[1]} n={best[2]} rate={best[0]:.12f} Ztot_sub={best[3]}  (=621/64 at a=5? {best[3]==Fr(621,64)})")
# closed form: maximize log((3/2)^a*(1+a/(3(a+1))))/(2a+1). Report neighbors.
print("  neighbors:", [(a, round(float(Zhub_cherry(a))**(1/(2*a+1)),12)) for a in range(3,9)])

print("\n=== LEAF arms vs CHERRY arms (single hub, same arm count a) ===")
for a in range(2,9):
    hub_c = tuple([CHERRY]*a); hub_l = tuple([LEAF]*a)
    nc,nl = vsize(hub_c), vsize(hub_l)
    zc = float(Ztot_sub(hub_c))**(1/nc); zl = float(Ztot_sub(hub_l))**(1/nl)
    print(f" a={a}: cherry n={nc} rate={zc:.10f}  |  leaf n={nl} rate={zl:.10f}  cherry_wins={zc>zl}")

print("\n=== NON-UNIFORM single-spine (m=2): does splitting arms across 2 hubs beat m=1,a=5? ===")
# spine of 2 vertices, arm_counts [a0,a1], cherries. Compare best to rhoB.
def spider2(a0,a1):
    tail = tuple([CHERRY]*a1)
    return tuple([CHERRY]*a0) + (tail,)
best2=None
for a0 in range(0,10):
    for a1 in range(0,10):
        t=spider2(a0,a1); n=vsize(t)
        if n>34: continue
        r=float(Ztot_sub(t))**(1/n)
        if best2 is None or r>best2[0]: best2=(r,a0,a1,n)
print(f"  best m=2 non-uniform: a0={best2[1]} a1={best2[2]} n={best2[3]} rate={best2[0]:.12f}  vs rhoB={RHOB:.12f}  beats_rhoB={best2[0]>RHOB}")

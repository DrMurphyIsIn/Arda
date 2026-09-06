"""
Front C1: exact parametric cherry-spider Aobj engine + extremal search + rhoB reconciliation.

Conventions (mirror Lean R47Tree / a3_derisk EXACTLY):
  UTree = nested tuple; LEAF = ().  udeg(K)=len(K)+1.
  Ztot_sub(K)/Zopen_sub(K): phantom-rooted subtree partition fn at degree udeg(K), edge wt 1/(udeg*udeg).
  Aobj_node(cs): root-realized at degree len(cs) (no parent edge) = per(L)/prod(deg) root-invariant.
  rhoB = (621/64)^(1/11) ~ 1.2294736877697814  [Lean R3Cert.rhoB, ExactCruxes.lean].
  Lean rate: Ztot_sub(t) <= rhoB^usize(t).  Aobj(t) <= ((d+1)/d)*rhoB^usize(t) (SharpRateNF).
  The DEFINING extremal for rhoB: degree-6 near-broom, n=11: hub with 5 cherry arms,
    Ztot_sub = (3/2)^5*(23/18) = 621/64 EXACTLY -> Ztot_sub^(1/11) = rhoB EXACTLY.
"""
from fractions import Fraction as Fr
from a3_derisk import Ztot_sub, Zopen_sub, unrooted_Aobj, Aobj_node, udeg, LEAF

RHOB = (621/64)**(1/11)  # 1.2294736877697814

def vsize(t): return 1 + sum(vsize(c) for c in t)

CHERRY = (LEAF,)                       # length-2 arm: node[leaf], 2 vertices
def leaf_arm(): return LEAF            # length-1 arm: leaf, 1 vertex

def spider(arm_counts, arm_type='cherry'):
    """Cherry-spider: spine of m vertices (a PATH), spine vertex i carries arm_counts[i] arms.
       arm_type 'cherry' -> each arm = node[leaf]; 'leaf' -> each arm = leaf.
       Built as nested tuples: spine is a caterpillar path; we root at spine-end.
       spine vertex structure: node( arms... , next_spine_vertex ).  Last spine vertex: node(arms...)."""
    arm = CHERRY if arm_type == 'cherry' else LEAF
    m = len(arm_counts)
    # build from the tail end inward
    node = None
    for i in reversed(range(m)):
        arms = tuple([arm] * arm_counts[i])
        if node is None:
            node = arms                     # last spine vertex: just its arms
        else:
            node = arms + (node,)           # this spine vertex: arms + link to next
    return node

def uniform_spider(m, a, arm_type='cherry'):
    return spider([a]*m, arm_type)

def rates(t):
    """Return (n, Aobj, Aobj^(1/n), Ztot_sub, Ztot_sub^(1/n)) as (int, Fr, float, Fr, float)."""
    n = vsize(t)
    A = Aobj_node(t)                 # root-realized; but for a NON-root whole tree use unrooted
    Au = unrooted_Aobj(t)            # root-invariant per(L)/prod(deg)
    Z = Ztot_sub(t)
    return n, Au, float(Au)**(1/n), Z, float(Z)**(1/n)

if __name__ == "__main__":
    # sanity: the defining near-broom
    broom5 = tuple([CHERRY]*5)
    n,Au,ar,Z,zr = rates(broom5)
    print(f"near-broom(5 cherries): n={n} Ztot_sub={Z}={float(Z):.6f} Ztot_sub^(1/n)={zr:.12f}  rhoB={RHOB:.12f}  match={abs(zr-RHOB)<1e-12}")
    print(f"  Aobj(unrooted)={Au}={float(Au):.6f}  Aobj^(1/n)={ar:.6f}")
    print()
    print("=== UNIFORM cherry-spiders: sweep (m spine, a arms/vertex), arm=cherry ===")
    print(f"{'m':>3}{'a':>3}{'n':>5}  {'Ztot_sub^(1/n)':>16}  {'Aobj^(1/n)':>14}  {'Ztot_sub':>14}")
    best = None
    for m in range(1, 12):
        for a in range(0, 10):
            n = m*(1 + 2*a) if False else None  # cherry adds 2 verts/arm
            t = uniform_spider(m, a, 'cherry')
            n = vsize(t)
            if n > 34: continue
            _,Au,ar,Z,zr = rates(t)
            if best is None or zr > best[0]:
                best = (zr, m, a, n, Z, ar)
            if a in (5,6,7,8) or m<=3:
                print(f"{m:>3}{a:>3}{n:>5}  {zr:>16.12f}  {ar:>14.8f}  {str(Z):>14}")
    print(f"\nBEST uniform (max Ztot_sub^(1/n)): m={best[1]} a={best[2]} n={best[3]} Ztot_sub^(1/n)={best[0]:.12f} (rhoB={RHOB:.12f})")

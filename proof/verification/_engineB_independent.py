"""INDEPENDENT Engine B verification (per(L)/prod(deg) monomer-dimer).

Recomputes Aobj(T(6,6,6,6)) and tieArgmax(52) from the repo's OWN structure
definitions, via two independent permanent/matching engines, and confirms
root-invariance of the rooted-Lean Aobj (a3_derisk.Aobj_node).

Engines:
  B1  perL_tree  (reused from exhaustive_maximizer_check) -> per(L)/prod(deg)
  B2  a fresh, INDEPENDENT rooted tree-DP over matchings that computes
      per(L) = sum_matchings prod_{uncovered v} deg(v)  in LINEAR time.
      (Written from scratch, different recurrence bookkeeping than B1.)
Baseline: a3_derisk.Aobj_node (rooted cavity engine).
"""
import os, sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "telperion", "scratch"))
sys.path.insert(0, HERE)

from a3_derisk import Aobj_node, all_rerootings  # baseline rooted engine
from exhaustive_maximizer_check import perL_tree   # engine B1

LEAF = ()

# ------- structure builders (mirror _verify52.py exactly) -------
def cherry():      return (LEAF,)
def armL(L):       return tuple(cherry() for _ in range(L))
def hub(a, b, c):  return tuple([armL(5)] * a + [armL(4)] * b + [cherry()] * c)
def pant4(t):
    def sub(i):
        ch = [cherry() for _ in range(t)]
        return tuple(ch) if i == 3 else tuple(ch + [sub(i + 1)])
    return sub(0)
def sz(x): return 1 + sum(sz(c) for c in x)

# ------- nested-tuple tree -> (n, edges) adjacency -------
def to_edges(t):
    edges = []; nid = [0]
    def rec(node):
        me = nid[0]; nid[0] += 1
        for c in node:
            ch = rec(c); edges.append((me, ch))
        return me
    rec(t)
    return nid[0], edges

# ================= ENGINE B2: independent rooted matching tree-DP =================
# per(L) for a tree = sum over matchings M of prod_{v not covered by M} deg(v).
# Independent DP: root the (arbitrary) tree at node 0. For each vertex u define
#   A[u] = sum over matchings of subtree(u) where u is NOT matched to a child,
#          weighted by prod of deg over uncovered vertices IN subtree(u), and
#          treating u itself as *available* (its deg factor NOT yet applied here
#          -- we apply it only if u ends up uncovered at the parent level).
# We track two quantities per subtree, folding children one at a time:
#   f[u] = total weight of subtree(u) with u COVERED (matched to some child)
#   g[u] = total weight of subtree(u) with u UNCOVERED (available to match parent),
#          NOT yet multiplying deg(u) (parent decides).
# Fold child c into (g,f) where child already reduced to (gc, fc):
#   child contributes, if not matched to u:  (gc*deg(c) + fc)   [c uncovered->deg(c), or covered]
#   child contributes, if matched to u:       gc                [edge u-c, c was available]
# Standard monomer-dimer tree DP. deg here is the FULL (unrooted) degree.
def perL_B2(edges, n):
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    deg = [len(adj[v]) for v in range(n)]
    # iterative post-order from root 0
    par = [-1] * n; order = []; seen = [False] * n; st = [0]; seen[0] = True
    while st:
        u = st.pop(); order.append(u)
        for w in adj[u]:
            if not seen[w]:
                seen[w] = True; par[w] = u; st.append(w)
    g = [Fr(0)] * n  # u uncovered, deg(u) NOT applied
    f = [Fr(0)] * n  # u covered
    for u in reversed(order):
        gu = Fr(1)  # empty subtree of u: u uncovered, weight 1
        fu = Fr(0)  # cannot be covered with no children yet
        for c in adj[u]:
            if c == par[u]:
                continue
            child_free = g[c] * deg[c] + f[c]   # c not matched to u
            match_uc   = g[c]                   # edge (u,c), c must have been available
            # new state: fold child c
            new_g = gu * child_free                       # u still uncovered
            new_f = fu * child_free + gu * match_uc       # u covered: either already, or now via c
            gu, fu = new_g, new_f
        g[u] = gu; f[u] = fu
    # root: u=0 uncovered contributes deg(0); covered as-is
    return g[0] * deg[0] + f[0], deg

def prod_vals(vals):
    p = Fr(1)
    for d in vals:
        p *= d
    return p

def aobj_B1(t):
    n, edges = to_edges(t)
    per, deg = perL_tree(edges, n)  # deg is a dict {v: degree}
    return per / prod_vals(deg.values())

def aobj_B2(t):
    n, edges = to_edges(t)
    per, deg = perL_B2(edges, n)    # deg is a list
    return per / prod_vals(deg)

# ================= root-invariance via polynomial DP (NO exponential) =================
def rooted_baseline_all(t, cap=None):
    """Aobj_node over ALL rerootings (polynomial each) -> set of values."""
    reroots = all_rerootings(t)
    if cap is not None:
        reroots = reroots[:cap]
    return set(Aobj_node(rt) for rt in reroots)


def main():
    # ---------- correctness cross-check of B2 vs B1 on small trees ----------
    small = [(LEAF, LEAF), ((LEAF,), (LEAF,)),
             ((LEAF, LEAF), (LEAF, LEAF), (LEAF,)),
             (((LEAF,), (LEAF,)), (LEAF, LEAF), (LEAF,)),
             hub(1, 1, 1), pant4(2)]
    for t in small:
        assert aobj_B1(t) == aobj_B2(t), ("B1!=B2", t)
        assert aobj_B1(t) == Aobj_node(t), ("B1!=baseline", t)
    print("[B2 selfcheck] B1==B2==baseline on 6 small trees. OK")

    # ---------- T(6,6,6,6) ----------
    T = pant4(6); n = sz(T)
    aT_b1 = aobj_B1(T)
    aT_b2 = aobj_B2(T)
    aT_base = Aobj_node(T)
    # root-invariance: baseline over ALL 52 rerootings
    rv = rooted_baseline_all(T)
    print(f"T(6,6,6,6): n={n}")
    print(f"  B1 per(L)/prod(deg)   = {aT_b1}")
    print(f"  B2 per(L)/prod(deg)   = {aT_b2}")
    print(f"  baseline Aobj_node    = {aT_base}")
    print(f"  B1==B2                = {aT_b1==aT_b2}")
    print(f"  B1==baseline          = {aT_b1==aT_base}")
    print(f"  root-invariant (all {len(all_rerootings(T))} rerootings, #distinct={len(rv)}) = {len(rv)==1}")
    print(f"  rerooted value == unrooted = {len(rv)==1 and next(iter(rv))==aT_b1}")

    # ---------- tieArgmax(52) ----------
    best = None; arg = None; alt = None
    for a in range(0, 6):
        for b in range(0, 7):
            if a + b < 5: continue
            for c in range(0, 6):
                if 1 + 11*a + 9*b + 2*c == n:
                    H = hub(a, b, c)
                    v1 = aobj_B1(H); v2 = aobj_B2(H); vb = Aobj_node(H)
                    assert v1 == v2 == vb, ("hub engine mismatch", (a,b,c), v1, v2, vb)
                    # root-invariance for the hub too
                    rvh = set(Aobj_node(rt) for rt in all_rerootings(H))
                    assert len(rvh) == 1 and next(iter(rvh)) == v1, ("hub not root-inv", (a,b,c))
                    if best is None or v1 > best:
                        best = v1; arg = (a, b, c)
    print(f"  tieArgmax({n}) = {best}  at (a,b,c)={arg}")

    diff = aT_b1 - best
    print(f"  Aobj(T) - tie = {diff}")
    print(f"  sign: {'T>tie' if diff>0 else ('T<tie' if diff<0 else 'T=tie')}")

    # ---------- compare to stated baseline rationals ----------
    base_aT  = Fr(1180837892027061, 26306674688)
    base_tie = Fr(4695479375868117, 104857600000)
    base_diff = Fr(8862581903961897, 82208358400000)
    print("  baseline-match Aobj:", aT_b1 == base_aT)
    print("  baseline-match tie :", best == base_tie)
    print("  baseline-match diff:", diff == base_diff)

if __name__ == "__main__":
    main()

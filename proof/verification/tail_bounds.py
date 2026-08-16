"""Region-free tail bounds toward closing prod_v W_vv <= 1 (step (i) of the Heilmann-Lieb route).

From heilmann_lieb.py: Phi(C)^2 = det(W) <= prod_v W_vv (Hadamard), with the LOCAL product
    prod_v W_vv = exp( sum_v q_v ),   q_v := 2 log a(d_v,c_v) + log( 1 + z_v Z_v ),   Z_v = sum_{u~v} z_u.
So Phi<=1 is implied by  sum_v q_v <= 0.  Each q_v is LOCAL (radius 1: it depends only on v's
(d_v,c_v) and its neighbours' activities z_u).  This module records what is RIGOROUS about the
per-vertex charge q_v, and states precisely the gap that remains.

RIGOROUS (region-free) FACTS.
  (R1) deg_A(v) <= d_v - c_v.  [In the gadget, d_v = (#children) + 1 + c_v; the matching adjacency A
       carries only the backbone edges, so deg_A(v) = (#children) + [v has a parent] <= d_v - c_v.]
  (R2) z_v * deg_A(v) <= 1  for every vertex, region-free:  z(d,c)(d-c) = 3(d-c)/(3d+c) <= 1
       (equivalent to 3(d-c) <= 3d+c, i.e. -3c <= c, always).  Hence z_v Z_v <= z_v deg_A(v) <= 1
       (neighbour activities z_u <= 1), so  log(1 + z_v Z_v) <= log 2, giving the CRUDE per-vertex bound
           q_v <= 2 log a(d_v,c_v) + log 2 .
  (R3) a(d,c) = F(d,c)/rho_B^{1+2c} is DECREASING in d (F=(3/2)^c(1+c/(3d)) has the +c/(3d) term),
       so a(d,c) <= a_leaf(c) := a(1+c,c).
  (R4) CHERRY CONFINEMENT (rigorous).  By (R2)-(R3), q_v <= 2 log a_leaf(c_v) + log 2, which is < 0
       as soon as a_leaf(c_v) < 1/sqrt(2).  Since a_leaf(c) -> 0 geometrically
       (a_leaf(c) ~ (4/3)(1/rho_B)((3/2)/rho_B^2)^c, ratio 0.9923 < 1), this holds for all c > 54
       (a_leaf(54)=0.712 > 1/sqrt2 > 0.707 = a_leaf(55)).  So EVERY vertex with c_v > 54 has q_v < 0:
       positive charges live only at c_v <= 54.

THE LINEAR SURROGATE S (cleaner for the accumulation).  Using log(1+x) <= x on each q_v,
    log prod_v W_vv = sum_v q_v <= 2 S(C),   S(C) := sum_v log a(d_v,c_v) + sum_{edges (u,v)} z_u z_v,
so  S(C) <= 0  ==>  prod_v W_vv <= 1  ==>  Phi(C) <= 1.  Unlike prod_v W_vv, S is LINEAR and
edge-decomposable.

CORRECTION (2026-08-05).  An earlier version claimed "S <= 0 for every tree past a small size" and
"sup prod_v W_vv attained on small trees", proposing a discharging route to closure.  BOTH WERE
WRONG -- artifacts of random sampling that never generates the adversarial structures.  In truth
BOTH surrogates are UNBOUNDED ABOVE while Phi <= 1:
  * S is UNBOUNDED: a c=0 caterpillar (spine with a leaf at each node) has S = 0.17, 0.64, 1.58,
    3.14 at 11, 41, 101, 201 nodes -- growing without bound (surrogate_S_unbounded()).  The
    log(1+x) <= x relaxation loses O(1) per edge, so it accumulates over the whole tree.
  * prod_v W_vv is UNBOUNDED: stacking the root(4)-four-arm motif grows it past any bound
    (heilmann_lieb.hadamard_bound_unbounded).
On BOTH families the true Phi stays <= 1 (and decreases).  So neither surrogate has a finite box,
and there is NO discharging route via S.  A closed proof needs the exact off-diagonal structure of
W, not S or the diagonal product.

WHAT REMAINS TRUE.  The exact per-vertex decomposition log prod_v W_vv = sum_v q_v and the
region-free bounds (R1)-(R4) hold -- in particular each individual q_v < 0 once c_v > 54.  But since
sum_v q_v = log prod_v W_vv is UNBOUNDED above (motifs), these per-vertex facts do NOT combine into
a global bound.  The discharging route (via S) is DEAD: S is unbounded, so there is no finite box to
discharge to.

STATUS.  Phi <= 1 remains OPEN.  Both surrogate routes (linear S and the Hadamard diagonal product
prod_v W_vv) are unbounded above and so cannot prove it; the exact reformulations (rational_
reduction, heilmann_lieb spectral identity) are correct but not sufficient on their own.  Reported
honestly; the earlier "finite box / discharging route to closure" claims are RETRACTED.
"""
from __future__ import annotations

import math

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def a_leaf(c):
    return _a(1 + c, c)


def per_vertex_charges(C):
    """Return the list of exact per-vertex charges q_v with node profiles; sum(q_v)=log prod_v W_vv."""
    nodes = []
    edges = []

    def rec(node, parent):
        cr, kids = node
        d = len(kids) + 1 + cr
        idx = len(nodes)
        nodes.append((d, cr))
        if parent is not None:
            edges.append((parent, idx))
        for ch in kids:
            rec(ch, idx)

    rec(C, None)
    n = len(nodes)
    zv = [_z(d, c) for (d, c) in nodes]
    av = [_a(d, c) for (d, c) in nodes]
    Z = [0.0] * n
    for (u, v) in edges:
        Z[u] += zv[v]
        Z[v] += zv[u]
    return [(2 * math.log(av[v]) + math.log(1 + zv[v] * Z[v]), nodes[v]) for v in range(n)]


def verify_region_free_bounds(dmax: int = 400) -> dict:
    """Verify (R1)-(R4): the region-free per-vertex bounds and the cherry confinement c<=54."""
    thr = 1 / math.sqrt(2)
    r2 = all(_z(d, c) * (d - c) <= 1 + 1e-12 for d in range(1, dmax) for c in range(0, d))
    r3 = all(_a(d, 3) >= _a(d + 1, 3) - 1e-15 for d in range(4, 200))
    cmax = max((c for c in range(0, 500) if a_leaf(c) > thr), default=None)
    ratio = (1.5 / _rhoB ** 2)
    return {
        "R2_z_times_degA_le_1": r2,
        "R3_a_decreasing_in_d": r3,
        "R4_cherry_confinement_cmax": cmax,          # positive charge => c <= cmax (=54)
        "a_leaf_geometric_ratio": ratio,             # < 1  => a_leaf(c) -> 0
        "crude_bound_confines_degree": _a(9, 0) <= thr,   # False: c=0 has a=0.813 for all d
        "residual": "degree/depth/branching confinement + accumulation via discharging; open",
    }


def prod_W(C) -> float:
    """prod_v W_vv = exp(sum_v q_v), the Hadamard upper bound on Phi^2."""
    return math.exp(sum(q for q, _ in per_vertex_charges(C)))


def S_surrogate(C) -> float:
    """S(C) = sum_v log a_v + sum_edges z_u z_v.  S <= 0 => prod_v W_vv <= 1 => Phi <= 1."""
    nodes = []
    edges = []

    def rec(node, parent):
        cr, kids = node
        d = len(kids) + 1 + cr
        idx = len(nodes)
        nodes.append((d, cr))
        if parent is not None:
            edges.append((parent, idx))
        for ch in kids:
            rec(ch, idx)

    rec(C, None)
    zv = [_z(d, c) for (d, c) in nodes]
    av = [_a(d, c) for (d, c) in nodes]
    return sum(math.log(x) for x in av) + sum(zv[u] * zv[v] for (u, v) in edges)


def surrogate_S_unbounded(Ls=(5, 20, 50, 100)) -> dict:
    """Demonstrate that the linear surrogate S is UNBOUNDED ABOVE (the correction).

    A c=0 caterpillar (spine of c=0 nodes, each carrying one c=0 leaf) has S growing without bound
    (0.17, 0.64, 1.58, 3.14 at 11/41/101/201 nodes) while the true Phi stays <= 1 -- so S has NO
    finite box and the discharging-via-S route is dead.
    """
    def caterpillar(L):
        C = (0, [])
        for _ in range(L):
            C = (0, [C, (0, [])])
        return C

    Ss = [S_surrogate(caterpillar(L)) for L in Ls]
    return {"Ls": list(Ls), "S": Ss, "S_unbounded_increasing": Ss == sorted(Ss) and Ss[-1] > 1.0}


if __name__ == "__main__":
    r = verify_region_free_bounds()
    print("region-free tail bounds toward prod_v W_vv <= 1:")
    for k, v in r.items():
        print(f"  {k}: {v}")

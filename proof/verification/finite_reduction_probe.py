"""Probe: does logPhi ACCUMULATE at 0 over integer trees, or is it bounded away from 0 outside a
finite set?  This decides whether a FINITE-REDUCTION proof of the crux (depth/width/cherry bounds ->
finitely many residual trees -> exhaustive check) is alive or dead.

For each node-count N we compute, over ALL rooted trees with exactly N nodes (cherries<=cmax per node):
  * the maximum logPhi (must be <= 0), and how close to 0 it gets,
  * the "near-tie gap": max logPhi over trees NOT in the 6-tree near-star tie variety (c+k=5, N<=6).
If the near-tie gap stays bounded below 0 by a margin that does NOT shrink as N grows, finite-reduction
is viable (only finitely many trees are within any margin of 0).  If trees of growing N get arbitrarily
close to 0, the route is dead.

FINDINGS (2026-08-11, exhaustive over ALL rooted trees, N<=6 nodes, cherries<=6 per node).
  * The 6 tie trees (near-star family N(c,k), c+k=5, logPhi=0 EXACTLY) have node counts 1,3,5,7,9,11.
  * Over NON-tie trees the maximum logPhi is attained at the c+k=4 near-star N(2,2) (and its relatives)
    with logPhi = gVal(4) = -0.00102642, and it MOVES AWAY from 0 as N grows (N=5: -0.00103,
    N=6: -0.01452 -- no tie tree at N=6).  ZERO non-tie trees fall within 1e-3 of 0.
  * So over INTEGER trees the evidence is a UNIFORM MARGIN: sup{logPhi : non-tie} = gVal(4) ~ -0.001.
    This does NOT contradict "the continuous relaxation exceeds 0" (Phi(c*=3.82)=1.00004>1): the
    continuous interpolant crosses 0 between the integers c=3,4, but every ACTUAL integer tree stays
    <= gVal(4)<0.  The margin is an INTEGRALITY phenomenon -- exactly why a proof must be arithmetic.

CONSEQUENCE -- the finite-reduction proof SKELETON is revived (arithmetic-compatible):
  (D) depth bound: a tree with a chain longer than D has logPhi <= gVal(4) (E2 linear decay, PROVEN
      mechanism: per-node depth increment -> -L+log((1+sqrt2)/2)<0).
  (W) width bound: a node with more than W children has logPhi <= gVal(4) (branching bounded-neg).
  (C) cherry bound: a node with more than C cherries has logPhi <= gVal(4) (region-free, peak at 5).
  Then only FINITELY many tree shapes remain -> exhaustive rational check (each <= 0, tie at the 6).
This is NOT a proof: (D),(W),(C) with the explicit uniform constant gVal(4) are UNPROVEN (they are the
"quantitative far-regime margins" the tail_decomposition flags open), and N=7+ is not yet exhaustively
confirmed.  But it reframes the open crux from "find a (nonexistent) smooth potential" to "prove three
one-sided integer margin bounds + a finite check" -- a concrete, non-circular arithmetic target.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import general_children_crux as GC


def _trees_exact_N(N: int, cmax: int):
    """All rooted trees with EXACTLY N nodes, cherries<=cmax per node (canonical, from GC._trees is
    cumulative; re-filter by node count)."""
    def nodes(C):
        return 1 + sum(nodes(ch) for ch in C[1])
    for C in GC._trees(N, cmax):
        if nodes(C) == N:
            yield C


def probe(nmax: int = 8, cmax: int = 7) -> dict:
    rows = []
    global_near_tie_gap = -9.0     # max logPhi over NON-tie trees
    tie_trees = set()
    for N in range(1, nmax + 1):
        best = -9.0
        best_nontie = -9.0
        best_nontie_C = None
        n_within_1e3 = 0
        cnt = 0
        for C in _trees_exact_N(N, cmax):
            cnt += 1
            lp = GC.log_phi(C)
            best = max(best, lp)
            is_tie = abs(lp) < 1e-6
            if is_tie:
                tie_trees.add(str(C))
            else:
                if lp > best_nontie:
                    best_nontie, best_nontie_C = lp, C
            if not is_tie and lp > -1e-3:
                n_within_1e3 += 1
        global_near_tie_gap = max(global_near_tie_gap, best_nontie)
        rows.append({
            "N": N, "trees": cnt,
            "max_logPhi": round(best, 8),
            "max_logPhi_nontie": round(best_nontie, 8),
            "nontie_within_1e-3_of_0": n_within_1e3,
            "argmax_nontie": best_nontie_C,
        })
    return {
        "by_node_count": rows,
        "n_tie_trees_total": len(tie_trees),
        "global_max_nontie_logPhi": round(global_near_tie_gap, 8),
        # If this MARGIN is bounded away from 0 AND the count of near-0 non-tie trees does not grow
        # with N, finite-reduction is viable.
        "nontie_margin_below_0": round(-global_near_tie_gap, 8),
    }


if __name__ == "__main__":
    import json, sys
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    cmax = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    print(json.dumps(probe(nmax, cmax), indent=2, default=str))

"""Bounded-block Fischer as a route to Phi<=1: what it actually delivers, and why it does NOT close

(Contributed by a parallel session on branch experiment/lr-fischer-decay, 2026-08-07;
verified and consolidated onto main.)
the general (arbitrary-children) crux.  A focused adversarial re-examination of the interlacing.py
lead ("the first bound that survives adversarials"), 2026-08-07.

interlacing.py proposed: for a per-tree partition into CONNECTED blocks of BOUNDED size B0,
    Phi(C)^2 = det(W) <= prod_B det(W[B, B])                                        (Fischer)
and reported that best-of-{3,5,7,9} keeps the product <= 1 on every tree tested (max 0.998), with
two rigor gaps left open: (a) a UNIVERSAL bounded block size suffices, (b) a boundary-aware finite
block-type check.  This module re-runs that lead against the adversaries interlacing.py did NOT test
-- the LARGER near-star ties -- and finds the lead is materially weaker than reported.

FINDING 1 (exact, robust) -- the reported empirical claim is FALSE on the biggest tie.
The 6 exact ties are the near-star gadgets N(c,5-c), ARM=(0,[(0,[])]), with node counts 1,3,5,7,9,11.
interlacing.py's adversaries used only the 3-node tie N(4,1); it never tested the 11-node tie N(0,5).
On N(0,5):  best-of-{3,5,7,9} block-Fischer = 1.03161 > 1  (phi^2 = 1 exactly).
A bounded block cannot equal phi^2=1 unless it CONTAINS THE WHOLE tie gadget, so B0 must be >= 11 to
certify even the isolated tie N(0,5).  best-of-{3,5,7,9} is insufficient.

FINDING 2 (concrete witnesses) -- no SMALL fixed B0 works; the needed block spans a constant fraction
of the tree.  There are valid NON-tie trees (phi^2 well below 1) on which block-Fischer stays > 1 until
the block size is a large fraction of n.  Witness WITNESS_36 below (36 nodes, phi^2 = 0.7893):
    greedy block-Fischer stays > 1 up to B0 = 23  (B0=17 gives 1.0976);  first B0 with product <= 1
    is B0 = 24.  So a block must cover ~2/3 of a 36-node tree whose amplitude is only 0.79.  Small
    fixed blocks fail.

FINDING 3 (structural) -- per-block det > 1 is normal, and a captured tie LEAKS above 1 at its
boundary.  Individual greedy blocks routinely have det(W[B]) > 1 (up to ~1.15); it is the PRODUCT that
is controlled, not the blocks.  In particular, when the tie N(0,5) is a sub-branch of a parent, the
block equal to the tie's 11 nodes has det = 1.011..1.065 > 1 (the parent edge enhances the attachment
vertex's W_vv via the distance-2 reach of A^2).  So the tie's excess must be EXACTLY compensated by the
neighbouring block -- a cross-boundary cancellation, not a per-block bound.

FINDING 4 (unification -- why this route does not escape the wall).  For a bipartite tree
det(W) = phi^2, and the Fischer defect  log prod_B det(W[B]) - log det(W) >= 0  is exactly the
cross-block correlation discarded by the partition.  Since log det(W) = 2 log Phi and the exact
per-vertex decomposition of log Phi IS the cavity telescoping (cavity_potential.py), the block route
and the potential route are two views of the SAME object; the block-boundary leakage of Finding 3 is
the per-vertex potential slack.  The tie has phi^2 = 1 with ZERO determinant margin, so the discarded
correlations accumulate with no budget -- the identical marginal-tie criticality that leaves the
potential route with its residual +0.0006.  Bounded-block Fischer is therefore NOT an independent path
around the marginal tie.

HONEST SCOPE.  This module DOWNGRADES the interlacing lead; it does not prove an impossibility theorem.
What is established: best-of-{3,5,7,9} fails (Finding 1, exact); small fixed B0 fails (Finding 2,
concrete witness); the route reduces to the same log det(W)=2 log Phi marginal-tie obstruction
(Findings 3-4).  What is NOT established: that NO fixed B0 works for ALL trees -- the >1 witnesses are
moderate-n "critical bumps" that did not tile into a clean family forcing unbounded blocks (connector
gluing is sub-critical and drags phi^2 -> 0).  Net: requirement (a) has no empirical support and the
route is not independent of the potential route.  Phi<=1 remains OPEN.

Requires numpy.  Reuses interlacing.build_W / block_fischer / best_block_fischer.
"""
from __future__ import annotations

import numpy as np

from verification import interlacing as IL

ARM = (0, [(0, [])])


def N(c, k):
    """Near-star gadget: root with c cherries and k cherry-arm children. Tie iff c+k=5."""
    return (c, [ARM] * k)


def _count(C):
    c, kids = C
    return 1 + sum(_count(k) for k in kids)


def _phi2(C):
    return float(np.linalg.det(IL.build_W(C)[0]))


# A concrete 36-node NON-tie witness (phi^2 = 0.7893) on which greedy bounded-block Fischer stays > 1
# until B0 = 24 (a block covering 67% of the tree; B0=17 gives 1.0976).  Hard-coded for
# reproducibility (found by adversarial assembly of tie / near-tie gadgets under low-degree
# connectors).  Small / moderate fixed block sizes are demonstrably insufficient.
WITNESS_36 = (2, [(0, [(0, [(1, [(1, [(1, [(0, [(0, [])]), (0, [(0, [])]), (0, [(0, [])]),
             (0, [(0, [])]), (0, [(0, [])])]), (0, [(0, [])]), (0, [(0, [])])]), (0, [(0, [])]),
             (0, [(0, [])])]), (0, [(0, [])]), (0, [(0, [])])]), (0, [(0, [])]), (0, [(0, [])])]),
             (0, [(0, [])]), (0, [(0, [])])])


def finding1_best_of_small_fails_on_big_tie():
    """best-of-{3,5,7,9} block-Fischer EXCEEDS 1 on the isolated 11-node tie N(0,5)."""
    val = IL.best_block_fischer(N(0, 5), (3, 5, 7, 9))
    return {
        "tie": "N(0,5)", "nodes": _count(N(0, 5)), "phi2": _phi2(N(0, 5)),
        "best_of_3_5_7_9": val,
        "exceeds_1": val > 1 + 1e-6,
        "min_B0_to_capture_tie": 11,
    }


def finding2_small_fixed_B0_insufficient(C=WITNESS_36):
    """A valid non-tie tree on which bounded-block Fischer needs a block spanning ~2/3 of the tree."""
    n = _count(C)
    table = {b0: round(IL.block_fischer(C, b0), 4) for b0 in range(9, n + 1, 2)}
    min_b0 = next((b0 for b0 in range(3, n + 1) if IL.block_fischer(C, b0) <= 1 + 1e-9), None)
    return {
        "nodes": n, "phi2_le_1": _phi2(C) <= 1 + 1e-12, "phi2": round(_phi2(C), 4),
        "fischer_at_B0_17": table.get(17),
        "min_B0_for_product_le_1": min_b0,
        "block_covers_fraction": None if min_b0 is None else round(min_b0 / n, 2),
        "small_fixed_B0_insufficient": (min_b0 is not None and min_b0 >= 17),
    }


def finding3_captured_tie_leaks_at_boundary():
    """The 11-node tie N(0,5), as a child of a parent, has block det > 1 (boundary enhancement)."""
    C = (0, [N(0, 5)])                       # bare c=0 parent with the tie as its only child
    W, edges, n = IL.build_W(C)
    tie_nodes = list(range(1, n))            # everything except the root parent (node 0)
    det_tie = float(np.linalg.det(W[np.ix_(tie_nodes, tie_nodes)]))
    return {"tie_block_det_when_attached": det_tie, "exceeds_1": det_tie > 1 + 1e-9,
            "note": "excess must be compensated by the parent block; per-block <=1 is false"}


def certify():
    f1 = finding1_best_of_small_fails_on_big_tie()
    f2 = finding2_small_fixed_B0_insufficient()
    f3 = finding3_captured_tie_leaks_at_boundary()
    return {
        "best_of_3_5_7_9_fails_on_N05_tie": f1["exceeds_1"],       # True: 1.032
        "small_fixed_B0_insufficient": f2["small_fixed_B0_insufficient"],  # True: witness needs B0=25
        "captured_tie_leaks_above_1": f3["exceeds_1"],             # True: ~1.065
        "universal_bounded_block_supported": False,
        "route_is_independent_of_potential": False,                # same log det(W)=2 log Phi object
        "phi_le_1_closed_by_this_route": False,
        "f1": f1, "f2": f2, "f3": f3,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(certify(), indent=2, default=float))

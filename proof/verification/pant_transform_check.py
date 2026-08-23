"""Verify the Wu-Dong-Lai (arXiv:2402.15669) transformation lemmas hold in our engine (exact pi).

Companion to docs/design/LITERATURE_SYNTHESIS_20260823.md.  These are the transferable transformation
bricks for the Laplacian ratio pi(T)=per(L(T))/prod d(v); each is checked here in exact rational pi
(verification.permanent.laplacian_ratio) to confirm it matches our engine before any adoption.

Bricks checked:
 - Lemma 2.9 (pendant redistribution): for T'' with two deg-2 vertices u,v carrying s,t pendants,
   pi(T_split) > min(pi(all-on-u), pi(all-on-v)).  (A MINIMIZATION tool -- the split is never the
   minimizer; drives arbitrary trees toward the broom.)
 - Lemma 2.3 (pendant-deletion recursion): per L(G) = per L(G-v) + 2 per L_u(G-v) for a pendant v~u,
   checked as an exact integer identity on random small trees.

HONEST SCOPE: these lemmas are VALID and transferable, but the SAME authors used this toolkit to
conjecture the maximizer and were REFUTED by Pant (arXiv:2605.14176).  So the transformation route
REDUCES trees to caterpillars/near-stars but does NOT close the maximizer -- the final comparison is
the marginal tie (our R3 / Phi<=1 crux).  See the synthesis doc.  conjecture1_proved = False.
Requires numpy, networkx.  Self-verifying.
"""
from __future__ import annotations

import warnings

import networkx as nx
import numpy as np

from verification.permanent import laplacian_ratio, ryser_laplacian_permanent


def _lap(A):
    d = A.sum(1)
    return np.diag(d) - A


def _T2side(su, sv):
    """T'' = path a-u-b-v-c (u=1,v=3 interior deg-2); su pendants on u, sv on v."""
    G = nx.Graph()
    G.add_edges_from([(0, 1), (1, 2), (2, 3), (3, 4)])
    nxt = 5
    for _ in range(su):
        G.add_edge(1, nxt)
        nxt += 1
    for _ in range(sv):
        G.add_edge(3, nxt)
        nxt += 1
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def verify() -> dict:
    warnings.filterwarnings("ignore")
    out = {}

    # Lemma 2.9: pi(split) > min(pi(consolidate-u), pi(consolidate-v))
    l29 = {}
    l29_ok = True
    for s, t in [(3, 1), (4, 2), (5, 3), (6, 1), (5, 5), (7, 2)]:
        piT = laplacian_ratio(_T2side(s, t))
        pi1 = laplacian_ratio(_T2side(s + t, 0))
        pi2 = laplacian_ratio(_T2side(0, s + t))
        ok = piT > min(pi1, pi2)
        l29[f"s{s}t{t}"] = ok
        if not ok:
            l29_ok = False
    out["lemma29_split_gt_min_consolidation"] = l29_ok
    out["lemma29_cases"] = l29

    # Lemma 2.3: per L(G) = per L(G-v) + 2 per L_u(G-v) for a pendant v~u (exact integer identity).
    # per L via Ryser on the full Laplacian (general, not tree-restricted, since L_u deletions are used).
    def per_L(A):
        return round(ryser_laplacian_permanent(_lap(A).astype(float)))

    def per_M(M):
        return round(ryser_laplacian_permanent(M))

    l23_ok = True
    rng_trees = [
        [(0, 1), (1, 2), (1, 3), (3, 4)],                     # small tree
        [(0, 1), (1, 2), (2, 3), (2, 4), (4, 5), (0, 6)],     # bigger
        [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (6, 7)],
    ]
    for edges in rng_trees:
        G = nx.Graph()
        G.add_edges_from(edges)
        n = G.number_of_nodes()
        # pick a pendant v and its neighbor u
        v = next(x for x in G if G.degree[x] == 1)
        u = next(iter(G[v]))
        A = nx.to_numpy_array(G, nodelist=sorted(G), dtype=int)
        # G - v
        Gv = G.copy()
        Gv.remove_node(v)
        Av = nx.to_numpy_array(Gv, nodelist=sorted(Gv), dtype=int)
        # L_u(G-v): delete row/col of u from L(G-v)
        Lv = _lap(Av).astype(float)
        idx = sorted(Gv)
        ui = idx.index(u)
        Luv = np.delete(np.delete(Lv, ui, 0), ui, 1)
        lhs = per_L(A)
        rhs = per_M(Lv) + 2 * per_M(Luv)
        if lhs != rhs:
            l23_ok = False
    out["lemma23_pendant_deletion_recursion"] = l23_ok

    out["note"] = ("Wu transformation lemmas hold in our engine (exact). VALID reduction toolkit "
                   "(= our R1-R6), but PROVEN insufficient to close the maximizer: the same authors "
                   "used it and were refuted by Pant. The marginal tie (R3/Phi<=1) is irreducible.")
    out["conjecture1_proved"] = False

    assert out["lemma29_split_gt_min_consolidation"], "Wu Lemma 2.9 failed in our engine!"
    assert out["lemma23_pendant_deletion_recursion"], "Wu Lemma 2.3 deletion recursion failed!"
    return out


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

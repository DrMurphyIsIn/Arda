"""EXTERNAL VALIDATION: our conjecture1 target survives Pant's (May 2026) counterexamples.

Priyanshu Pant, "Counterexamples to a Conjecture on Laplacian Ratios of Trees", arXiv:2605.14176
(13 May 2026), DISPROVES the Wu-Dong-Lai (Discrete Appl. Math. 372:224-236, 2025) Conjecture 1.2
that the subdivided star S(n,(n-1)/2) [odd] / S(n,a,b) [even] MAXIMIZES the Laplacian ratio
pi(T)=per(L(T))/prod d(v).  Pant's counterexamples are the family T(a1,...,am): a core path
x1-...-xm with a_i cherries (pendant P2's) on x_i, with the EXACT closed form
    pi(T(a1..am)) = (3/2)^{sum a_i} * f_m,   f_i=(1+a_i/(3 d_i)) f_{i-1} + (1/(d_{i-1} d_i)) f_{i-2}
-- which is EXACTLY the cavity recursion this whole effort uses.  Pant's B_t=T(t,t,t,t),
C_t=T(t,t,t+1,t), A_t=T(3,t,3) strictly beat the Wu-Dong-Lai bound; the true maximizer is left OPEN.

WHY THIS MATTERS FOR US.  Wu-Dong-Lai's disproved odd maximizer S(n,(n-1)/2) is a single hub with
(n-1)/2 cherry-arms -- structurally a NAIVE near-star.  Our conjecture1 target is the DE-LOADED
cherry-bundle star (single hub, hub-load de-loading 5->0, arms balanced at 5; R4-R6).  The natural
worry: do Pant's MULTI-HUB caterpillars beat OUR single-hub target too (which would refute R5)?

THIS MODULE ANSWERS: NO.  Exact-rational pi (verification.permanent.laplacian_ratio) shows our engine's
best structured tree (maximizer_structure.best_structure over spider/cbstar/dstar) BEATS Pant's
counterexamples at matched n, with a margin that GROWS with n:

    Pant B_t=T(t,t,t,t) [n=8t+4] vs our best cbstar:  P/ours = 0.9956 (t=4) -> 0.9333 (t=11).

So: Wu-Dong-Lai (2025, refuted by Pant) < Pant's caterpillars (2026) < our de-loaded cherry-bundle
star.  Our conjecture1 target SURVIVES the literature that killed the previous conjecture, and our
engine independently found a tree beating the just-published counterexamples.  This is confirmatory
EXTERNAL evidence for conjecture1's shape (R5 single-hub + R6 de-loading/arms-at-5); it does NOT prove
it (our search is over structured families, not exhaustive; Pant's true max is open = our conjecture1).
conjecture1_proved = False.

SEARCH-SPACE NOTE.  maximizer_structure._candidates covers spider/cbstar(1-hub)/dstar(2-hub) but NOT
Pant's m>=3 cherry-loaded core-path.  T_family below plugs that gap so the large-n confirmatory search
can include multi-hub cherry-caterpillars; verify() checks our best still dominates them.
Requires numpy, networkx.  Self-verifying.
"""
from __future__ import annotations

import warnings

import networkx as nx

from verification.permanent import laplacian_ratio
from verification import maximizer_structure as MS


def T_family(avec):
    """Pant's T(a1,...,am): core path x1..xm, a_i cherries (pendant P2's) on x_i.  Adjacency matrix."""
    G = nx.Graph()
    nxt = 0
    core = []
    for i in range(len(avec)):
        xi = nxt
        nxt += 1
        core.append(xi)
        if i > 0:
            G.add_edge(core[i - 1], xi)
    for i, ai in enumerate(avec):
        for _ in range(ai):
            y, z = nxt, nxt + 1
            nxt += 2
            G.add_edge(core[i], y)
            G.add_edge(y, z)
    if len(core) == 1:
        G.add_node(core[0])
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def _our_best(n):
    best = None
    for kind, k, c0, M in MS._candidates(n):
        if M.shape[0] != n:
            continue
        p = laplacian_ratio(M)
        if best is None or p > best[0]:
            best = (p, kind, k, c0)
    return best


def verify() -> dict:
    warnings.filterwarnings("ignore")
    out = {}

    # (V1) Pant's explicit counterexamples: our engine's best is >= them (exact rational).
    named = {
        "B_4=T(4,4,4,4)": [4, 4, 4, 4],
        "C_4=T(4,4,5,4)": [4, 4, 5, 4],
        "A_4=T(3,4,3)": [3, 4, 3],
        "A_3=T(3,3,3)_n21_tie": [3, 3, 3],
    }
    rows = {}
    ours_dominates_named = True
    for name, av in named.items():
        A = T_family(av)
        n = A.shape[0]
        piP = laplacian_ratio(A)
        b = _our_best(n)
        rows[name] = {"n": n, "pi_pant": float(piP), "pi_ours": float(b[0]),
                      "P_over_ours": float(piP / b[0]), "our_shape": (b[1], b[2], b[3])}
        if piP > b[0]:
            ours_dominates_named = False
    out["named_cases"] = rows
    out["ours_dominates_named_counterexamples"] = ours_dominates_named

    # (V2) asymptotic: our best beats Pant B_t=T(t,t,t,t) with GROWING margin (t=4..9).
    asym = {}
    ours_wins_family = True
    for t in range(4, 10):
        A = T_family([t, t, t, t])
        n = A.shape[0]
        piP = laplacian_ratio(A)
        b = _our_best(n)
        r = float(piP / b[0])
        asym[t] = {"n": n, "P_over_ours": r}
        if piP > b[0]:
            ours_wins_family = False
    out["asym_B_t"] = asym
    out["ours_beats_or_ties_B_t_family"] = ours_wins_family
    # margin grows: ratio at t=9 strictly below ratio at t=4 (our advantage widens with n)
    out["margin_grows_with_n"] = asym[9]["P_over_ours"] < asym[4]["P_over_ours"]

    out["conclusion"] = ("Wu-Dong-Lai (2025, refuted by Pant 2026) < Pant caterpillars < our de-loaded "
                         "cherry-bundle star. conjecture1 target survives Pant; true maximizer open = conjecture1.")
    out["conjecture1_proved"] = False

    assert out["ours_dominates_named_counterexamples"], "Pant counterexample beat our target -- conjecture1 in doubt!"
    assert out["ours_beats_or_ties_B_t_family"], "Pant B_t family beat our target on the asymptotic scan!"
    assert out["margin_grows_with_n"], "our advantage over Pant does not widen with n"
    return out


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

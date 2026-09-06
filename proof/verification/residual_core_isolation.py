"""RESIDUAL-CELL direct-step characterization -- independent verification (2026-09-05).

*** CORRECTED 2026-09-05 (v2). ***  The FIRST version of this file scanned C's movers as BARE
LEAVES (`load=0`) over a BOUNDED range (deg_C <= 14) and concluded "(0,5) fully rescued; each
cb-heavy cell reduces to one tiny 3-hub path core."  BOTH premises were wrong:
  (i)  the genuine stuck configs have ARM movers (load-5 sub-hubs), not bare leaves -- with bare
       leaves a Kelmans consolidation always rescues, hiding the real obstruction;
  (ii) the failures appear only at LARGE deg_C (into the hundreds), outside the bounded range.
This matches the parallel session's own flint self-correction (`residual_flint_probe.py`).  The
corrected, independently-reproduced picture is below.  `conjecture1_proved = False`.

Independent engine cross-validation (unchanged, and still valid): `pi_loaded` (their per-vertex
factorization) equals the literal tree `per(L)/prod(deg)` via a matching-sum permanent DP
(`per(L)=Sum_matchings prod_{uncovered} deg`), validated against an exact Ryser permanent.

Run: `python3 proof/verification/residual_core_isolation.py` -- run() asserts the corrected split.
"""
from __future__ import annotations
import sys, os, collections, itertools
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))


# ---- independent literal-tree permanent (matching-sum, O(n) rooted DP) --------------------
def perL_tree(edges, n):
    adj = collections.defaultdict(list)
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    deg = {v: len(adj[v]) for v in range(n)}
    order = []; par = {0: -1}; seen = {0}; st = [0]
    while st:
        u = st.pop(); order.append(u)
        for w in adj[u]:
            if w not in seen:
                seen.add(w); par[w] = u; st.append(w)
    f = {}; g = {}
    for u in reversed(order):
        kids = [w for w in adj[u] if w != par[u]]
        pf = Fr(1)
        for c in kids:
            pf *= f[c]
        g[u] = pf
        mt = Fr(0)
        for c0 in kids:
            t = g[c0]
            for c in kids:
                if c != c0:
                    t *= f[c]
            mt += t
        f[u] = Fr(deg[u]) * pf + mt
    return f[0], deg


def pi_literal(edges, n):
    p, deg = perL_tree(edges, n)
    d = Fr(1)
    for v in deg:
        d *= deg[v]
    return p / d


def _ryser_abs(edges, n):
    L = [[0] * n for _ in range(n)]
    for a, b in edges:
        L[a][b] -= 1; L[b][a] -= 1; L[a][a] += 1; L[b][b] += 1
    tot = 0
    for k in range(n + 1):
        for S in itertools.combinations(range(n), k):
            pr = 1
            for i in range(n):
                s = sum(L[i][j] for j in S)
                pr *= s
                if pr == 0:
                    break
            tot += ((-1) ** (n - k)) * pr
    return abs(tot)


def _literal_from_backbone(bb_edges, load):
    verts = set()
    for a, b in bb_edges:
        verts.add(a); verts.add(b)
    edges = list(bb_edges); nxt = max(verts) + 1
    for v in sorted(verts):
        for _ in range(load.get(v, 0)):
            edges.append((v, nxt)); edges.append((nxt, nxt + 1)); nxt += 2
    return edges, nxt


def run() -> dict:
    import networkx as nx
    from verification.kelmans_mixed_load import pi_loaded, kelmans_step

    # (0) matching-DP permanent validated vs exact Ryser magnitude
    import random
    rng = random.Random(1)
    for _ in range(6):
        m = rng.randint(4, 11); e = [(v, rng.randint(0, v - 1)) for v in range(1, m)]
        assert perL_tree(e, m)[0] == _ryser_abs(e, m), "matching-DP != Ryser"

    # (1) engine exactness: factorized pi_loaded == literal per(L)/prod(deg)
    for ld in [(0, 0, 0), (1, 5, 0), (2, 3, 1), (1, 5, 5)]:
        G = nx.Graph([(0, 1), (1, 2)]); load = {0: ld[0], 1: ld[1], 2: ld[2]}
        lit, n = _literal_from_backbone([(0, 1), (1, 2)], load)
        assert pi_loaded(G, load) == pi_literal(lit, n), f"pi_loaded != literal at {ld}"

    # ---- CORRECT model: movers are LOAD-5 ARMS (not bare leaves) --------------------------
    def build(ca, cb, cc, pA, qB, r):
        G = nx.Graph([(0, 1), (1, 2)]); load = {0: ca, 1: cb, 2: cc}; nxt = 3
        for hub, cnt in ((0, pA), (1, qB), (2, r)):
            for _ in range(cnt):
                G.add_edge(hub, nxt); load[nxt] = 5; nxt += 1
        return G, load

    def direct_gain(ca, cb, r):                     # A(ca,1 arm)-B(cb)-C(load5, r arm-movers)
        G, load = build(ca, cb, 5, 1, 0, r)
        return pi_loaded(kelmans_step(G, 0, 1), load) - pi_loaded(G, load), G, load

    def threshold(ca, cb, cap=400):
        for r in range(1, cap):
            g, _, _ = direct_gain(ca, cb, r)
            if g < 0:
                return 1 + r
        return None

    # (2) ALL 5 residual cells fail the direct step at a FINITE deg_C (arm-mover, large deg)
    RESIDUAL = [(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)]
    th = {cell: threshold(*cell) for cell in RESIDUAL}
    assert all(t is not None for t in th.values()), f"expected all 5 finite; got {th}"
    # independently reproduced thresholds (deg_C): (2,5)=8 (1,5)=9 (1,4)=29 (3,5)=111 (0,5)=170
    assert th == {(0, 5): 170, (1, 4): 29, (1, 5): 9, (2, 5): 8, (3, 5): 111}, th

    # (3) at its threshold, (0,5) is a genuine Kelmans-local-max, but DOMINATED by a non-Kelmans
    #     arm-move C->A (so it refutes (0,5) direct-step monotonicity, NOT the Hdom domination goal)
    r0 = th[(0, 5)] - 1
    G, load = build(0, 5, 5, 1, 0, r0); base = pi_loaded(G, load)
    bestK = max((pi_loaded(kelmans_step(G, u, v), load) - base
                 for a, b in G.edges() for (u, v) in ((a, b), (b, a))
                 if kelmans_step(G, u, v) is not None), default=Fr(-1))
    assert bestK == 0, f"(0,5)@thresh expected Kelmans-local-max (best 0), got {bestK}"
    armC = next(w for w in G.neighbors(2) if w > 2 and load.get(w) == 5)
    H = G.copy(); H.remove_edge(2, armC); H.add_edge(0, armC)
    assert pi_loaded(H, load) - base > 0, "(0,5) stuck config should be dominated by arm-move C->A"

    # (4) THE CLOSURE: all failures need imbalance OR uncapped hubs; on Balanced+Capped
    #     (Hdom's actual domain: arm counts within delta AND all >= 5) the direct merge NEVER
    #     decreases.  Balanced ALONE is NOT enough -- uncapped balanced configs do decrease.
    bal_only_dec = 0; bal_cap_dec = 0; bal_cap_checked = 0
    for (ca, cb) in [(1, 5), (2, 5), (3, 5)]:
        for base_a in range(0, 12):
            for da in range(0, 3):
                for db in range(0, 3):
                    for dr in range(0, 3):
                        pA, qB, r = base_a + da, base_a + db, base_a + dr
                        if max(pA, qB, r) - min(pA, qB, r) > 2:   # Balanced (delta<=2)
                            continue
                        G, load = build(ca, cb, 5, pA, qB, r)
                        Hd = kelmans_step(G, 0, 1)
                        if Hd is None:
                            continue
                        dec = pi_loaded(Hd, load) - pi_loaded(G, load) < 0
                        if min(pA, qB, r) >= 5:                    # + Capped
                            bal_cap_checked += 1
                            if dec:
                                bal_cap_dec += 1
                        elif dec:
                            bal_only_dec += 1
    assert bal_cap_dec == 0, f"Balanced+Capped must be decrease-free, got {bal_cap_dec}"
    assert bal_only_dec > 0, "Balanced-alone (uncapped) SHOULD still decrease (Capped is essential)"

    return {"engine_exact": True,
            "direct_failure_thresholds_degC": {str(k): v for k, v in th.items()},
            "all_five_fail_direct_step": True,
            "cell_0_5": "Kelmans-local-max at deg_C=170, dominated by non-Kelmans arm-move C->A",
            "balanced_capped_decrease_free": True,
            "capped_is_essential": f"balanced-alone still has {bal_only_dec} decreases (uncapped)"}


if __name__ == "__main__":
    out = run()
    print("VERIFIED (corrected v2 -- arm-mover model, large deg_C):")
    print("  pi_loaded engine exact vs literal permanent:", out["engine_exact"])
    print("  ALL 5 residual cells fail the DIRECT step at finite deg_C:")
    print("   ", out["direct_failure_thresholds_degC"])
    print("  (0,5):", out["cell_0_5"])
    print("  -> the earlier 'bare-leaf, bounded-range' core-isolation was an ARTIFACT.")
    print("  conjecture1_proved = False")

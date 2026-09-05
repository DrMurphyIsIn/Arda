"""RESIDUAL-CELL CORE ISOLATION -- independent verification + sharpening of the
`residual_hub_mover_probe` / anti-hubward-rescue findings (2026-09-05).

This is an INDEPENDENT re-derivation (own driver + own permanent) that (a) validates the
`kelmans_mixed_load.pi_loaded` engine against a literal tree permanent, (b) confirms the
direct-hubward-step split, and (c) SHARPENS the "anti-hubward rescues 54/54, zero genuinely
stuck" claim: across all in-scope direct-step failures, the strict rescuer is a Kelmans move
(K) OR the leg->cherry move (L, = R2, proven) -- EXCEPT exactly ONE tiny config per cb-heavy
cell, a 3-hub loaded PATH, which no K or L move strictly progresses. Those 4 cores are exactly
what the (H) hub-merge/de-load (R5/R6, crux (26/23)^11 < 621/64) is for.

Engine cross-validation method (independent of both networkx and the cavity Ztot):
  per(L(tree)) = sum over matchings M of prod_{v uncovered by M} deg(v)
(the only nonzero permutations of a tree Laplacian are 2-cycles along disjoint edges), via an
O(n) rooted DP. Validated against an exact Ryser permanent (|value|) on random trees.

Run: `python3 proof/verification/residual_core_isolation.py` -- run() asserts the whole split.
conjecture1_proved = False.
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
    from verification.kelmans_mixed_load import pi_loaded, kelmans_step, z_of

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

    def build(ca, cb, cc, r):
        G = nx.Graph([(0, 1), (1, 2)]); load = {0: ca, 1: cb, 2: cc}; nxt = 3
        for _ in range(r):
            G.add_edge(2, nxt); load[nxt] = 0; nxt += 1
        return G, load

    def best_kelmans(G, load):
        base = pi_loaded(G, load); best = Fr(-10 ** 9)
        for a, b in list(G.edges()):
            for u, v in [(a, b), (b, a)]:
                H = kelmans_step(G, u, v)
                if H is None:
                    continue
                g = pi_loaded(H, load) - base
                if g > best:
                    best = g
        return best

    def best_L(G, load):
        base = pi_loaded(G, load); best = None
        for w in list(G.nodes()):
            if G.degree(w) == 1 and load.get(w, 0) == 0:
                hub = next(iter(G.neighbors(w)))
                H = G.copy(); H.remove_node(w)
                nl = dict(load); nl.pop(w, None); nl[hub] = nl[hub] + 1
                g = pi_loaded(H, nl) - base
                if best is None or g > best:
                    best = g
        return best

    # (2)+(3) split + K/L rescue counts + core isolation
    cores = {}
    per_cell = {}
    for (ca, cb) in [(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)]:
        fails = 0; unrescued = []
        for r in range(0, 14):
            for cc in range(0, 6):
                G, load = build(ca, cb, cc, r)
                if z_of(G.degree(2), cc) > Fr(3, 23):
                    continue
                base = pi_loaded(G, load)
                Hd = kelmans_step(G, 0, 1)
                if Hd is None:
                    continue
                if pi_loaded(Hd, load) - base < 0:      # direct hubward genuinely decreases
                    fails += 1
                    bk = best_kelmans(G, load); bl = best_L(G, load)
                    if not (bk > 0 or (bl is not None and bl > 0)):
                        unrescued.append((r, cc, {k: v for k, v in load.items() if v}))
        per_cell[(ca, cb)] = fails
        cores[(ca, cb)] = unrescued

    # ASSERTIONS -- the verified split
    assert per_cell[(0, 5)] > 0, "(0,5) should have in-scope direct failures"
    assert cores[(0, 5)] == [], "(0,5) fully rescued by K/L"
    for cell in [(1, 4), (1, 5), (2, 5), (3, 5)]:
        u = cores[cell]
        assert len(u) == 1, f"{cell} expected exactly 1 K/L-unrescued core, got {len(u)}"
        r, cc, ld = u[0]
        assert r == 0 and cc == 5, f"{cell} core should be the 3-hub path r=0 cc=5, got r={r} cc={cc}"
    return {"per_cell_direct_failures": per_cell,
            "KL_unrescued_cores": {str(k): v for k, v in cores.items()}}


if __name__ == "__main__":
    out = run()
    print("VERIFIED residual-core isolation:")
    print("  direct-hubward in-scope failures per cell:", out["per_cell_direct_failures"])
    print("  K/L-unrescued cores (the genuine hard core):")
    for cell, u in out["KL_unrescued_cores"].items():
        print(f"    {cell}: {u}")
    print("  -> (0,5) fully K/L-rescued; the 4 cb-heavy cells each reduce to ONE 3-hub")
    print("     loaded path {A:ca,B:cb,C:5}, resolved only by (H) de-load (R5/R6).")
    print("  conjecture1_proved = False")

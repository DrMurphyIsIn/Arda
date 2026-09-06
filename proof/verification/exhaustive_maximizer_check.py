"""EXHAUSTIVE per-n maximizer of Aobj = per(L)/prod(deg) over ALL trees (2026-09-06).

Confidence instrument M2(1) of the BG closure plan: the previously-MISSING exhaustive
non-isomorphic free-tree enumeration. For each n it computes the EXACT `pi(T)=per(L(T))/prod deg`
for EVERY non-isomorphic tree (via `nx.nonisomorphic_trees` = the WROM/Beyer-Hedetniemi generator
+ the validated matching-sum permanent DP), finds the argmax, and CHARACTERIZES its structure.

Purpose: de-risk the load-bearing assumption behind the whole closure (that the broadened single-hub
family is the maximizer). The HONEST finding it establishes:
  * the SMALL-n maximizer is a caterpillar/spider (a few degree-3..5 "hubs" joined by degree-2 paths),
    NOT the single-hub broadened family -- the broadened family is the ASYMPTOTIC/aligned maximizer;
  * max hub-degree grows slowly with n and the maximizer stays a "path-spine spider" through the
    enumerable range -- consistent with Pant 2026 (arXiv:2605.14176: global maximizer OPEN) and the
    plan's non-aligned-n gap (M8). Exhaustive enumeration verifies the maximizer FAMILY per n<=N;
    the large-n / aligned claim is the complementary asymptotic instrument M2(3).

`per(L(tree)) = sum_matchings prod_{v uncovered} deg(v)` (validated vs flint-Ryser earlier).
Run: `python3 proof/verification/exhaustive_maximizer_check.py [Nmax]`. run() asserts correctness
+ records the per-n maximizer. `conjecture1_proved = False`.
"""
from __future__ import annotations
import sys, collections
from fractions import Fraction as Fr


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
        kids = [w for w in adj[u] if w != par[u]]; pf = Fr(1)
        for c in kids:
            pf *= f[c]
        g[u] = pf; mt = Fr(0)
        for c0 in kids:
            t = g[c0]
            for c in kids:
                if c != c0:
                    t *= f[c]
            mt += t
        f[u] = Fr(deg[u]) * pf + mt
    return f[0], deg


def pi_of(T):
    e = list(T.edges()); n = T.number_of_nodes()
    p, deg = perL_tree(e, n)
    d = Fr(1)
    for v in deg:
        d *= deg[v]
    return p / d


def _classify(T):
    """Structure class of the argmax tree: single-hub-star / spider / caterpillar / path."""
    deg = dict(T.degree())
    branch = [v for v in deg if deg[v] >= 3]          # hubs
    leaves = [v for v in deg if deg[v] == 1]
    maxdeg = max(deg.values())
    if len(branch) == 0:
        return "path", maxdeg, 0
    if len(branch) == 1:
        return "single-hub", maxdeg, 1
    # remove leaves; if the remaining "spine" is a path, it's a caterpillar/spider
    import networkx as nx
    core = T.subgraph([v for v in deg if deg[v] >= 2]).copy()
    is_cat = all(d <= 2 for _, d in core.degree()) if core.number_of_nodes() else True
    return ("caterpillar/spider" if is_cat else "branched"), maxdeg, len(branch)


def run(Nmax: int = 18) -> dict:
    import networkx as nx
    # (0) correctness: matching-DP pi vs an independent Ryser permanent on small trees
    import itertools
    def ryser_abs(edges, n):
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
    for T in nx.nonisomorphic_trees(7):
        e = list(T.edges())
        assert perL_tree(e, 7)[0] == ryser_abs(e, 7), "matching-DP != Ryser"

    out = {}
    for n in range(2, Nmax + 1):
        best = None
        for T in nx.nonisomorphic_trees(n):
            r = pi_of(T)
            if best is None or r > best[0]:
                best = (r, T)
        r, T = best
        cls, maxdeg, nhub = _classify(T)
        degseq = tuple(sorted((d for _, d in T.degree()), reverse=True))
        out[n] = {"max_pi": float(r), "class": cls, "max_deg": maxdeg,
                  "n_hubs": nhub, "deg_seq": degseq}

    # ASSERTIONS -- the honest, decisive findings (RECORD the structure, don't presuppose it)
    # (a) low branching throughout: the maximizer is a cherry-spider / caterpillar, at most 2 hubs.
    for n, d in out.items():
        assert d["n_hubs"] <= 2, f"n={n}: expected <=2 hubs (cherry-spider regime), got {d['n_hubs']}"
    # (b) PARITY OSCILLATION (the small-n / non-aligned-n structure, made exact):
    #     odd n>=7 -> a SINGLE cherry-spider hub; even n>=10 -> TWO hubs.
    for n, d in out.items():
        if n >= 7 and n % 2 == 1:
            assert d["n_hubs"] == 1, f"odd n={n} should be single-hub, got {d['n_hubs']}"
        if n >= 10 and n % 2 == 0:
            assert d["n_hubs"] == 2, f"even n={n} should be two-hub, got {d['n_hubs']}"
    # (c) the arms are CHERRIES (load-1), NOT load-5: the single (odd-n) hub has degree (n-1)/2,
    #     which GROWS with n -- inconsistent with any fixed broadened (load-4/5-arm) hub. So the
    #     broadened single-hub family is the ASYMPTOTIC/aligned maximizer, not the small-n one.
    for n, d in out.items():
        if n >= 7 and n % 2 == 1:
            assert d["max_deg"] == (n - 1) // 2, f"odd n={n} cherry-spider hub deg should be {(n-1)//2}"
    return out


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    res = run(N)
    print(f"EXHAUSTIVE per-n maximizer of pi=per(L)/prod(deg), all non-iso trees, n<= {N}:")
    print(f"{'n':>3} {'max_pi':>10}  {'maxdeg':>6} {'hubs':>4}  class / degree-sequence")
    for n, d in res.items():
        print(f"{n:>3} {d['max_pi']:>10.4f}  {d['max_deg']:>6} {d['n_hubs']:>4}  {d['class']}  {d['deg_seq']}")
    print("\nHONEST FINDING: the maximizer stays a low-degree caterpillar/spider through the")
    print("enumerable range -- the broadened SINGLE-HUB family is the ASYMPTOTIC/aligned maximizer,")
    print("not the small-n one (the M8 non-aligned-n gap, made exact). Large-n dominance is the")
    print("complementary asymptotic instrument M2(3). conjecture1_proved = False")

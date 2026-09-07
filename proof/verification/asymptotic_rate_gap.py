"""ASYMPTOTIC RATE GAP: the broadened (load-5) family is the top-rate tree family (2026-09-06).

Confidence instrument M2(3) of the BG closure plan -- the LARGE-n bracket complementing the
exhaustive small-n check M2(1). It computes the per-vertex growth rate `pi(T)^(1/n)`
(pi = per(L)/prod deg, via the validated matching-DP) for large instances of each candidate tree
family, and confirms the single-hub LOAD-5 family (the broadened tie's asymptotic form) has the
STRICTLY HIGHEST rate `rhoB = (621/64)^(1/11) ≈ 1.22947`, beating:
  * cherry-spiders and Pant-2026 path-spine spiders (rate -> sqrt(3/2) ≈ 1.22474, a fixed gap;
    since it is a RATE the load-5 family dominates by an exponentially growing factor);
  * multi-hub load-5 caterpillars (rate < rhoB) -- confirming SINGLE-hub dominance asymptotically
    (the Piece-2 / Hdom multi-hub-domination direction).

Together with M2(1) (cherry-spiders win the small-n regime) this brackets the honest picture: the
broadened family is the ASYMPTOTIC/aligned maximizer; the arm-load-5 rate optimum is already
Lean-proven (`armObj_le_one`, R47ArmRate). This is EVIDENCE for the global-maximizer assumption at
large n (not a proof; Pant 2026 leaves the finite global maximizer OPEN). `conjecture1_proved = False`.

Run: `python3 proof/verification/asymptotic_rate_gap.py`. run() asserts the rate ordering.
"""
from __future__ import annotations
import collections, math
from fractions import Fraction as Fr

RHOB = (621 / 64) ** (1 / 11)          # ≈ 1.229474  (load-5 arm rate)
SQRT32 = math.sqrt(1.5)                # ≈ 1.224745  (cherry / spider rate)


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


def rate(edges, n):
    p, deg = perL_tree(edges, n)
    d = Fr(1)
    for v in deg:
        d *= deg[v]
    return float(p / d) ** (1.0 / n)


class _B:
    def __init__(self):
        self.e = []; self.n = 1

    def leaf(self, p):
        v = self.n; self.n += 1; self.e.append((p, v)); return v

    def cherry(self, p):
        m = self.leaf(p); self.leaf(m); return m

    def arm(self, p, load):
        a = self.leaf(p)
        for _ in range(load):
            self.cherry(a)
        return a


def _near_star(K):                      # single hub, K load-5 arms (broadened asymptotic form)
    b = _B()
    for _ in range(K):
        b.arm(0, 5)
    return b.e, b.n


def _cherry_spider(K):                  # single hub, K cherry arms
    b = _B()
    for _ in range(K):
        b.cherry(0)
    return b.e, b.n


def _pant_TTTt(t):                      # Pant path-spine spider T(t,t,t,t)
    b = _B(); spine = [0]
    for _ in range(3):
        spine.append(b.leaf(spine[-1]))
    for sv in spine:
        for _ in range(t):
            b.cherry(sv)
    return b.e, b.n


def _caterpillar_load5(m):              # spine of m hubs, each with 5 load-5 arms (multi-hub)
    b = _B(); spine = [0]
    for _ in range(m - 1):
        spine.append(b.leaf(spine[-1]))
    for sv in spine:
        for _ in range(5):
            b.arm(sv, 5)
    return b.e, b.n


def run() -> dict:
    r_ns = rate(*_near_star(40))
    r_cs = rate(*_cherry_spider(120))
    r_pant = rate(*_pant_TTTt(30))
    r_cat = rate(*_caterpillar_load5(8))

    # (a) load-5 near-star is the TOP rate, and it converges UP to rhoB
    assert r_ns > r_cs and r_ns > r_pant and r_ns > r_cat, "load-5 near-star must have top rate"
    assert r_ns < RHOB and abs(r_ns - RHOB) < 1e-3, "near-star rate should approach rhoB from below"
    # (b) spiders/cherry-spiders sit at the sqrt(3/2) rate, strictly below rhoB
    assert abs(r_cs - SQRT32) < 2e-3 and abs(r_pant - SQRT32) < 3e-3, "spider rate should be ~sqrt(3/2)"
    assert RHOB - SQRT32 > 4e-3, "the rhoB vs sqrt(3/2) rate gap must be a real positive constant"
    # (c) single-hub load-5 STRICTLY beats multi-hub load-5 caterpillar (Hdom direction, asymptotic)
    assert r_ns > r_cat, "single-hub load-5 must beat the multi-hub caterpillar rate"
    # (d) the near-star rate INCREASES toward rhoB with K (converging up), spiders DECREASE toward sqrt(3/2)
    assert rate(*_near_star(40)) > rate(*_near_star(10)), "near-star rate increases with K -> rhoB"
    assert rate(*_cherry_spider(120)) < rate(*_cherry_spider(40)), "cherry-spider rate decreases -> sqrt(3/2)"

    return {"rhoB": RHOB, "sqrt(3/2)": SQRT32,
            "near_star_K40": r_ns, "cherry_spider_K120": r_cs,
            "pant_TTTt_t30": r_pant, "caterpillar_load5_m8": r_cat,
            "rate_gap_rhoB_minus_sqrt32": RHOB - SQRT32}


if __name__ == "__main__":
    out = run()
    print("ASYMPTOTIC RATE GAP (per-vertex growth rate pi^(1/n), large instances):")
    print(f"  rhoB (load-5 limit)      = {out['rhoB']:.6f}")
    print(f"  near-star K=40           = {out['near_star_K40']:.6f}  (-> rhoB from below)")
    print(f"  caterpillar load5 m=8    = {out['caterpillar_load5_m8']:.6f}  (multi-hub < single-hub)")
    print(f"  Pant T(t,t,t,t) t=30     = {out['pant_TTTt_t30']:.6f}")
    print(f"  cherry-spider K=120      = {out['cherry_spider_K120']:.6f}")
    print(f"  sqrt(3/2) (spider limit) = {out['sqrt(3/2)']:.6f}")
    print(f"  RATE GAP rhoB - sqrt(3/2) = {out['rate_gap_rhoB_minus_sqrt32']:.6f} (>0, exponential in n)")
    print("  => the broadened load-5 family is the TOP-rate family; single-hub beats multi-hub.")
    print("  Complements M2(1) (cherry-spiders win small-n). conjecture1_proved = False")

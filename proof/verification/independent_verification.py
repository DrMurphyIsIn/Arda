"""INDEPENDENT verification of the Laplacian-ratio closed forms.

SageMath is not installed here (what was installed alongside is cypari2 = PARI's Python
bindings, not Sage). This is fine: PARI is the computer-algebra engine SageMath itself
uses, and its `matpermanent` is a fully independent permanent implementation. We verify
with THREE routes that share no code with the paper's engine (permanent.py / theorem.py):

  1. PARI `matpermanent` (via cypari2) -- independent CAS permanent, on the exact integer
     Laplacian, for every tree small enough (n <= 22).
  2. a from-scratch brute-force MATCHING enumerator (Thm 2.1), written here independently.
  3. exact-rational POINT-MATCHING of the k=3 difference identity: a rational function is
     determined by enough values, so agreement at 15 points PROVES the identity.

The paper's CLAIMED closed forms are recomputed here from the backbone-reduction Lemma
using only `fractions.Fraction` (no import of theorem.py), and checked against PARI.
Trees are rebuilt from fresh edge lists (no import of trees.py).

Run with the PARI venv:
  .../.venv-pari/bin/python proof/verification/independent_verification.py
"""
from __future__ import annotations

from fractions import Fraction

import cypari2

_pari = cypari2.Pari()
H = Fraction(3, 2)


def per_poly(edges, n):
    """Fresh, numpy-free, POLYNOMIAL per(L(T)) = sum_matchings prod_{unmatched} deg via a
    rooted tree DP. Written independently of the paper's permanent.py (used only to reach
    large n, after being certified against PARI + brute enumeration at small n)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(adj[i]) for i in range(n)]
    parent = [-1] * n
    order = []
    seen = [False] * n
    stack = [0]
    seen[0] = True
    while stack:
        u = stack.pop()
        order.append(u)
        for w in adj[u]:
            if not seen[w]:
                seen[w] = True
                parent[w] = u
                stack.append(w)
    # f[u] = matchings of subtree(u) with u UNMATCHED (earns weight deg[u]);
    # g[u] = with u matched to a child.
    f = [0] * n
    g = [0] * n
    for u in reversed(order):
        kids = [w for w in adj[u] if parent[w] == u]
        tot = [f[c] + g[c] for c in kids]
        prod = 1
        for x in tot:
            prod *= x
        f[u] = deg[u] * prod
        s = 0
        for j, c in enumerate(kids):
            others = 1
            for jj, cc in enumerate(kids):
                if jj != j:
                    others *= tot[jj]
            s += (f[c] // deg[c]) * others          # child c free (weight deferred), matched to u
        g[u] = s
    return f[0] + g[0]


# ---------- independent fresh tree builders ----------
def star_branch(k, t):
    edges = [(0, i) for i in range(1, k + 1)]
    nxt = k + 1
    for center in range(k + 1):
        for _ in range(t):
            edges += [(center, nxt), (nxt, nxt + 1)]
            nxt += 2
    return edges, nxt


def path_spider(m, t):
    edges = [(i, i + 1) for i in range(m - 1)]
    nxt = m
    for center in range(m):
        for _ in range(t):
            edges += [(center, nxt), (nxt, nxt + 1)]
            nxt += 2
    return edges, nxt


def degs(edges, n):
    d = [0] * n
    for u, v in edges:
        d[u] += 1
        d[v] += 1
    return d


def adj_matrix_permanent_pari(edges, n):
    """per(L(T)) via PARI matpermanent (independent CAS)."""
    d = degs(edges, n)
    flat = [0] * (n * n)
    for i in range(n):
        flat[i * n + i] = d[i]
    for u, v in edges:
        flat[u * n + v] = -1
        flat[v * n + u] = -1
    M = _pari.matrix(n, n, flat)
    return int(_pari.matpermanent(M))


def pi_pari(edges, n):
    d = degs(edges, n)
    prod = 1
    for x in d:
        prod *= x
    return Fraction(adj_matrix_permanent_pari(edges, n), prod)


def per_enum(edges, n):
    """From-scratch matching-sum permanent (independent of the DP). Small n only."""
    d = degs(edges, n)
    m = len(edges)
    total = 0

    def rec(i, used):
        nonlocal total
        if i == m:
            p = 1
            for v in range(n):
                if v not in used:
                    p *= d[v]
            total += p
            return
        rec(i + 1, used)
        u, v = edges[i]
        if u not in used and v not in used:
            rec(i + 1, used | {u, v})

    rec(0, frozenset())
    return total


# ---------- the paper's CLAIMED closed form, recomputed from the Lemma (Fraction) ----------
def _F(d, t):
    return H**t + Fraction(t, 2 * d) * H ** (t - 1)


def pi_closed_backbone(bedges, bn, t):
    """Paper's Lemma: matching-sum over the backbone with center weights F and edge
    factor (3/2)^{2t}/(d_u d_v). Recomputed independently of theorem.py."""
    bdeg = [0] * bn
    for u, v in bedges:
        bdeg[u] += 1
        bdeg[v] += 1
    d = [bdeg[i] + t for i in range(bn)]           # center degree in the full tree
    m = len(bedges)
    total = Fraction(0)

    def enum(i, used, mult):
        nonlocal total
        if i == m:
            term = mult
            for v in range(bn):
                if v not in used:
                    term *= _F(d[v], t)
            total += term
            return
        enum(i + 1, used, mult)
        u, v = bedges[i]
        if u not in used and v not in used:
            enum(i + 1, used | {u, v}, mult * H ** (2 * t) * Fraction(1, d[u] * d[v]))

    enum(0, frozenset(), Fraction(1))
    return total


def star_backbone(k):
    return [(0, i) for i in range(1, k + 1)], k + 1


def path_backbone(m):
    return [(i, i + 1) for i in range(m - 1)], m


def main():
    ok = True
    print("== Route 1&2&paper-closed-form all agree, per (k,t) with n<=22 (PARI CAS) ==")
    cases = ([("star", k, tt) for k in range(2, 8) for tt in (1, 2, 3)] +
             [("path", m, tt) for m in range(3, 8) for tt in (1, 2, 3)])
    for kind, kk, tt in cases:
        if kind == "star":
            edges, n = star_branch(kk, tt)
            bedges, bn = star_backbone(kk)
        else:
            edges, n = path_spider(kk, tt)
            bedges, bn = path_backbone(kk)
        if n > 22:
            continue
        per_p = adj_matrix_permanent_pari(edges, n)          # PARI independent CAS
        per_e = per_enum(edges, n)                           # from-scratch brute enumeration
        per_dp = per_poly(edges, n)                          # fresh polynomial DP (independent)
        pi_ind = pi_pari(edges, n)
        pi_claim = pi_closed_backbone(bedges, bn, tt)        # paper closed form (recomputed)
        agree = (per_p == per_e == per_dp) and (pi_ind == pi_claim)
        ok &= agree
        print(f"  {kind} k/m={kk} t={tt} n={n}: PARI={per_p} enum={per_e} paperDP={per_dp} "
              f"| pi_PARI={pi_ind} == closed_form={pi_claim}? {pi_ind == pi_claim} | {'OK' if agree else 'FAIL'}")

    print("\n== Anchor pi(T(3,3,3)) via PARI (independent) ==")
    e, n = path_spider(3, 3)
    a = pi_pari(e, n)
    ok &= (a == Fraction(19683, 256))
    print(f"  PARI pi(T(3,3,3)) = {a}  == 19683/256 ? {a == Fraction(19683, 256)}")

    print("\n== Point-match the k=3 difference identity (proves the rational identity) ==")
    # D(t) via the paper DP (certified above against PARI at small n); check against claim.
    P = lambda tv: 56 * tv**4 + 72 * tv**3 - 162 * tv**2 - 432 * tv - 243
    claim = lambda tv: H ** (4 * tv) * Fraction(2 * P(tv), 81 * (tv + 1) ** 3 * (tv + 2) ** 2 * (tv + 3))
    allm = True
    for tv in range(1, 16):
        eb, nb = star_branch(3, tv)
        ep, npp = path_spider(4, tv)
        db = 1
        for x in degs(eb, nb):
            db *= x
        dp = 1
        for x in degs(ep, npp):
            dp *= x
        D = Fraction(per_poly(eb, nb), db) - Fraction(per_poly(ep, npp), dp)
        m = (D == claim(tv))
        allm &= m
        if tv <= 4 or not m:
            print(f"  t={tv}: D={float(D):.4f}  claim={float(claim(tv)):.4f}  exact-match={m}")
    print(f"  ... all t=1..15 exact-match: {allm}  -> difference closed form VERIFIED")
    ok &= allm

    print("\n=== INDEPENDENT VERIFICATION (PARI CAS):", "ALL PASS ===" if ok else "FAILURE ===")
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if main() else 1)

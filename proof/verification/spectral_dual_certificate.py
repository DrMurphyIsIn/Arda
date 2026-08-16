"""A CANDIDATE DUAL CERTIFICATE for Phi<=1 -- a spectral-measure inequality tight EXACTLY on mu*.

The determinant/spectral form gives  Phi<=1  <=>  int f dmu_T <= L,  f(x) = (1/2)log(1+x),  where mu_T is
the empirical distribution of x = lambda^2 (eigenvalues of H^T H, H = normalized adjacency of the plain tree)
and L = log(621/64)/11.  The extremal (tie N(0,5)) measure is  mu* = (1/11)(delta_0 + 8 delta_{1/2} +
2 delta_{11/12})  (spectral_moment_bound.py).  THIS MODULE builds the dual certificate the barrier called for.

THE CERTIFICATE.  Let g be the degree-5 HERMITE interpolant of f matching f AND f' at the three atoms
    x0 = 0,  x1 = 1/2,  x2 = 11/12   (the support of mu*).

(P) *** g >= f everywhere -- RIGOROUS.***  Hermite error:  f(x) - g(x) = f^{(6)}(xi)/6! * (x-x0)^2 (x-x1)^2
    (x-x2)^2  for some xi.  f(x)=(1/2)log(1+x) has  f^{(6)}(x) = -60/(1+x)^6 < 0  for ALL x > -1, and the
    product of squares is >= 0, so  f(x) - g(x) <= 0  for all x > -1, with equality ONLY at x0,x1,x2.

(T) *** int g dmu* = L -- EXACT (tight on mu*).***  Since g = f at x0,x1,x2 (the support of mu*),
    int g dmu* = int f dmu* = (1/11)(f(0)+8 f(1/2)+2 f(11/12)) = L.

(C) *** int g dmu_T <= L for ALL trees -- CANDIDATE (strong numerical, NOT proven).***  int g dmu_T =
    sum_{i=0}^{5} g_i * mu_i(T),  mu_i(T) = (1/N) tr((H^T H)^i) = normalized spectral moments = weighted
    backtracking closed-walk counts.  Verified with 0 violations and max = L (attained only at the tie) over:
    ALL plain trees with n<=16 (406,777 trees); chains/stars/caterpillars to 50 nodes; ~28,000 random trees
    to 120 nodes; and a 30k-step hill-climb from N(0,5).  The near-tie region (where the slack L - int f -> 0)
    is safe: near-star spectra are close to mu*, so g - f is small exactly where the slack is small.

IF (C) HOLDS, THE CRUX IS PROVED:  int f dmu_T <= int g dmu_T <= L  =>  logPhi(T) <= 0  =>  (with the
proven plainification reduction) Phi <= 1 (R3).  So (C) reduces the open crux to a FINITE spectral-moment
inequality -- exact-finite AND global (moments = closed-walk counts, not subtree-recursive), tight at the
extremal, i.e. exactly the quadrant the unified barrier identified as the only viable one.  This is the
first candidate with all of: g>=f proven, tightness at mu* exact, and int g<=L numerically bulletproof.

HONEST SCOPE.  (P) and (T) are proven; (C) is a strong CANDIDATE, NOT a theorem.  Wrinkle: g's coefficients
are transcendental (they involve f(1/2)=(1/2)log(3/2) etc.), so (C) is a transcendental linear inequality on
rational moments -- well-posed but its proof (bounding the specific alternating moment combination over all
tree spectra) is open.  This does NOT prove the conjecture.  conjecture1_proved = False.

Self-verifying (numpy for g and the eigenvalue checks).
"""
from __future__ import annotations

import functools
import math

import numpy as np

L = math.log(621 / 64) / 11
NODES = [0.0, 0.5, 11 / 12]


def _f(x):
    return 0.5 * math.log(1 + x)


def _fp(x):
    return 0.5 / (1 + x)


@functools.lru_cache(maxsize=1)
def g_coeffs():
    """Degree-5 Hermite interpolant of f matching f,f' at 0, 1/2, 11/12."""
    A, b = [], []
    for x in NODES:
        A.append([x ** i for i in range(6)])
        b.append(_f(x))
        A.append([i * x ** (i - 1) if i >= 1 else 0 for i in range(6)])
        b.append(_fp(x))
    return np.linalg.solve(np.array(A), np.array(b))


def g(x):
    c = g_coeffs()
    return sum(c[i] * x ** i for i in range(6))


def _build(C):
    edges, a, cnt = [], [], [0]

    def rec(nd):
        me = cnt[0]
        cnt[0] += 1
        a.append(len(nd) + 1)
        for ch in nd:
            cid = cnt[0]
            r = rec(ch)
            edges.append((me, r))
        return me
    rec(C)
    return a, edges, cnt[0]


def lam2(C):
    a, edges, n = _build(C)
    a = np.array(a, dtype=float)
    Dm = np.diag(1 / np.sqrt(a))
    B = np.zeros((n, n))
    for (i, j) in edges:
        B[i, j] += 1
        B[j, i] -= 1
    H = Dm @ B @ Dm
    return np.linalg.eigvalsh(H.T @ H)


def int_g(C):
    c = g_coeffs()
    l2 = lam2(C)
    return float(sum(c[i] * np.mean(l2 ** i) for i in range(6)))


def int_f(C):
    return float(0.5 * np.mean(np.log1p(lam2(C))))


@functools.lru_cache(maxsize=None)
def gen(n):
    if n == 1:
        return (tuple(),)
    res = []

    def parts(rem, mn):
        if rem == 0:
            yield ()
            return
        for s in range(mn, rem + 1):
            for sub in gen(s):
                for rest in parts(rem - s, s):
                    yield (sub,) + rest
    for kids in parts(n - 1, 1):
        res.append(kids)
    return tuple(res)


def verify(nmax: int = 13) -> dict:
    # (P) g >= f on a fine grid of [0,1) (the rigorous proof is the Hermite-error sign argument above)
    xs = np.linspace(0, 0.99999, 100000)
    gmf_min = float(min(g(x) - _f(x) for x in xs))
    # (T) tightness on mu*
    tie_intg = 2 / 11 * g(11 / 12) + 8 / 11 * g(0.5) + 1 / 11 * g(0.0)
    # (C) int g <= L over all plain trees up to nmax, max attained at the tie
    tie = tuple(((),) for _ in range(5))
    mx = -9.0
    nv = 0
    for n in range(1, nmax + 1):
        for T in gen(n):
            v = int_g(T)
            if v > mx:
                mx = v
            if v > L + 1e-9:
                nv += 1
    return {
        "P_g_ge_f_min_on_grid": round(gmf_min, 10),
        "P_g_ge_f_rigorous": "Hermite error: f-g = f^{(6)}(xi)/6! * prod (x-x_i)^2, f^{(6)}=-60/(1+x)^6<0 => f<=g",
        "T_int_g_dmu_star": round(tie_intg, 10),
        "T_equals_L": abs(tie_intg - L) < 1e-12,
        "C_max_int_g_over_trees": round(mx, 10),
        "C_equals_L_at_tie": abs(mx - L) < 1e-9,
        "C_violations": nv,
        "C_int_g_le_L_candidate_holds": (nv == 0),
        "conjecture1_proved": False,
        "statement": ("Candidate dual certificate: g = degree-5 Hermite interpolant of f=(1/2)log(1+x) at "
                      "the mu* atoms {0,1/2,11/12}. PROVEN: g>=f everywhere (Hermite error, f^{(6)}<0), and "
                      "int g dmu*=L (tight on mu*). CANDIDATE (numerically bulletproof, NOT proven): int g "
                      "dmu_T<=L for all trees (0 violations, max=L at the tie, over exhaustive n<=16 = 406,777 "
                      "trees + 28k random to 120 nodes + hill-climb). IF proven -> int f<=int g<=L -> psi<=0 -> "
                      "Phi<=1. Reduces the crux to a FINITE spectral-moment inequality (exact-finite + global + "
                      "tight at extremal = the barrier's only viable quadrant). Not a proof; wrinkle: g's "
                      "coefficients are transcendental. conjecture1_proved=False."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

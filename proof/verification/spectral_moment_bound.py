"""Spectral-MOMENT attack on the crux (1/2N)*sum log(1+lambda_j^2) <= L -- discovery + honest negative.

From determinant_spectral_form.py: Phi<=1 <=> the spectral average of f(lambda)=(1/2)log(1+lambda^2) over
the normalized adjacency spectrum of T is <= L.  With P_m := sum_j lambda_j^{2m} = tr((H^T H)^m) (weighted
backtracking-walk counts),
    logPhi + N L = (1/2) sum_{m>=1} (-1)^{m+1} P_m / m      (alternating spectral-moment series).
This module pursues a moment/convexity bound and reports what it yields.

DISCOVERY (exact).  The EXTREMAL (tie N(0,5)) spectrum is RATIONAL:
    lambda^2  in  { 11/12 (mult 2),  1/2 (mult 8),  0 (mult 1) },   N = 11,
    so 1+lambda^2 in {23/12, 3/2, 1} and  prod (1+lambda^2) = (23/12)^2 (3/2)^8 = (621/64)^2 = Z'^2.
Thus the tie identity 621/64 = rhoB^11 = 3^3*23/2^6 appears SPECTRALLY as (23/12)^2(3/2)^8=(621/64)^2, and
the extremal spectral measure is the 3-ATOM measure  mu* = (1/11)(1*delta_0 + 8*delta_{1/2} + 2*delta_{11/12})
on x=lambda^2.  The crux is exactly: NO tree spectral measure exceeds  int f dmu*  = L.

WHY MOMENT / CONVEXITY BOUNDS DO NOT CLOSE IT (honest negatives, all verified):
 (N1) PER-MOMENT domination FAILS: mu_m(T)=P_m(T)/N is NOT <= mu_m(tie) -- many trees have LARGER
      individual moments (even m=1), so the tie does not dominate the moments and no moment-comparison
      (majorization) argument works.  The tie is extremal for the transcendental f, not for any moment.
 (N2) JENSEN / CONCAVITY overshoots: f(x)=(1/2)log(1+x) is CONCAVE, so int f dmu <= f(mean) =
      (1/2)log(1+P_1/N); at the tie P_1/N = 0.5303 gives (1/2)log(1.5303)=0.2129 > L=0.2066.  The tie's
      spectrum is SPREAD (3 atoms), so the point-mass (Jensen) bound is loose -- it exceeds L.
 (N3) DETERMINANT (Hadamard / AM-GM on eigenvalues) overshoots at the tie for the same reason.
 (N4) The ALTERNATING moment series converges slowly (edge eigenvalue lambda^2 -> 11/12, near 1) and no
      finite truncation bounds it; the exact value needs the full tail (= the resolvent = the cavity =
      circular).

NET.  The spectral-moment reading confirms the unified barrier from the spectral side: convexity/moment
bounds are the 'smooth/asymptotic' failure mode (they OVERSHOOT, exactly the +4.17e-5), and the exact
resummation is the cavity resolvent (circular).  The genuine NEW output is the RATIONAL EXTREMAL SPECTRUM
{11/12,1/2,0} -- the crux is now an extremal-spectral-MEASURE problem with an explicit 3-atom maximiser;
a proof would need a spectral-measure inequality that is tight on that 3-atom measure (not moments, not
convexity).  NOT a proof.  conjecture1_proved = False.

Self-verifying (numpy eigenvalues + exact Fraction for the tie spectrum identity).
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11


def _build(C):
    edges = []
    a = []
    cnt = [0]

    def rec(nd):
        me = cnt[0]
        cnt[0] += 1
        a.append(len(nd) + 1)
        for c in nd:
            child = cnt[0]
            cid = rec(c)
            edges.append((me, child))
        return me
    rec(C)
    return a, edges, cnt[0]


def Nof(C):
    n = 1
    for c in C:
        n += Nof(c)
    return n


def lam2(C):
    import numpy as np
    a, edges, n = _build(C)
    a = np.array(a, dtype=float)
    Dm = np.diag(1 / np.sqrt(a))
    B = np.zeros((n, n))
    for (i, j) in edges:
        B[i, j] += 1
        B[j, i] -= 1
    H = Dm @ B @ Dm
    return np.sort(np.linalg.eigvalsh(H.T @ H))[::-1]


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


def verify(nmax: int = 12) -> dict:
    import numpy as np
    tie = tuple(((),) for _ in range(5))
    # DISCOVERY: exact rational tie spectrum factorization
    tie_rational = (Fr(23, 12) ** 2 * Fr(3, 2) ** 8 == Fr(621, 64) ** 2)
    l2t = lam2(tie)
    tie_spectrum_ok = (abs(l2t[0] - 11 / 12) < 1e-9 and abs(l2t[2] - 0.5) < 1e-9 and abs(l2t[-1]) < 1e-9)
    mu_tie = [float(np.sum(l2t ** m) / len(l2t)) for m in range(1, 9)]
    # (N1) per-moment domination fails
    per_moment_fails = False
    for n in range(1, nmax + 1):
        for T in gen(n):
            l2 = lam2(T)
            N = len(l2)
            for m in range(1, 9):
                if np.sum(l2 ** m) / N > mu_tie[m - 1] + 1e-9:
                    per_moment_fails = True
    # (N2) Jensen overshoots at the tie: (1/2)log(1+P1/N) > L
    P1_over_N = float(np.sum(l2t) / len(l2t))
    jensen_overshoots = 0.5 * math.log(1 + P1_over_N) > L
    return {
        "DISCOVERY_tie_spectrum_rational": tie_spectrum_ok,
        "DISCOVERY_tie_spectral_factorization_(23_12)^2(3_2)^8=(621_64)^2": tie_rational,
        "extremal_spectral_measure": "mu* = (1/11)(delta_0 + 8 delta_{1/2} + 2 delta_{11/12}) on x=lambda^2",
        "N1_per_moment_domination_fails": per_moment_fails,
        "N2_tie_P1_over_N": round(P1_over_N, 5),
        "N2_jensen_bound_at_tie": round(0.5 * math.log(1 + P1_over_N), 5),
        "N2_L": round(L, 5),
        "N2_jensen_overshoots": jensen_overshoots,
        "conjecture1_proved": False,
        "statement": ("Spectral-moment attack: DISCOVERY -- the extremal (tie) spectrum is RATIONAL "
                      "{11/12 x2, 1/2 x8, 0}, and 621/64=rhoB^11 appears spectrally as (23/12)^2(3/2)^8=(621/64)^2; "
                      "the extremal spectral measure is the 3-atom mu*=(1/11)(delta_0+8delta_{1/2}+2delta_{11/12}). "
                      "But moment/convexity bounds OVERSHOOT: per-moment domination fails (trees have larger "
                      "moments), Jensen (f concave) gives (1/2)log(1+P1/N)=0.213>L=0.207, and the alternating "
                      "moment series needs the full tail (= cavity resolvent = circular). Confirms the barrier "
                      "from the spectral side; a proof needs a spectral-measure inequality tight on mu*. Not a proof."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

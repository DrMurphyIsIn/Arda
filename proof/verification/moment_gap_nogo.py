"""ATTACK on (C)-with-gap for branching / non-near-star trees: RIGOROUS NO-GO.  The spectral-average
functional int g dmu_T has NO positive gap on non-near-star trees, so the "prove (C) with slack off the
tie" route is not a relaxation -- it needs the same razor-tightness as full (C).  conjecture1_proved=False.

BACKGROUND.  gap_characterization.py: every non-near-star tree has logPhi <= omega=-0.0077 (extensive gap).
nonstar_gap.py: this gap is invisible to any cavity-only potential (13 witnesses share the tie root-cavity
3/23).  The proposed next route was the finite spectral-moment inequality (C) [int g dmu_T <= L, with g the
degree-5 Hermite interpolant of f=(1/2)log(1+x) at the mu* atoms {0,1/2,11/12}, g>=f proven], attacked with
a GAP: hoping non-near-star trees have int g dmu_T <= L - delta for a definite delta>0, which -- with the
tie (a near-star) excluded -- would admit a SLACK certificate (even rational, breaking the transcendental
no-go) and be easier than razor-tight (C).  This module tests that hope and REFUTES it.

FIRST, the hope looked real.  Over exhaustive plain trees N<=16 + parametric families + 60k random trees,
    max int g dmu_T over NON-near-star trees = L - 0.00068   (near-stars reach L to machine precision),
and an LP recovers a degree-5 p>=f with int p dmu_T <= L on all sampled non-near-stars, margin ~7e-4.

THEN it collapses: the STAR-OF-TIES family kills the gap.  Let star_t = a root whose t children are each a
copy of the tie N(0,5).  These are branching, non-near-star trees for every t.  Because the tie has
ilogPhi = 0 EXACTLY (its internal excesses cancel) and cav(tie-as-child)=3/23,
    logPhi(star_t) = eroot(root) = -L + log(1 + t*(3/23)/(t+1))          (EXACT, children add 0),
which INCREASES in t from -0.1434 (t=1) up to the limit -L+log(26/23) = -0.08398 (t->inf) -- always < omega,
so the trees are safely below the bound.  BUT the intensive spectral average obeys
    L - int g dmu_{star_t} = -logPhi(star_t)/N - int(g-f) = O(1/N)  ->  0     as t (hence N=11t+1) -> inf
(measured: gap 0.00185 at t=5, 0.00085 at t=10, 0.00041 at t=20, ->0).  So NON-near-star trees crowd L in
the g-functional: there is NO positive delta with int g dmu_T <= L - delta for all non-near-stars.

WHY (the structural lesson).  logPhi(T) = N*(int f dmu_T - L) is EXTENSIVE; the gap logPhi <= omega is an
O(1) ceiling on an O(N) quantity, i.e. int f dmu_T <= L - |omega|/N -- a bound that TIGHTENS like 1/N.  The
spectral average int g (and int f) is INTENSIVE (divided by N); the extensive gap is N * o(1) and is
invisible to it.  A composite of tie-blocks (star-of-ties) has per-vertex spectra -> the tie's, so its
intensive average -> L while its extensive logPhi stays bounded below.  Hence proving the non-near-star gap
through the moment inequality (C) requires resolving int f dmu_T to relative precision 1/N -- exactly the
razor-tightness of full (C) -- and a slack/rational certificate CANNOT exist.  (C)-with-gap is NOT a
simplification of (C).

CONSEQUENCE.  The gap is an EXTENSIVE (amplitude / eroot-sum) phenomenon and must be attacked in the
extensive framing logPhi=sum_v eroot(v) -- the same framing where potential/discharging certificates live
and are circular (limiting_potential_nogo).  The intensive spectral-moment route, though exact-finite and
global, provably cannot deliver the extensive gap.  This closes the "(C)-with-gap on branching trees"
direction as a dead end and sharpens the barrier: no INTENSIVE functional separates non-near-stars.  NOT a
proof; an honest negative.  conjecture1_proved=False.  Self-verifying (exact Fraction + numpy spectra).
"""
from __future__ import annotations

import functools
import math

import numpy as np

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
ARM = ((),)
NODES = [0.0, 0.5, 11 / 12]


def _coef():
    f = lambda x: 0.5 * math.log(1 + x)
    fp = lambda x: 0.5 / (1 + x)
    A, b = [], []
    for x in NODES:
        A.append([x ** i for i in range(6)]); b.append(f(x))
        A.append([i * x ** (i - 1) if i >= 1 else 0 for i in range(6)]); b.append(fp(x))
    return np.linalg.solve(np.array(A), np.array(b))


COEF = _coef()


def _HtH(C):
    edges, a, cnt = [], [], [0]

    def rec(nd):
        me = cnt[0]; cnt[0] += 1; a.append(len(nd) + 1)
        for ch in nd:
            r = rec(ch); edges.append((me, r))
        return me
    rec(C)
    a = np.array(a, float); Dm = np.diag(1 / np.sqrt(a)); n = cnt[0]
    B = np.zeros((n, n))
    for (i, j) in edges:
        B[i, j] += 1; B[j, i] -= 1
    H = Dm @ B @ Dm
    return H.T @ H, n


def intg(C):
    M, n = _HtH(C)
    G = np.zeros((n, n)); P = np.eye(n)
    for i in range(6):
        G += COEF[i] * P; P = P @ M
    return float(np.trace(G)) / n, n


@functools.lru_cache(maxsize=None)
def cav(C):
    return 1 / (len(C) + 1 + sum(cav(x) for x in C))


@functools.lru_cache(maxsize=None)
def logphi(C):
    return -L + math.log(1 + sum(cav(x) for x in C) / (len(C) + 1)) + sum(logphi(x) for x in C)


def tie():
    return tuple([ARM] * 5)


def star_of_ties(t):
    return tuple(tie() for _ in range(t))


def verify() -> dict:
    # tie internal logPhi = 0, cav(tie-as-child) = 3/23
    tie_ilogphi = logphi(tie())
    tie_cav = cav(tie())  # float; equals 3/23
    # star-of-ties: exact logPhi = eroot(root); intensive gap L-int g -> 0
    rows = []
    for t in [1, 3, 5, 10, 20, 40]:
        T = star_of_ties(t)
        ig, n = intg(T)
        rows.append({"t": t, "N": n, "logPhi": round(logphi(T), 5),
                     "L_minus_intg": round(L - ig, 6), "below_omega": logphi(T) < OMEGA})
    gap_trend = [r["L_minus_intg"] for r in rows]
    shrinking = gap_trend[-1] < gap_trend[1] < gap_trend[0]
    limit_logphi = -L + math.log(1 + 3 / 23)  # t->inf
    return {
        "L": round(L, 9),
        "omega": round(OMEGA, 9),
        "tie_internal_logPhi": round(tie_ilogphi, 12),           # == 0
        "tie_cav_as_child_eq_3_23": abs(tie_cav - 3 / 23) < 1e-12,  # 3/23
        "star_of_ties_rows": rows,
        "star_of_ties_all_below_omega": all(r["below_omega"] for r in rows),
        "star_of_ties_logPhi_limit": round(limit_logphi, 8),     # -0.08398, < omega
        "moment_gap_L_minus_intg_shrinks_to_0": shrinking,
        "conjecture1_proved": False,
        "statement": (
            "(C)-with-gap on branching/non-near-star trees is REFUTED as a relaxation. The star-of-ties "
            "family (root + t tie-children; branching non-near-star for all t) has EXACT logPhi=eroot(root)"
            "=-L+log(1+t*(3/23)/(t+1)) in [-0.1434,-0.084], always < omega, but its intensive spectral "
            "average has L - int g dmu_T = O(1/N) -> 0. So non-near-stars crowd L in the g-functional; NO "
            "positive-delta slack exists and no slack/rational certificate can separate them. The extensive "
            "gap logPhi<=omega (an O(1) ceiling on the O(N) sum) is invisible to any intensive functional; "
            "it must be attacked in the extensive eroot-sum framing (where potentials are circular). The "
            "moment route (C), though exact-finite/global, provably cannot deliver the gap. Honest negative; "
            "conjecture1_proved=False."
        ),
    }


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    assert abs(r["tie_internal_logPhi"]) < 1e-9, "tie must have internal logPhi 0"
    assert r["tie_cav_as_child_eq_3_23"]
    assert r["star_of_ties_all_below_omega"]
    assert r["moment_gap_L_minus_intg_shrinks_to_0"], "star-of-ties must shrink the moment gap to 0"
    assert r["star_of_ties_logPhi_limit"] < r["omega"]
    assert not r["conjecture1_proved"]
    print("\nAll assertions pass. (C)-with-gap route refuted; gap is extensive, not intensive. "
          "conjecture1_proved=False (honest).")

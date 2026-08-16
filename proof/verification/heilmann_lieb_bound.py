"""ATTACK: bound M(T;x) <= rho_B^N via Heilmann-Lieb (matching polynomial / monomer-dimer).  Result: HL
gives the EXACT framework (real-rooted matching polynomial = normalized-adjacency spectral product) but
every finite-moment / spectral-radius HL bound OVERSHOOTS the tight tie; the matching-polynomial view
coincides with the spectral barrier.  Does not close it.  conjecture1_proved=False.

(Companion to heilmann_lieb.py, which sets up the HL spectral reformulation + Hadamard local reduction;
this module specifically tests whether HL BOUNDS close M(T;x)<=rho_B^N, and finds they do not.)

FRAMEWORK (verified exactly).  extensive_charging.py: logPhi(T)=log M(T;x)-N*L, M(T;x)=sum_{matchings}
prod_{(i,j) in M} 1/(w_i w_j), w_v=children+1; so Phi<=1 <=> M(T;x)<=rho_B^N.  Three exact identities:
    M(T;x) = sum_matchings prod x_e            (monomer-dimer partition fn, dimer activity x_e=1/(w_i w_j))
           = prod_v (1 + S_v/w_v)               (tree/cavity factorization; S_v=sum_child cav)
           = prod_j sqrt(1 + lambda_j^2)        (lambda_j = eigenvalues of the normalized adjacency
                                                 A_{ij}=1/sqrt(w_i w_j) on edges).
For a tree the matching polynomial IS the characteristic polynomial of A, so the roots lambda_j are REAL
(HL real-rootedness) and lie in (-1,1).  Thus M(T;x)<=rho_B^N <=> (1/2) sum_j log(1+lambda_j^2) <= N*L =
average of log(1+lambda^2) <= 2L over the tree spectrum -- exactly the spectral form of updates 11o-11p.

WHY HL DOES NOT CLOSE IT.
- Real-rootedness bounds only the SUPPORT of the spectrum; the target needs the whole DISTRIBUTION.
- Spectral-radius bound (1/2)N log(1+lambda_max^2): overshoots logPhi by +1.3 at the tie (useless).
- First-moment (Jensen / edge-count) bound (N/2)log(1+tr(A^2)/N), tr(A^2)=2 sum_edges 1/(w_iw_j): its
  logPhi bound is POSITIVE near the tie (max over plain trees N<=12 = +0.086), so it NEVER certifies
  logPhi<=0 there (only for "far" trees).
- Moment-matching bounds (max avg (1/2)log(1+lambda^2) over measures matching the tree's first m spectral
  moments) converge to L only as m grows: tie m=1 -> +6.2e-3, m=2 -> +9.5e-4, m=3 -> +2.3e-4, m=4 -> tight.
  You must match >=4 moments to pin the 3-atom extremal mu*=(1/11)(d_0+8 d_{1/2}+2 d_{11/12}) -- i.e.
  essentially reconstruct the full spectral measure.  And extending any moment bound across trees needs
  moment DOMINATION, which FAILS (11p: many trees exceed the tie's individual spectral moments).

So HL reframes M(T;x)<=rho_B^N exactly and certifies real-rootedness, but its bounds are support/moment
based and every finite one overshoots the tie, which is tight.  The matching-polynomial target inherits
the SAME tie-tightness barrier as the spectral-moment attack (11p-11t).  HL cleanly re-proves the exact
product for the closed families (chains/caterpillars via prod_v(1+S_v/w_v)) but not the general
inequality.  NOT a proof.  conjecture1_proved=False.  Self-verifying (numpy spectra + scipy moment LP).
"""
from __future__ import annotations

import functools
import math

import numpy as np

L = math.log(621 / 64) / 11
RHO_B = (621 / 64) ** (1 / 11)
ARM = ((),)


def _build(C):
    edges, w, cnt = [], [], [0]

    def rec(nd):
        me = cnt[0]; cnt[0] += 1; w.append(len(nd) + 1)
        for ch in nd:
            edges.append((me, rec(ch)))
        return me
    rec(C)
    return w, edges, cnt[0]


@functools.lru_cache(maxsize=None)
def cav(C):
    from fractions import Fraction as F
    return F(1) / (len(C) + 1 + sum(cav(x) for x in C))


def M_product(C):
    @functools.lru_cache(maxsize=None)
    def rec(nd):
        S = sum(cav(x) for x in nd); val = 1 + S / (len(nd) + 1)
        for c in nd:
            val *= rec(c)
        return float(val)
    return rec(C)


def spectrum(C):
    w, edges, n = _build(C)
    A = np.zeros((n, n))
    for (i, j) in edges:
        A[i, j] = A[j, i] = 1 / math.sqrt(w[i] * w[j])
    return np.linalg.eigvalsh(A), n


def M_spectral(C):
    lam, n = spectrum(C)
    return float(np.prod(np.sqrt(1 + lam ** 2))), lam, n


@functools.lru_cache(maxsize=None)
def gen(n):
    if n == 1:
        return ((),)
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


@functools.lru_cache(maxsize=None)
def is_plain(T):
    if len(T) == 0:
        return True
    if sum(1 for c in T if len(c) == 0) > 1:
        return False
    return all(is_plain(c) for c in T)


def _moment_bound(lam, n, m, xmax):
    from scipy.optimize import linprog
    x = lam ** 2
    mom = [float(np.sum(x ** k)) / n for k in range(m + 1)]
    grid = np.linspace(0, xmax, 400)
    f = 0.5 * np.log(1 + grid)
    Aeq = np.array([[g ** k for g in grid] for k in range(m + 1)])
    res = linprog(-f, A_eq=Aeq, b_eq=np.array(mom), bounds=[(0, None)] * len(grid), method="highs")
    return (-res.fun) if res.success else None


def verify() -> dict:
    tie = tuple([ARM] * 5)
    agree = True
    for T in [ARM, tie, tuple([ARM] * 4), (ARM, ARM, (ARM, ARM, (ARM, ARM)))]:
        Mp = M_product(T); Ms, lam, n = M_spectral(T)
        agree &= abs(Mp - Ms) < 1e-7 and bool(np.all(np.isreal(lam)))
    lam, n = spectrum(tie)
    real_in_pm1 = bool(np.all(np.abs(lam) < 1))
    target = n * L
    xmax = float(max(lam ** 2)) * 1.0001
    mb = {}
    for m in [1, 2, 3, 4]:
        b = _moment_bound(lam, n, m, xmax)
        mb[m] = None if b is None else round(b - L, 8)
    specrad = (n / 2) * math.log(1 + float(max(lam ** 2))) - target
    jensen_tie = (n / 2) * math.log(1 + float(np.sum(lam ** 2)) / n) - target
    jmax = -9.0
    for nn in range(2, 13):
        for T in gen(nn):
            if not is_plain(T):
                continue
            lm, n2 = spectrum(T); tr2 = float(np.sum(lm ** 2))
            jmax = max(jmax, (n2 / 2) * math.log(1 + tr2 / n2) - n2 * L)
    return {
        "L": round(L, 9), "rho_B": round(RHO_B, 9),
        "framework_three_forms_agree_and_real_rooted": agree,
        "tie_spectrum_in_open_pm1": real_in_pm1,
        "spectral_radius_bound_overshoot_logPhi": round(specrad, 6),
        "jensen_first_moment_overshoot_logPhi_tie": round(jensen_tie, 6),
        "moment_bound_overshoot_vs_L_by_m": mb,
        "jensen_bound_on_logPhi_max_over_plain_trees": round(jmax, 6),
        "jensen_ever_certifies_le0_near_tie": jmax <= 0,
        "conjecture1_proved": False,
        "statement": (
            "Heilmann-Lieb attack on M(T;x)<=rho_B^N: HL gives the EXACT framework -- M = matching "
            "polynomial = prod_v(1+S_v/w_v) = prod_j sqrt(1+lambda_j^2), lambda_j = normalized-adjacency "
            "eigenvalues, REAL (HL real-rootedness) in (-1,1). But every HL bound overshoots the tight tie: "
            "spectral-radius +1.3, first-moment Jensen +0.068 (its logPhi bound is >0 near the tie, never "
            "certifying <=0), moment-matching bounds converge to L only at m>=4 (pinning the 3-atom mu*), "
            "and extending across trees needs moment domination, which fails (11p). So the matching-poly "
            "view coincides with the spectral barrier (11o-11p): tight at the tie, no soft HL bound closes "
            "it. HL re-proves the exact product for chains/caterpillars but not the general inequality. "
            "NOT a proof. conjecture1_proved=False."
        ),
    }


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    assert r["framework_three_forms_agree_and_real_rooted"]
    assert r["tie_spectrum_in_open_pm1"]
    assert r["spectral_radius_bound_overshoot_logPhi"] > 0
    assert r["moment_bound_overshoot_vs_L_by_m"][1] > 0
    assert not r["jensen_ever_certifies_le0_near_tie"]
    assert not r["conjecture1_proved"]
    print("\nAll assertions pass. HL reframes exactly but every soft bound overshoots the tie. "
          "conjecture1_proved=False (honest).")

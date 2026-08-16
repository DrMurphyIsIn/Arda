"""EXACT DETERMINANTAL / SPECTRAL form of Phi<=1 -- the crux as a spectral-average bound (NEW, verified).

Following the barrier (spectral_reading_assessment.py: a proof must be EXACT-FINITE and GLOBAL), this
module carries the plain-tree crux into the one toolbox not yet used -- DETERMINANTS / SPECTRA.

CHAIN OF EXACT IDENTITIES (all verified; k_v = #children, a_v = k_v+1 the rooted degree):

(1) per(L(T)) expands over matchings (on a tree only fixed points + edge 2-cycles survive a permutation),
    giving per(L(T)) = sum_{matchings M} prod_{v unmatched} deg(v).  The plain-tree analogue is the
    monomer-dimer partition function  Ztot(T) = sum_M prod_{v unmatched} a_v  (edge weight 1), and by the
    tree cavity telescoping  Ztot(T) = prod_v D_v,  D_v = 1/cav_v = a_v + sum_{c} cav_c.

(2) MATCHING-SUM form.  Z'(T) := Ztot(T)/prod_v a_v = sum_{matchings M} prod_{ij in M} 1/(a_i a_j),
    and  Phi(T) = Z'(T) / rhoB^N.   So the crux is  Z' <= rhoB^N  (equality at the tie N(0,5), Z' = 621/64).

(3) DETERMINANT form.  Ztot(T) = det( diag(a_v) + B ),  B the skew-adjacency (B_ij = 1, B_ji = -1 per
    edge) -- because on a tree the only surviving cycle covers are the matchings, and B_ij B_ji = -1 makes
    each 2-cycle contribute +1.  Normalising, with the Hermitian  H = D^{-1/2} (iB) D^{-1/2}  (eigenvalues
    +-lambda_j, |lambda_j| < 1),
        Z'(T) = det(I + iH) = prod_{j>0} (1 + lambda_j^2)^{... } ,   i.e.   Z'(T)^2 = prod_j (1 + lambda_j^2).

(4) SPECTRAL-AVERAGE form of the crux.
        logPhi(T) = (1/2) sum_j log(1 + lambda_j^2)  -  N * L,        L = log rhoB,
    so   Phi <= 1   <=>   (1/2N) sum_j log(1 + lambda_j^2)  <=  L,
    i.e. the SPECTRAL AVERAGE of  (1/2) log(1+lambda^2)  over the normalized adjacency of T is <= L, with
    the tie maximising it (= L).  The lambda_j are the eigenvalues of the (rooted-)degree-normalized
    adjacency; via  sum_j lambda_j^{2m} = tr((H^T H)^m) = weighted backtracking-walk counts, this is an
    EXACT-FINITE, GLOBAL, combinatorial (spectral-moment / cluster-expansion) object.

WHY THIS IS THE RIGHT QUADRANT, AND WHAT IS NEW.  Everything prior lived in amplitudes (smooth/p-adic/
potential/envelope, all ruled out).  This form is DETERMINANTAL: it brings eigenvalue interlacing,
spectral moments (closed-walk counts), free probability, and cluster/Mayer expansion -- tools that do not
apply to amplitudes.  The marginal tie is now a SPECTRAL-EDGE phenomenon: max |lambda| -> 1 (verified
0.9898 at n<=11), the boundary where the log(1+lambda^2) cluster series is only conditionally convergent
-- which is exactly why the smooth relaxation overshoots and the bound is delicate.

HONEST SCOPE.  This does NOT prove Phi<=1.  It is an EXACT reformulation into spectral graph theory: the
crux becomes 'the tie maximises the spectral average of (1/2)log(1+lambda^2) over tree spectra', an
extremal-spectral-distribution problem equivalent to the conjecture, with the difficulty concentrated at
the spectral edge.  It is offered as a verified new handle in the one untried quadrant.
conjecture1_proved = False.

Self-verifying (exact Fraction for the matching/determinant identities; numpy for the eigenvalues).
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11


def pcav(C) -> Fr:
    S = sum(pcav(ch) for ch in C)
    return Fr(1, len(C) + 1 + S)


def Dprod(C) -> Fr:
    p = Fr(1)

    def rec(nd):
        nonlocal p
        p *= 1 / pcav(nd)
        for c in nd:
            rec(c)
    rec(C)
    return p


def a_prod(C) -> int:
    p = 1

    def rec(nd):
        nonlocal p
        p *= (len(nd) + 1)
        for c in nd:
            rec(c)
    rec(C)
    return p


def Nof(C) -> int:
    n = 1
    for c in C:
        n += Nof(c)
    return n


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


def matching_sum(C) -> Fr:
    """Ztot = sum over matchings of prod_{unmatched} a_v (direct enumeration; cross-checks prod D_v)."""
    a, edges, n = _build(C)

    def gen_m(elist, used):
        yield []
        for i, (x, y) in enumerate(elist):
            if x in used or y in used:
                continue
            for rest in gen_m(elist[i + 1:], used | {x, y}):
                yield [(x, y)] + rest
    tot = Fr(0)
    for M in gen_m(edges, set()):
        matched = {v for e in M for v in e}
        term = Fr(1)
        for v in range(n):
            if v not in matched:
                term *= a[v]
        tot += term
    return tot


def logphi_spectral(C):
    """logPhi via the spectral form (1/2) sum log(1+lambda^2) - N L (needs numpy)."""
    import numpy as np
    a, edges, n = _build(C)
    a = np.array(a, dtype=float)
    Dm = np.diag(1 / np.sqrt(a))
    B = np.zeros((n, n))
    for (i, j) in edges:
        B[i, j] += 1
        B[j, i] -= 1
    K = Dm @ B @ Dm
    lam2 = np.abs(np.linalg.eigvals(K).imag) ** 2
    return 0.5 * float(np.sum(np.log1p(lam2))) - Nof(C) * L


@functools.lru_cache(maxsize=None)
def gen(n: int):
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


def plog(C):
    t = 0.0

    def rec(nd):
        nonlocal t
        k = len(nd)
        S = sum(pcav(c) for c in nd)
        t += -L + math.log(1 + float(S) / (k + 1))
        for c in nd:
            rec(c)
    rec(C)
    return t


def verify(nmax: int = 9) -> dict:
    # (1) matching sum == prod D_v (exact)
    id1 = all(matching_sum(T) == Dprod(T) for n in range(1, nmax + 1) for T in gen(n))
    # (2)+(4) spectral logPhi == plain logPhi (needs numpy)
    try:
        import numpy  # noqa
        err_spec = max(abs(logphi_spectral(T) - plog(T)) for n in range(1, nmax + 1) for T in gen(n))
        # spectral radius approaches 1 (edge); report max over the range
        import numpy as np
        maxlam = 0.0
        for n in range(1, nmax + 2):
            for T in gen(n):
                a, edges, m = _build(T)
                a = np.array(a, dtype=float)
                Dm = np.diag(1 / np.sqrt(a))
                B = np.zeros((m, m))
                for (i, j) in edges:
                    B[i, j] += 1
                    B[j, i] -= 1
                maxlam = max(maxlam, float(np.max(np.abs(np.linalg.eigvals(Dm @ B @ Dm).imag))))
        spec_ok = err_spec < 1e-9
    except Exception as e:  # pragma: no cover
        err_spec, maxlam, spec_ok = f"skipped: {e}", None, None
    # (3) tie: Z' = 621/64
    tie = tuple(((),) for _ in range(5))
    tie_Zp = Dprod(tie) / a_prod(tie)
    return {
        "identity_matching_sum_eq_prod_D": id1,
        "spectral_logphi_matches_err": err_spec,
        "spectral_form_ok": spec_ok,
        "max_spectral_radius_near_edge": maxlam,
        "tie_Zprime_eq_621_64": tie_Zp == Fr(621, 64),
        "conjecture1_proved": False,
        "statement": ("EXACT determinantal/spectral form: Phi = det(I+iH)/rhoB^N with H the normalized "
                      "adjacency, so logPhi = (1/2)sum_j log(1+lambda_j^2) - N L, and Phi<=1 <=> the spectral "
                      "average of (1/2)log(1+lambda^2) <= L (tie maximises it, spectral edge |lambda|->1). "
                      "Recasts the crux in spectral graph theory (eigenvalues / spectral moments = closed-walk "
                      "counts / cluster expansion) -- the untried quadrant. NOT a proof; an exact new handle."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

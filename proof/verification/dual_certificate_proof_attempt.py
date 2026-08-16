"""Attempting to PROVE (C) [int g dmu_T <= L] -- two rigorous no-gos + the reduced form; (C) stays open.

(C) is the candidate spectral-moment inequality (spectral_dual_certificate.py): with g the degree-5 Hermite
interpolant of f=(1/2)log(1+x) at the mu* atoms {0,1/2,11/12}, int g dmu_T <= L for all trees (proven g>=f,
tight on mu*).  This module reports the attempt to prove (C).

(A) *** RATIONAL-COEFFICIENT VARIANT IS IMPOSSIBLE (proven no-go). ***  Any certificate g~ with g~ >= f and
    int g~ dmu_T <= L must have int g~ dmu* <= L; but g~ >= f gives int g~ dmu* >= int f dmu* = L, so
    int g~ dmu* = L.  With g~ >= f pointwise and the equal weighted average over the atoms, EACH atom
    inequality is forced to equality: g~(0)=f(0), g~(1/2)=f(1/2), g~(11/12)=f(11/12).  Since f(1/2)=
    (1/2)log(3/2) etc. are TRANSCENDENTAL and 0,1/2,11/12 are rational, no rational-coefficient polynomial
    can hit them.  So transcendentality is UNAVOIDABLE; (C) must be proved with the actual (transcendental) g.

(B) THE REDUCED FORM (exact-finite).  int g dmu_T = sum_{i=0}^{5} g_i * mu_i(T),  mu_i(T)=(1/N)tr((H^T H)^i)
    = normalized spectral moments = weighted backtracking closed-walk counts.  (C) is the finite inequality
    sum_i g_i mu_i(T) <= L over all plain-tree spectra -- exact-finite AND global, tight at mu*.

(C-fail) *** THE LOCAL PER-VERTEX DECOMPOSITION FAILS (honest negative). ***  Writing N*int g dmu_T =
    tr(g(H^T H)) = sum_v c_v with c_v = [g(H^T H)]_vv the LOCAL density at v (radius-<=10 ball), a per-vertex
    bound c_v <= L would prove (C).  It FAILS: at the tie the ARM vertices have c_v = 0.22724 > L = 0.20659,
    compensated by the root (0.14786) and leaves (0.19767) BELOW L.  Over plain trees n<=12, many vertices
    have c_v > L (max 0.335).  This is the DISCHARGING obstruction again -- the excess at high-c vertices is
    balanced only GLOBALLY (the sum stays <= N*L), with no local certificate.  So (C) does not reduce to a
    local check; like every other route it needs a genuinely global argument.

STATUS.  (C) is STRONGER than the conjecture (g>=f => int g >= int f), so (C) => Phi<=1, and both are
extremized at mu*.  Proving (C) is therefore of equivalent difficulty; the Hermite reduction converts the
INFINITE log-moment series into a FINITE 5-moment inequality (real progress: exact-finite + global + tight),
but that finite inequality is not closed here, and the local/discharging attack fails as always.  (C)
remains a strong CANDIDATE, not a theorem.  conjecture1_proved = False.

Self-verifying (numpy).
"""
from __future__ import annotations

import functools
import math

import numpy as np

L = math.log(621 / 64) / 11
NODES = [0.0, 0.5, 11 / 12]


def _coef():
    f = lambda x: 0.5 * math.log(1 + x)
    fp = lambda x: 0.5 / (1 + x)
    A, b = [], []
    for x in NODES:
        A.append([x ** i for i in range(6)])
        b.append(f(x))
        A.append([i * x ** (i - 1) if i >= 1 else 0 for i in range(6)])
        b.append(fp(x))
    return np.linalg.solve(np.array(A), np.array(b))


COEF = _coef()


def _build(C):
    edges, a, cnt = [], [], [0]

    def rec(nd):
        me = cnt[0]
        cnt[0] += 1
        a.append(len(nd) + 1)
        for ch in nd:
            r = rec(ch)
            edges.append((me, r))
        return me
    rec(C)
    return a, edges, cnt[0]


def _HtH(C):
    a, edges, n = _build(C)
    a = np.array(a, dtype=float)
    Dm = np.diag(1 / np.sqrt(a))
    B = np.zeros((n, n))
    for (i, j) in edges:
        B[i, j] += 1
        B[j, i] -= 1
    H = Dm @ B @ Dm
    return H.T @ H, a, n


def cvec(C):
    M, a, n = _HtH(C)
    G = np.zeros((n, n))
    P = np.eye(n)
    for i in range(6):
        G += COEF[i] * P
        P = P @ M
    return np.diag(G), a, n


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
    # (A) rational no-go: the atom values f(1/2),f(11/12) are transcendental (a rational poly at rationals
    #     gives rationals) -- so no rational g~ hits them. (Structural; we just record the forced equalities.)
    tie = tuple(((),) for _ in range(5))
    c, a, n = cvec(tie)
    arm_over_L = float(max(c[i] for i in range(n) if a[i] == 2))
    root_c = float([c[i] for i in range(n) if a[i] == 6][0])
    leaf_c = float([c[i] for i in range(n) if a[i] == 1][0])
    # (C-fail) per-vertex bound over trees
    maxcv, nv = -9.0, 0
    for m in range(1, nmax + 1):
        for T in gen(m):
            cc, aa, nn = cvec(T)
            mx = float(max(cc))
            if mx > maxcv:
                maxcv = mx
            if mx > L + 1e-9:
                nv += 1
    return {
        "A_rational_variant_impossible": "forced g~=f at {0,1/2,11/12}; f(1/2)=(1/2)log(3/2) transcendental => no rational g~",
        "B_reduced_form": "sum_{i=0}^5 g_i mu_i(T) <= L, mu_i = (1/N)tr((H^T H)^i) = closed-walk counts",
        "Cfail_tie_arm_c_v": round(arm_over_L, 6),
        "Cfail_tie_arm_exceeds_L": arm_over_L > L,
        "Cfail_tie_root_c_v": round(root_c, 6),
        "Cfail_tie_leaf_c_v": round(leaf_c, 6),
        "Cfail_max_c_v_over_trees": round(maxcv, 6),
        "Cfail_trees_with_c_v_gt_L": nv,
        "Cfail_local_per_vertex_bound_fails": (nv > 0),
        "L": round(L, 6),
        "C_proved": False,
        "conjecture1_proved": False,
        "statement": ("Attempt to PROVE (C): (A) rational-coefficient certificate is IMPOSSIBLE -- forced "
                      "g~=f at the rational atoms, but f-values are transcendental (proven no-go). (B) (C) "
                      "reduces to the finite inequality sum_i g_i mu_i(T)<=L (moments=closed-walk counts). "
                      "(C-fail) the local per-vertex decomposition tr(g(H^T H))=sum_v c_v FAILS: at the tie "
                      "arm c_v=0.2272 > L, balanced only globally by root 0.148 / leaf 0.198 (discharging). "
                      "So (C) needs a global argument; not closed here. (C) => Phi<=1 (stronger), so it is of "
                      "equivalent difficulty. Strong candidate, NOT a theorem. conjecture1_proved=False."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

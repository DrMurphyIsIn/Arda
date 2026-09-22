#!/usr/bin/env python3
"""Two add-ons to gauss_window_numerics.py (same conventions; conjecture1_proved = False):

  3c. the HYBRID (b'): method (b) made elementary by c-cells.  For c in [c_j, c_{j+1}] (0 <= c_j) the
      bump mass in |r| < rho is at most the centred-bump mass in [-rho - c_{j+1}, rho - c_j] (window
      monotonicity), and the pole term is bounded below on the cell by its monotone pieces
      (2 lam c <= pi/2).  Per cell: bound_j = P_floor_j + phi_0 + Sum_{k>=1} (phi_k - phi_{k-1}) (1 - cap_j(r_k)/M)
      - log pi - PrimeBound.  Certified lam0 as a function of the cell width and K.  Exact erf caps
      (each cap is two erf values: the erf-free cost is a further per-cap inequality, see 3b).
  4c. the best polynomial-moment bound for the LOG piece of Binet, as a linear programme over the
      coefficients of p(x), x = r^2:  maximise min_{c in grid} E_c[p(r^2)] subject to p(x_j) <= log(1/16 + x_j/4)
      on a fine x-grid up to a large X_big and leading coefficient <= 0 (so p <= log globally, checked on the grid).
"""
import math
import sys
import os
import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gauss_window_numerics as g


def hybrid_min(lam, edges, floor, prime_bound, cells):
    """min over cells of the cell bound (cells: array of c-cell edges starting at 0)."""
    M = g.M_of(lam)
    A = g.A_of(lam)
    r = np.concatenate([[0.0], np.asarray(edges, dtype=float)])
    phi = np.maximum.accumulate(floor(r))
    dphi = np.diff(phi)
    worst = np.inf
    worst_c = None
    for cj, cj1 in zip(cells, cells[1:]):
        caps = g.G_cum(r[1:] - cj, lam) - g.G_cum(-r[1:] - cj1, lam)     # enlarged window
        caps = np.minimum(caps, M)
        avg = phi[0] + np.sum(dphi * (1.0 - caps / M))
        # pole floor on the cell (2 lam c <= pi/2 assumed: true for c <= 200, lam <= 3.9e-3; else use -e^{lam/2}/2)
        if 2 * lam * cj1 <= math.pi / 2:
            pf = 2.0 * math.exp(-2.0 * lam * (cj1 * cj1 - 0.25)) * (cj * cj - 0.25) * math.cos(2.0 * lam * cj1)
            if cj * cj - 0.25 < 0:
                pf = -0.5 * math.exp(lam / 2.0)
        else:
            pf = -0.5 * math.exp(lam / 2.0)
        v = pf / A + avg - g.LOG_PI - prime_bound(lam)
        if v < worst:
            worst, worst_c = v, cj
    return worst, worst_c


def hybrid_lam0(K, floor, prime_bound, dc_over_w, cmax_over_w=4.0):
    def best(lam):
        w = g.width(lam)
        cells = np.arange(0.0, cmax_over_w * w + 1e-9, dc_over_w * w)
        bestv = -np.inf
        for R in [1.5 * w, 2.5 * w, 4.0 * w]:
            for p in [1.0, 1.5, 2.0]:
                v, _ = hybrid_min(lam, g.edges_family(K, R, p), floor, prime_bound, cells)
                bestv = max(bestv, v)
        return bestv
    return g.bisect_lam(lambda l: best(l) >= 0, 1e-6, 0.03, 20)


def section_3c():
    print("## 3c. Hybrid (b'): c-cells of width dc (units of w) on [0, 4w] with enlarged-window caps and cell pole floors; beyond 4w the")
    print("#      bound is monotone-safe (one cell [4w, 200] is included).  Exact erf caps.  Certified lam0.")
    pb = g.prime_abs_closed_form
    print(f"{'floor':<32} {'K':>3} " + " ".join(f"{'dc=' + str(d) + 'w':>10}" for d in [0.5, 0.25, 0.1, 0.05]))
    for name in ['exact psiR at edges', 'Stirling (S) 7/24', 'Stirling20 + psi(1/4) floor']:
        floor = g.FLOORS[name]
        for K in [5, 10, 20]:
            row = []
            for dc in [0.5, 0.25, 0.1, 0.05]:
                row.append(hybrid_lam0(K, floor, pb, dc))
            print(f"{name:<32} {K:>3} " + " ".join(f"{v:>10.3e}" for v in row))
            sys.stdout.flush()
    print()


def lp_polynomial_bound(lam, deg, cmax_over_w=3.0, ngrid=60):
    """max over polynomial p of degree deg (in x = r^2) of min_c E_c[p], s.t. p <= log(1/16 + x/4) on [0, X_big]."""
    w = g.width(lam)
    X_big = (cmax_over_w * w + 12 * w) ** 2
    xs = np.concatenate([np.linspace(0, 4 * w * w, 2000), np.geomspace(4 * w * w, X_big, 2000)])
    # scale x by w^2 for conditioning
    xs_s = xs / (w * w)
    # moments of the bump about c: E[(x + c)^{2k}] with x ~ bump; E x^{2j} = (2j+1)!!/(2 (2 lam))^j ... compute numerically exactly:
    # E x^{2j} = Gamma(j + 3/2) / (Gamma(3/2) (2 lam)^j)
    def Ex2j(j):
        return math.gamma(j + 1.5) / (math.gamma(1.5) * (2 * lam) ** j)
    cs = np.linspace(0, cmax_over_w * w, ngrid)
    # E_c[(r^2)^k] = E[(x + c)^{2k}] = Sum_{i even} C(2k, i) c^{2k-i} E x^i
    from math import comb
    Mom = np.zeros((len(cs), deg + 1))
    for k in range(deg + 1):
        for ic, c in enumerate(cs):
            s = 0.0
            for i in range(0, 2 * k + 1, 2):
                s += comb(2 * k, i) * c ** (2 * k - i) * Ex2j(i // 2)
            Mom[ic, k] = s / (w * w) ** k
    # LP: variables a_0..a_deg, t; maximise t; t <= Mom[c] . a; V(xs) a <= log(...)
    V = np.vander(xs_s, deg + 1, increasing=True)
    L = np.log(1.0 / 16.0 + xs / 4.0)
    nv = deg + 2
    cobj = np.zeros(nv); cobj[-1] = -1.0
    A_ub = np.vstack([np.hstack([V, np.zeros((len(xs), 1))]), np.hstack([-Mom, np.ones((len(cs), 1))])])
    b_ub = np.concatenate([L, np.zeros(len(cs))])
    bounds = [(None, None)] * (deg + 1) + [(None, None)]
    res = linprog(cobj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    if not res.success:
        return None
    a = res.x[:-1]
    t = -res.fun
    return t, a


def section_4c():
    print("## 4c. Best polynomial-moment lower bound on LOG = (1/2) E_c[log(1/16 + r^2/4)] (LP over degree-d polynomials in r^2, p <= log on [0, X_big])")
    print("#      value = (1/2) min over c in [0, 3w] of E_c[p]; compare with the true min over c of LOG (same c range); F/A margin uses the exact floors elsewhere.")
    print(f"{'lam':>7} {'deg':>4} {'(1/2)min E_c[p]':>16} {'true min LOG':>13} {'loss':>7}")
    for lam in [3e-4, 1e-3, 3e-3]:
        w = g.width(lam)
        cs = np.linspace(0, 3 * w, 31)
        true = min(g.binet_pieces(c, lam)[1] for c in cs)
        for deg in [2, 4, 6, 8, 12]:
            out = lp_polynomial_bound(lam, deg)
            if out is None:
                print(f"{lam:>7.3g} {deg:>4} {'LP failed':>16}")
                continue
            t, a = out
            print(f"{lam:>7.3g} {deg:>4} {0.5 * t:>16.4f} {true:>13.4f} {true - 0.5 * t:>7.3f}")
            sys.stdout.flush()
    print("#  The loss is what a closed-form (moments only) treatment of the log piece costs relative to the exact bump average;")
    print("#  subtract it from the method-(a)/(b) margins to see whether anything survives (the Arch margin at lam = 1e-3 is 0.92).")
    print()


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else '3c,4c'
    if '3c' in which:
        section_3c()
    if '4c' in which:
        section_4c()
    print("# conjecture1_proved = False.")

"""Intermediate rung (no finite-matrix certificate): pole-free Cauchy-Schwarz caps + layer cake.
2026-10-11.  Exact rationals (python-flint fmpq); floors cross-checked against arb digamma.
Certified-in-script, NOT kernel-checked.  conjecture1_proved = False.

THE BOUND.  g smooth, tsupport g in [-L, L], int g e^{-u/2} = 0.  For every real r and every c in C,
    ghat(r) = int g(u) (e^{iru} - c e^{-u/2}) du,   so   |ghat(r)|^2 <= ||g||^2 D(r)^2,
    D(r)^2 = min_c int_{-L}^{L} |e^{iru} - c e^{-u/2}|^2 du
           = 2L - 2 (sinh(L/2)^2 + sin(rL)^2) / ((r^2 + 1/4) sinh L).
Band caps: on band j = [a_j, a_{j+1}) (and its mirror), D(r)^2 <= S_j with
    S_j = 2L - 2 (SH2 + m_j) / ((a_{j+1}^2 + 1/4) SINHL_UP),
    SH2 <= sinh(L/2)^2 (from sinh x >= x + x^3/6), SINHL_UP >= sinh L (Taylor + e^L bound),
    m_j <= min_{band} sin(rL)^2 (T7(x) = x - x^3/6 + x^5/120 - x^7/5040 <= sin x on [0, pi/2],
           sin(x) = sin(pi - x), concavity on [0, pi]; m_j = 0 once a_{j+1} L > PI_LO).
Cumulative cap C_k := sum_{j<k} 2 S_j (a_{j+1} - a_j), so int_{|r|<a_k} |ghat|^2 <= C_k ||g||^2.
Layer cake (E6Bridge31 CakeW with the window bound 2 rho S replaced by C_k): for K with
C_K <= 2 PI_LO (<= 2 pi = int |ghat|^2 / ||g||^2),
    (1/2pi) int |ghat|^2 psiR >= ||g||^2 [ phi_K - (1/(2 PI_LO)) sum_{k=1..K} (phi_k - phi_{k-1}) C_k ],
phi_k <= psiR(a_k) the rational floors (E6Bridge30 psiR_ge_rational, N = 40, M = 10^6).
So Q(g) >= ||g||^2 * BOUND,  BOUND = phi_K - LOGPI_UP - (1/(2 PI_LO)) sum_k (phi_k - phi_{k-1}) C_k.

usage: python intermediate_rung.py
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import sys
from flint import fmpq, arb, acb, ctx
import cert_exact as CE

ctx.prec = 128
PI_LO, PI_UP = fmpq(314159, 100000), fmpq(314160, 100000)
LOGPI_UP = fmpq(1159, 1000)          # E6Bridge31 log_pi_le


def T7(x):
    return x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040


def sinh_lo(x):                       # sinh x >= x + x^3/6 + x^5/120 + x^7/5040 (x >= 0)
    return x + x ** 3 / 6 + x ** 5 / 120 + x ** 7 / 5040


def sinh_up(x):                       # sinh x <= x + x^3/6 + x^5/120 + x^7/5040 * cosh x  (0 <= x <= 1, cosh 1 < 1.6)
    return x + x ** 3 / 6 + x ** 5 / 120 + x ** 7 / 5040 * fmpq(16, 10)


def sin2_lo(a, b, L):
    """rational lower bound of sin(rL)^2 on r in [a, b] (0 <= a < b)."""
    xa, xb = a * L, b * L
    if xb > PI_LO:
        return fmpq(0)
    half = PI_LO / 2
    cands = []
    # sin(x) >= T7(x) for 0 <= x <= pi/2 ; sin(x) = sin(pi - x) >= T7(PI_LO - x) when pi - x in [0, pi/2]
    if xa <= half:
        cands.append(T7(xa))
    else:
        cands.append(T7(PI_LO - xa))
    if xb <= half:
        cands.append(T7(xb))
    else:
        cands.append(T7(PI_LO - xb))
    m = min(cands)
    return m * m if m > 0 else fmpq(0)


def cumulative_caps(L, cgrid, expand=True):
    """C[j] >= int_{|r| < cgrid[j]} D(r)^2 dr, via per-sub-band caps."""
    SH2 = sinh_lo(L / 2) ** 2
    SHL = sinh_up(L)
    caps, C = [], [fmpq(0)]
    for j in range(len(cgrid) - 1):
        a, b = cgrid[j], cgrid[j + 1]
        S = 2 * L - 2 * (SH2 + sin2_lo(a, b, L)) / ((b * b + fmpq(1, 4)) * SHL)
        if expand:
            qa, qb = a * a + fmpq(1, 4), b * b + fmpq(1, 4)
            X = L * L + (SH2 - L * L / 4) / qb - (b * L) ** 4 / 3 / qb \
                + 2 * (a * L) ** 6 / 45 / qa - (b * L) ** 8 / 315 / qb
            S = min(S, 2 * L - 2 * X / SHL)
        S = max(S, fmpq(0))
        caps.append(S)
        C.append(C[-1] + 2 * S * (b - a))
    return caps, C


def bound2(L, fgrid, sub, nser=40):
    """floors on fgrid; caps on fgrid refined `sub` times."""
    cgrid = [fgrid[0]]
    for a, b in zip(fgrid[:-1], fgrid[1:]):
        for i in range(1, sub + 1):
            cgrid.append(a + (b - a) * i / sub)
    caps, Cf = cumulative_caps(L, cgrid)
    C = [Cf[sub * k] for k in range(len(fgrid))]
    phis = [CE.round_down(CE.psiR_ge_rational(r, nser, 10 ** 6)) for r in fgrid]
    K = max(k for k in range(len(fgrid)) if C[k] <= 2 * PI_LO)
    acc = sum(((phis[k] - phis[k - 1]) * C[k] for k in range(1, K + 1)), fmpq(0))
    return phis[K] - LOGPI_UP - acc / (2 * PI_LO), K, phis, caps, C, cgrid


def bound(L, grid, nser=40, verbose=False, expand=True):
    SH2 = sinh_lo(L / 2) ** 2
    SHL = sinh_up(L)
    caps, C = [], [fmpq(0)]
    for j in range(len(grid) - 1):
        a, b = grid[j], grid[j + 1]
        S = 2 * L - 2 * (SH2 + sin2_lo(a, b, L)) / ((b * b + fmpq(1, 4)) * SHL)
        if expand:
            # cancellation-aware: sin^2 x >= x^2 - x^4/3 + 2x^6/45 - x^8/315 (all real x), so
            # (sh^2 + sin^2(rL))/(r^2+1/4) >= L^2 + (SH2 - L^2/4)/(r^2+1/4) - (rL)^4/3/(r^2+1/4)
            #     + 2(rL)^6/45/(r^2+1/4) - (rL)^8/315/(r^2+1/4); each piece monotone on the band.
            qa, qb = a * a + fmpq(1, 4), b * b + fmpq(1, 4)
            X = L * L + (SH2 - L * L / 4) / qb - (b * L) ** 4 / 3 / qb \
                + 2 * (a * L) ** 6 / 45 / qa - (b * L) ** 8 / 315 / qb
            S = min(S, 2 * L - 2 * X / SHL)
        S = max(S, fmpq(0))
        caps.append(S)
        C.append(C[-1] + 2 * S * (b - a))
    phis = []
    for r in grid:
        f = CE.round_down(CE.psiR_ge_rational(r, nser, 10 ** 6))
        assert arb(f.p) / arb(f.q) < CE.psiR_arb(r)
        phis.append(f)
    # largest K with C_K <= 2 PI_LO
    K = max(k for k in range(len(grid)) if C[k] <= 2 * PI_LO)
    acc = fmpq(0)
    for k in range(1, K + 1):
        acc += (phis[k] - phis[k - 1]) * C[k]
    val = phis[K] - LOGPI_UP - acc / (2 * PI_LO)
    if verbose:
        print(f"   K={K} (radius {float(grid[K]):.3f}), phi_K={float(phis[K]):.5f}, C_K={float(C[K]):.4f} <= 2pi_lo")
    return val, K, phis, caps, C


def uniform(R, h):
    return [h * j for j in range(int(R / h) + 1)]


def check_caps(L, cgrid, caps):
    """float sanity: every rational cap dominates the exact D(r)^2 sampled on its sub-band."""
    import numpy as np
    Lf = float(L)
    worst = 1e9
    for (a, b), S in zip(zip(cgrid[:-1], cgrid[1:]), caps):
        r = np.linspace(float(a), float(b), 64)
        z = 1j * r - 0.5
        A = (np.exp(z * Lf) - np.exp(-z * Lf)) / z
        d2 = 2 * Lf - np.abs(A) ** 2 / (2 * math.sinh(Lf))
        worst = min(worst, float(S) - d2.max())
    return worst


if __name__ == "__main__" and "--decoupled" in sys.argv:
    for Lq in [fmpq(1, 4), fmpq(27, 100), fmpq(7, 25), fmpq(29, 100), fmpq(3, 10)]:
        for hf, sub in [(fmpq(1, 2), 8), (fmpq(1, 4), 4), (fmpq(1, 4), 8), (fmpq(1, 8), 4)]:
            fgrid = uniform(fmpq(16), hf)
            v, K, phis, caps, C, cg = bound2(Lq, fgrid, sub)
            print(f"L={float(Lq):.3f} floors every {float(hf)} (K={K}, floors used {K + 1}), "
                  f"cap sub-bands {sub}x ({len(cg) - 1})  BOUND={float(v):+.5f}  "
                  f"cap-check min(S - D^2)={check_caps(Lq, cg, caps):+.2e}", flush=True)
    sys.exit(0)

if __name__ == "__main__" and "--final" not in sys.argv:
    for Lq in [fmpq(1, 5), fmpq(1, 4), fmpq(27, 100), fmpq(7, 25), fmpq(29, 100), fmpq(3, 10)]:
        for h in [fmpq(1, 2), fmpq(1, 4), fmpq(1, 8)]:
            grid = uniform(fmpq(16), h)
            v, K, *_ = bound(Lq, grid)
            print(f"L={float(Lq):.3f} h={float(h):.3f} bands used={K:3d}  BOUND={float(v):+.5f}", flush=True)


def final(Lq=fmpq(7, 25), hf=fmpq(1, 4), sub=4, logpi=None, dump=True):
    """The recommended intermediate-rung instance; prints exact data and validates the chain on
    test functions (cumulative-cap inequality int_{|r|<rho_k} |ghat|^2 <= C_k ||g||^2)."""
    global LOGPI_UP
    if logpi is not None:
        LOGPI_UP = logpi
    fgrid = uniform(fmpq(16), hf)
    v, K, phis, caps, C, cg = bound2(Lq, fgrid, sub)
    print(f"INTERMEDIATE RUNG L = {Lq} = {float(Lq)}: floors {K + 1} (every {hf} up to {float(fgrid[K])}), "
          f"cap sub-bands {sub * K} used, LOGPI_UP = {LOGPI_UP}, BOUND = {float(v):+.6f} (exact {v})")
    print(f"   cap check min(S - D^2) = {check_caps(Lq, cg, caps):+.2e}")
    import numpy as np
    from numpy.polynomial.legendre import leggauss, legvander
    Lf = float(Lq)
    x, wx = leggauss(300)
    u, wu = Lf * x, Lf * wx
    rng = np.random.default_rng(7)
    worst = 1e9
    for t in range(20):
        deg = int(rng.integers(2, 30))
        bump = np.exp(-1 / np.maximum(1 - x ** 2, 1e-300))
        gv = bump * (legvander(x, deg - 1) @ rng.normal(size=deg))
        e = np.exp(-u / 2)
        b = bump * e
        gv = gv - (np.sum(wu * gv * e) / np.sum(wu * b * e)) * b
        nrm2 = np.sum(wu * gv ** 2)
        for k in range(1, K + 1):
            rho = float(fgrid[k])
            r = np.linspace(0, rho, 400)
            gh = np.abs((np.exp(1j * np.outer(r, u)) * (gv * wu)[None, :]).sum(1)) ** 2
            mass = 2 * np.trapezoid(gh, r)
            worst = min(worst, float(C[k]) * nrm2 - mass)
    print(f"   chain check on 20 random pole-free tests: min_k (C_k ||g||^2 - int_(|r|<rho_k) |ghat|^2) = {worst:+.3e}")
    if dump:
        import json
        with open(f"intermediate_L{Lq.p}_{Lq.q}.json", "w") as fh:
            json.dump(dict(L=str(Lq), floors_grid=[str(r) for r in fgrid[:K + 1]],
                           floors=[str(p) for p in phis[:K + 1]],
                           cap_subgrid=[str(r) for r in cg[:sub * K + 1]], caps=[str(cp) for cp in caps[:sub * K]],
                           cumulative_caps=[str(c) for c in C[:K + 1]], LOGPI_UP=str(LOGPI_UP),
                           PI_LO=str(PI_LO), BOUND=str(v)), fh)
    return v


if __name__ == "__main__" and "--final" in sys.argv:
    final()
    final(Lq=fmpq(29, 100), hf=fmpq(1, 4), sub=8, dump=False)
    final(Lq=fmpq(29, 100), hf=fmpq(1, 4), sub=8, logpi=fmpq(11455, 10000), dump=False)

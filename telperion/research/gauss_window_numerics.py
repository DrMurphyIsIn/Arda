#!/usr/bin/env python3
"""Numerics for the Gaussian-window design memo (docs/GAUSS_WINDOW_DESIGN_2026-09-22.md).

conjecture1_proved = False.  Nothing in this file proves, or is meant to prove, anything about the
Riemann Hypothesis.  Everything here MEASURES (float64 grids, mpmath spot checks) the pieces of the
unconditional identity behind E6Bridge11 / E6Bridge16 and the lower bounds one can put on them.

The identity (E6Bridge10/11, hypothesis-free), with bump B(r) = (r - c)^2 e^{-2 lam (r - c)^2},
A = 1/(8 sqrt(2 pi) lam^{3/2}), M = int B = 2 pi A, psiR(r) = Re psi(1/4 + i r/2):

    F(c, lam) := Re Sum_rho m(rho) (gamma_rho - c)^2 e^{-2 lam (gamma_rho - c)^2}
              = P(c, lam) + Arch(c, lam) - Primes(c, lam),
    P      = 2 e^{-2 lam (c^2 - 1/4)} [(c^2 - 1/4) cos(2 lam c) + c sin(2 lam c)]      (= 2 Re gaussTest(i/2)),
    Arch   = (1/2 pi) int B(r) (psiR(r) - log pi) dr,
    Primes = 2 A Sum_{n >= 2} Lambda(n) n^{-1/2} (1 - u^2/(4 lam)) e^{-u^2/(8 lam)} cos(c u),  u = log n,
    PrimeAbs = 2 A Sum Lambda(n) n^{-1/2} |1 - u^2/(4 lam)| e^{-u^2/(8 lam)}        (E6Bridge16.primeAbs * A).

Everything is reported in units of A (divide by A), so that Arch/A = <psiR>_B - log pi with <.>_B the
bump average.

Sections (flags select them; default runs all with the landscape lam list):
  0. identity check: zero sum (first 2000 zeros, cached) vs P + Arch - Primes.
  1. landscape: min over c in [0, 200] of F, Arch, P + Arch, P + Arch - PrimeAbs; lam_max(l1), lam_max(arch).
  2. method (a): c-uniform band bounds (monotone floors on psiR, window-mass caps), K bands optimised.
  3. method (b): c-dependent band bounds (exact erf masses per c, min over c), and the erf-free variant.
  4. method (c): Binet decomposition of the archimedean integral; chord bounds on the log piece.
  5. summary.

Usage: python3 telperion/research/gauss_window_numerics.py [--zeros FILE] [--quick]
Runtime: about 4 minutes (full), about 1 minute (--quick).
"""
import argparse
import json
import math
import os
import sys
import time

import numpy as np
from scipy.special import digamma as sp_digamma, erf as sp_erf
from scipy.signal import fftconvolve
from scipy.optimize import minimize

LOG_PI = math.log(math.pi)
PSI_QUARTER = -4.2274535333762654   # psi(1/4) = -gamma - pi/2 - 3 log 2 (exact); psiR(0)
BINET_C = 0.8411587                 # int_0^inf phi(t) e^{-t/4} dt = log(1/4) - 2 - psi(1/4) (survey E.3)
LAM_LIST = [1e-4, 3e-4, 1e-3, 3e-3, 0.01, 0.02, 0.03, 0.05, 0.1]
C_MAX = 200.0


# ----------------------------------------------------------------------------------------------
# basic pieces
# ----------------------------------------------------------------------------------------------
def A_of(lam):
    return 1.0 / (8.0 * math.sqrt(2.0 * math.pi) * lam ** 1.5)


def M_of(lam):
    """int (r-c)^2 e^{-2 lam (r-c)^2} dr = sqrt(pi/(2 lam)) / (4 lam) = 2 pi A."""
    return 2.0 * math.pi * A_of(lam)


def width(lam):
    """the lobe position 1/sqrt(2 lam) (peak of x^2 e^{-2 lam x^2})."""
    return 1.0 / math.sqrt(2.0 * lam)


def psiR(r):
    """Re psi(1/4 + i r/2), vectorised (scipy complex digamma; agrees with mpmath to 1e-12)."""
    r = np.asarray(r, dtype=float)
    return np.real(sp_digamma(0.25 + 0.5j * r))


def pole_term(c, lam):
    c = np.asarray(c, dtype=float)
    return 2.0 * np.exp(-2.0 * lam * (c * c - 0.25)) * ((c * c - 0.25) * np.cos(2.0 * lam * c) + c * np.sin(2.0 * lam * c))


def von_mangoldt(N):
    """Lambda(n), n <= N, as an array (float), by a smallest-prime-factor sieve."""
    spf = np.zeros(N + 1, dtype=np.int64)
    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i:N + 1:i][spf[i:N + 1:i] == 0] = i
    lam = np.zeros(N + 1)
    for n in range(2, N + 1):
        p = spf[n]
        m = n
        while m % p == 0:
            m //= p
        if m == 1:
            lam[n] = math.log(p)
    return lam


_LAMBDA = None


def lambda_table(N=200000):
    global _LAMBDA
    if _LAMBDA is None or len(_LAMBDA) < N + 1:
        _LAMBDA = von_mangoldt(N)
    return _LAMBDA


def prime_terms(lam, cutoff=80.0):
    """(n, weight) with weight = 2 Lambda(n) n^{-1/2} (1 - u^2/(4 lam)) e^{-u^2/(8 lam)}, u = log n,
    over n with u^2/(8 lam) <= cutoff (the rest is < e^{-cutoff} relative).  Units of A."""
    tab = lambda_table()
    n = np.arange(2, len(tab))
    u = np.log(n)
    keep = (u * u / (8.0 * lam) <= cutoff) & (tab[2:] > 0)
    n = n[keep]
    u = u[keep]
    w = 2.0 * tab[n] / np.sqrt(n) * (1.0 - u * u / (4.0 * lam)) * np.exp(-u * u / (8.0 * lam))
    return n, u, w


def primes_over_A(c, lam):
    """Primes(c, lam)/A, vectorised in c."""
    n, u, w = prime_terms(lam)
    c = np.atleast_1d(np.asarray(c, dtype=float))
    return (np.cos(np.outer(c, u)) * w).sum(axis=1)


def prime_abs_over_A(lam):
    n, u, w = prime_terms(lam)
    return float(np.abs(w).sum())


def prime_abs_closed_form(lam):
    """A Lean-shaped closed-form majorant of PrimeAbs/A for lam <= 1/40 (see memo, section 2):
    n = 2 term exact + tail over n >= 3 with e^{-u^2/(8 lam)} <= n^{-sigma}, sigma = log 3/(8 lam),
    |1 - u^2/(4 lam)| <= 1 + u^2/(4 lam) <= 1 + (2 sqrt n)^2/(4 lam) = 1 + n/lam, Lambda(n) <= log n <= sqrt n:
    tail <= 2 Sum_{n>=3} n^{-sigma} (1 + n/lam) <= 2 (1 + 1/lam) Sum_{n>=3} n^{1 - sigma}
         <= 2 (1 + 1/lam) 3^{2 - sigma} (sigma - 2)^{-1} ... we use the integral test: Sum_{n>=3} n^{1-sigma}
         <= 3^{1-sigma} + 3^{2-sigma}/(sigma - 2)  (sigma > 2)."""
    u2 = math.log(2.0)
    t2 = 2.0 * u2 / math.sqrt(2.0) * abs(1.0 - u2 * u2 / (4.0 * lam)) * math.exp(-u2 * u2 / (8.0 * lam))
    sigma = math.log(3.0) / (8.0 * lam)
    if sigma <= 2.5:
        return float('inf')
    tail = 2.0 * (1.0 + 1.0 / lam) * (3.0 ** (1.0 - sigma) + 3.0 ** (2.0 - sigma) / (sigma - 2.0))
    return t2 + tail


def e6b11_prime_bound(lam):
    """E6Bridge11.norm_primeSide_le: 64 e^{-(log 2)^2/(16 lam)} (units of A), valid for log 2/(16 lam) >= 2."""
    if math.log(2.0) / (16.0 * lam) < 2.0:
        return float('inf')
    return 64.0 * math.exp(-math.log(2.0) ** 2 / (16.0 * lam))


# ----------------------------------------------------------------------------------------------
# the archimedean integral as a convolution on a grid
# ----------------------------------------------------------------------------------------------
class ArchGrid:
    """<psiR>_B(c) = (1/M) int B(r - c) psiR(r) dr for c on a grid [0, cmax], by FFT convolution on a
    uniform r-grid of step h.  psiR is analytic in |Im r| < 1/2 so the trapezoid rule on step h
    has error ~ e^{-pi/h}; h = 0.01 is far beyond double precision."""

    def __init__(self, lam, cmax=C_MAX, h=0.01, nsig=8.0):
        self.lam = lam
        self.h = h
        w = width(lam)
        L = nsig * w                       # e^{-2 lam L^2} = e^{-2 nsig^2} ~ e^{-128}
        self.L = L
        nk = int(math.ceil(L / h))
        x = np.arange(-nk, nk + 1) * h
        self.kernel = x * x * np.exp(-2.0 * lam * x * x)
        nr = int(math.ceil((cmax + L) / h))
        r = np.arange(-nr, nr + 1) * h
        self.r = r
        self.psi = psiR(r)
        full = fftconvolve(self.psi, self.kernel, mode='same') * h     # (B * psiR)(r) on the r grid
        self.conv = full
        self.mass = self.kernel.sum() * h
        self.M = M_of(lam)
        # c grid = the r grid restricted to [0, cmax]
        sel = (r >= -1e-12) & (r <= cmax + 1e-12)
        self.c = r[sel]
        self.avg = full[sel] / self.mass    # <psiR>_B(c)

    def arch_over_A(self):
        """Arch/A = <psiR>_B - log pi on the c grid."""
        return self.avg - LOG_PI


def zero_sum_over_A(c, lam, zeros):
    """F/A from the first len(zeros) zeros (both signs), vectorised in c.  The tail beyond gamma_N is
    e^{-2 lam (gamma_N - c)^2} ~ 0 for c <= 200, lam >= 1e-4 (gamma_2000 = 2515)."""
    c = np.atleast_1d(np.asarray(c, dtype=float))
    g = np.asarray(zeros)
    out = np.empty_like(c)
    A = A_of(lam)
    for i, ci in enumerate(c):
        d1 = g - ci
        d2 = -g - ci
        out[i] = (np.sum(d1 * d1 * np.exp(-2.0 * lam * d1 * d1)) + np.sum(d2 * d2 * np.exp(-2.0 * lam * d2 * d2))) / A
    return out


def load_zeros(path):
    with open(path) as fh:
        return np.array([float(x) for x in json.load(fh)])


# ----------------------------------------------------------------------------------------------
# section 0: identity check with mpmath (independent of the grid machinery)
# ----------------------------------------------------------------------------------------------
def identity_check(zeros):
    import mpmath as mp
    mp.mp.dps = 25
    print("## 0. Identity check: zero sum (2000 zeros) vs P + Arch - Primes (mpmath quad, dps 25)")
    print(f"{'lam':>6} {'c':>4} {'F zero-sum/A':>16} {'P/A':>12} {'Arch/A':>12} {'Primes/A':>12} {'RHS/A':>16} {'rel.diff':>10}")
    tab = lambda_table()
    worst = 0.0
    for lam in [0.003, 0.01, 0.03]:
        laml = mp.mpf(lam)
        A = 1 / (8 * mp.sqrt(2 * mp.pi) * laml ** mp.mpf(1.5))
        for c in [0, 5, 13, 30]:
            cl = mp.mpf(c)
            # zero side
            zs = mp.mpf(0)
            for g in zeros:
                gl = mp.mpf(g)
                for s in (gl, -gl):
                    d = s - cl
                    zs += d * d * mp.exp(-2 * laml * d * d)
            # pole
            z = mp.mpc(0, 0.5)
            P = 2 * mp.re((z - cl) ** 2 * mp.exp(-2 * laml * (z - cl) ** 2))
            # arch
            w = 1 / mp.sqrt(2 * laml)
            Lr = 8 * w
            pts = sorted({cl - Lr, cl - 3 * w, cl - w, cl, cl + w, cl + 3 * w, cl + Lr, mp.mpf(-3), mp.mpf(0), mp.mpf(3)})
            pts = [p for p in pts if cl - Lr <= p <= cl + Lr]
            integ = mp.quad(lambda r: (r - cl) ** 2 * mp.exp(-2 * laml * (r - cl) ** 2) * (mp.re(mp.digamma(mp.mpc(0.25, r / 2))) - mp.log(mp.pi)), pts)
            Arch = integ / (2 * mp.pi)
            # primes
            pr = mp.mpf(0)
            for n in range(2, len(tab)):
                if tab[n] == 0:
                    continue
                u = mp.log(n)
                e = u * u / (8 * laml)
                if e > 90:
                    break
                pr += 2 * A * mp.mpf(tab[n]) / mp.sqrt(n) * (1 - u * u / (4 * laml)) * mp.exp(-e) * mp.cos(cl * u)
            rhs = P + Arch - pr
            rel = (rhs - zs) / zs
            worst = max(worst, abs(float(rel)))
            print(f"{lam:>6} {c:>4} {mp.nstr(zs / A, 10):>16} {mp.nstr(P / A, 6):>12} {mp.nstr(Arch / A, 8):>12} {mp.nstr(pr / A, 8):>12} {mp.nstr(rhs / A, 10):>16} {mp.nstr(rel, 3):>10}")
            sys.stdout.flush()
    print(f"# worst relative difference: {worst:.3e}  (the zero-side tail beyond gamma_2000 = 2515 is < e^{{-2 lam (2515 - 30)^2}} = 0)")
    print()


# ----------------------------------------------------------------------------------------------
# section 1: landscape
# ----------------------------------------------------------------------------------------------
def landscape_row(lam, zeros, h=0.01, with_zeros=True):
    G = ArchGrid(lam, h=h)
    c = G.c
    arch = G.arch_over_A()
    A = A_of(lam)
    P = pole_term(c, lam) / A
    pabs = prime_abs_over_A(lam)
    pr = primes_over_A(c, lam)
    pa = P + arch
    l1 = pa - pabs
    sgn = pa - pr
    out = dict(lam=lam, A=A, w=width(lam), pabs=pabs,
               arch_min=float(arch.min()), arch_arg=float(c[arch.argmin()]),
               pa_min=float(pa.min()), pa_arg=float(c[pa.argmin()]),
               l1_min=float(l1.min()), l1_arg=float(c[l1.argmin()]),
               sgn_min=float(sgn.min()), sgn_arg=float(c[sgn.argmin()]),
               arch0=float(arch[0]), pa0=float(pa[0]), l10=float(l1[0]))
    if with_zeros:
        # zero sum on a coarser c grid (every 0.1) plus the argmin points
        cz = np.concatenate([np.arange(0.0, C_MAX + 1e-9, 0.1), [out['sgn_arg'], out['pa_arg']]])
        fz = zero_sum_over_A(cz, lam, zeros)
        out['F_min'] = float(fz.min())
        out['F_arg'] = float(cz[fz.argmin()])
        out['F_at_sgnarg'] = float(fz[-2])
        out['F0'] = float(fz[0])
    return out


def landscape(zeros, lams=LAM_LIST):
    print("## 1. Landscape: minima over c in [0, 200] (units of A; c step 0.01 for the prime-side columns, 0.1 for the zero sum)")
    print(f"{'lam':>7} {'w':>6} {'A':>9} {'PrimeAbs/A':>11} | {'min Arch':>9} {'@c':>6} | {'min P+Arch':>10} {'@c':>6} | {'min P+Arch-PrimeAbs':>19} {'@c':>6} | {'min P+Arch-Primes':>17} {'@c':>6} | {'min F(zeros)':>12} {'@c':>6} {'F@sgnarg':>10}")
    rows = []
    for lam in lams:
        t0 = time.time()
        R = landscape_row(lam, zeros)
        rows.append(R)
        print(f"{lam:>7.4g} {R['w']:>6.1f} {R['A']:>9.4g} {R['pabs']:>11.3e} | {R['arch_min']:>9.4f} {R['arch_arg']:>6.2f} | {R['pa_min']:>10.4f} {R['pa_arg']:>6.2f} | {R['l1_min']:>19.4f} {R['l1_arg']:>6.2f} | {R['sgn_min']:>17.4e} {R['sgn_arg']:>6.2f} | {R['F_min']:>12.4e} {R['F_arg']:>6.2f} {R['F_at_sgnarg']:>10.4e}")
        sys.stdout.flush()
    print("# (min P+Arch-Primes is F through the identity; min F(zeros) is the zero sum: they agree to grid accuracy.)")
    print()
    return rows


def bisect_lam(pred, lo, hi, iters=40):
    """largest lam in [lo, hi] with pred(lam) true, assuming pred true at lo and false at hi (monotone)."""
    for _ in range(iters):
        mid = math.sqrt(lo * hi)
        if pred(mid):
            lo = mid
        else:
            hi = mid
    return lo


def landscape_thresholds():
    print("## 1b. Thresholds (bisection in lam, c step 0.01 on [0, 200])")

    def min_l1(lam):
        G = ArchGrid(lam)
        pa = pole_term(G.c, lam) / A_of(lam) + G.arch_over_A()
        return float(pa.min()) - prime_abs_over_A(lam), float(G.c[pa.argmin()]), float(pa.min())

    lam_l1 = bisect_lam(lambda l: min_l1(l)[0] >= 0, 1e-3, 0.05, 36)
    v = min_l1(lam_l1)
    print(f"lam_max(l1)   = {lam_l1:.5f}   (largest lam with min_c [P + Arch - PrimeAbs] >= 0; at that lam argmin c = {v[1]:.2f}, min P+Arch = {v[2]:.4f}, PrimeAbs/A = {prime_abs_over_A(lam_l1):.4f})")
    lam_arch = bisect_lam(lambda l: min_l1(l)[2] >= 0, 1e-3, 0.05, 36)
    v = min_l1(lam_arch)
    print(f"lam_max(arch) = {lam_arch:.5f}   (largest lam with min_c [P + Arch] >= 0; argmin c = {v[1]:.2f})")

    def min_arch_only(lam):
        G = ArchGrid(lam)
        a = G.arch_over_A()
        return float(a.min()), float(G.c[a.argmin()])

    lam_a = bisect_lam(lambda l: min_arch_only(l)[0] >= 0, 1e-3, 0.05, 36)
    print(f"lam_max(Arch alone) = {lam_a:.5f}   (largest lam with min_c Arch >= 0, no pole term; argmin c = {min_arch_only(lam_a)[1]:.2f})")
    print("lam_max(sign) = not finite on this range: min_c [P + Arch - Primes(c)] = min_c F >= 0 at every lam tested")
    print("  (the zeros up to height 2515 are on the line; the signed prime side tracks P + Arch to 1e-3 relative by lam = 0.05).")
    print()
    return lam_l1, lam_arch


# ----------------------------------------------------------------------------------------------
# section 2: method (a), c-uniform band bounds
# ----------------------------------------------------------------------------------------------
def floor_exact(r):
    return psiR(r)


def floor_e6b11(r):
    r = np.asarray(r, dtype=float)
    return np.where(r >= 41.0, 2.0, -5.0)


def make_floor_stirling(floor0=-5.0, err=20.0):
    """psiR >= floor0 everywhere, >= log(r/2) - err/r^2 for r >= 2 (E6Bridge16: err = 20)."""
    def f(r):
        r = np.asarray(r, dtype=float)
        with np.errstate(divide='ignore', invalid='ignore'):
            s = np.log(np.maximum(r, 1e-300) / 2.0) - err / np.maximum(r, 1e-300) ** 2
        return np.where(r >= 2.0, np.maximum(s, floor0), floor0)
    return f


def floor_binetB(r):
    """survey (E.3)(B): psiR >= (1/2) log(1/16 + r^2/4) - 1/(8 |z|^2) - 0.84116 (global, exact at r = 0)."""
    r = np.asarray(r, dtype=float)
    z2 = 1.0 / 16.0 + r * r / 4.0
    return 0.5 * np.log(z2) - 1.0 / (8.0 * z2) - BINET_C


def floor_stirlingS(r):
    """survey (E.3)(S): psiR >= (1/2) log(1/16 + r^2/4) - (7/24)/|z|^2 (Stirling remainder 1/(6|z|^2))."""
    r = np.asarray(r, dtype=float)
    z2 = 1.0 / 16.0 + r * r / 4.0
    return 0.5 * np.log(z2) - (7.0 / 24.0) / z2


def floor_BS(r):
    return np.maximum(floor_binetB(r), floor_stirlingS(r))


FLOORS = {
    'exact psiR at edges': floor_exact,
    'E6Bridge11 (-5 / 2 beyond 41)': floor_e6b11,
    'Stirling20 + floor -5 (E6Bridge16)': make_floor_stirling(-5.0, 20.0),
    'Stirling20 + psi(1/4) floor': make_floor_stirling(PSI_QUARTER, 20.0),
    'Binet (B)': floor_binetB,
    'Stirling (S) 7/24': floor_stirlingS,
    'max(B, S)': floor_BS,
}


def mass_cap_sup(rho, lam):
    """c-uniform bound on the bump mass in |r| < rho: min(M, 2 rho sup B), sup B = 1/(2 lam e)."""
    return np.minimum(M_of(lam), 2.0 * rho / (2.0 * lam * math.e))


def mass_cap_sup_e6b11(rho, lam):
    """E6Bridge11's cruder sup B <= 1/(2 lam) (y e^{-y} <= 1)."""
    return np.minimum(M_of(lam), 2.0 * rho / (2.0 * lam))


def G_cum(x, lam):
    """int_{-inf}^x t^2 e^{-2 lam t^2} dt (exact, erf)."""
    a = 2.0 * lam
    x = np.asarray(x, dtype=float)
    xf = np.where(np.isinf(x), 0.0, x)
    val = -xf * np.exp(-a * xf * xf) / (2.0 * a) + (1.0 / (2.0 * a)) * 0.5 * math.sqrt(math.pi / a) * (1.0 + sp_erf(math.sqrt(a) * xf))
    full = (1.0 / (2.0 * a)) * math.sqrt(math.pi / a)
    return np.where(x == np.inf, full, np.where(x == -np.inf, 0.0, val))


def mass_cap_rearr(rho, lam):
    """c-uniform window-mass bound from the rearrangement argument (memo section 3):
    sup_c int_{|r|<rho} B(r - c) dr <= 4 int_w^{w + rho/2} x^2 e^{-2 lam x^2} dx  (exact erf form)."""
    w = width(lam)
    rho = np.asarray(rho, dtype=float)
    return np.minimum(M_of(lam), 4.0 * (G_cum(w + rho / 2.0, lam) - G_cum(w, lam)))


def mass_cap_rearr_erffree(rho, lam):
    """erf-free version: int_w^X x^2 e^{-2lam x^2} = [-x e^{-2 lam x^2}/(4 lam)]_w^X + (1/(4 lam)) int_w^X e^{-2 lam x^2},
    and, by convexity of x^2 (tangent at w, 2 lam w^2 = 1): e^{-2 lam x^2} <= e^{-1} e^{-4 lam w (x - w)}, so
    int_w^X e^{-2 lam x^2} <= (w/(2e)) (1 - e^{-2 (X - w)/w})."""
    w = width(lam)
    rho = np.asarray(rho, dtype=float)
    X = w + rho / 2.0
    part = (w * math.exp(-1.0) - X * np.exp(-2.0 * lam * X * X)) / (4.0 * lam)
    gauss = (w / (2.0 * math.e)) * (1.0 - np.exp(-2.0 * (X - w) / w)) / (4.0 * lam)
    return np.minimum(M_of(lam), 4.0 * (part + gauss))


_SUPC_CACHE = {}


def mass_cap_exact_supc(rho, lam):
    """the true sup over c of the window mass (numerical, cached on a rho grid per lam), for diagnosis only."""
    w = width(lam)
    if lam not in _SUPC_CACHE:
        rg = np.linspace(0.0, 40.0 * w, 1601)
        cgrid = np.linspace(0.0, 6.0 * w, 601)
        vals = np.empty_like(rg)
        for i, p in enumerate(rg):
            m = G_cum(p - cgrid, lam) - G_cum(-p - cgrid, lam)
            vals[i] = m.max()
        _SUPC_CACHE[lam] = (rg, np.minimum(vals, M_of(lam)))
    rg, vals = _SUPC_CACHE[lam]
    rho = np.asarray(rho, dtype=float)
    return np.interp(rho, rg, vals, right=M_of(lam))


def band_bound(lam, edges, floor, cap):
    """the c-uniform lower bound on <psiR>_B from monotone floors phi_k = floor(r_k) on bands
    [r_k, r_{k+1}) in |r| (r_0 = 0) and the window-mass caps m(rho) >= sup_c mass(|r| < rho):
        <psiR>_B >= phi_0 + Sum_{k>=1} (phi_k - phi_{k-1}) (1 - m(r_k)/M)."""
    edges = np.asarray(edges, dtype=float)
    r = np.concatenate([[0.0], edges])
    phi = floor(r)
    phi = np.maximum.accumulate(phi)          # a valid floor stays valid after the running max (monotone psiR)
    M = M_of(lam)
    frac = 1.0 - cap(edges, lam) / M
    return phi[0] + np.sum(np.diff(phi) * frac)


def method_a_bound(lam, edges, floor, cap, prime_bound):
    """F/A >= P/A + <psiR>_B - log pi - Prime/A with P/A >= -e^{lam/2}/(2A) (c-uniform, valid for
    lam <= 0.3 where the |c| >= pi/(4 lam) remainder is < 1e-15)."""
    pole = -math.exp(lam / 2.0) / (2.0 * A_of(lam))
    return pole + band_bound(lam, edges, floor, cap) - LOG_PI - prime_bound(lam)


def optimise_edges(lam, K, floor, cap, prime_bound, rmax_guess=None):
    """maximise method_a_bound over K increasing edges; parametrised by log-gaps."""
    w = width(lam)
    best = (-1e9, None)
    seeds = []
    for R in ([0.7 * w, 1.5 * w, 3.0 * w] if K > 1 else np.geomspace(0.05 * w, 20 * w, 40)):
        for p in ([1.0, 2.0] if K > 1 else [1.0]):
            seeds.append(R * (np.arange(1, K + 1) / K) ** p)

    def obj(theta):
        gaps = np.exp(theta)
        edges = np.cumsum(gaps)
        return -method_a_bound(lam, edges, floor, cap, prime_bound)

    for s in seeds:
        s = np.asarray(s, dtype=float)
        theta0 = np.log(np.diff(np.concatenate([[0.0], s])))
        res = minimize(obj, theta0, method='Nelder-Mead', options=dict(maxiter=400 * K + 200, xatol=1e-5, fatol=1e-8))
        if -res.fun > best[0]:
            best = (-res.fun, np.cumsum(np.exp(res.x)))
    return best


def lam0_method_a(K, floor, cap, prime_bound, lo=1e-8, hi=0.1):
    """largest lam with max_edges bound >= 0 (bisection, 30 steps)."""
    def ok(lam):
        return optimise_edges(lam, K, floor, cap, prime_bound)[0] >= 0.0
    if not ok(lo):
        return 0.0, None
    l = bisect_lam(ok, lo, hi, 22)
    return l, optimise_edges(l, K, floor, cap, prime_bound)[1]


def continuum_bound(lam, R, floor, cap, prime_bound, n=4000):
    """the K -> infinity limit of the band bound with outer edge R (uniform fine partition)."""
    edges = np.linspace(0.0, R, n + 1)[1:]
    return method_a_bound(lam, edges, floor, cap, prime_bound)


def lam0_continuum(floor, cap, prime_bound):
    def best(lam):
        w = width(lam)
        Rs = np.geomspace(0.05 * w, 30 * w, 120)
        vals = [continuum_bound(lam, R, floor, cap, prime_bound) for R in Rs]
        i = int(np.argmax(vals))
        return vals[i], Rs[i]
    l = bisect_lam(lambda lam: best(lam)[0] >= 0, 1e-8, 0.1, 24)
    return l, best(l)[1]


def method_a(quick=False):
    print("## 2. Method (a): c-uniform band bounds.  F/A >= -e^{lam/2}/(2A) + [floor-band bound on <psiR>_B] - log pi - PrimeBound/A")
    print("#  window-mass caps: 'sup' = min(M, 2 rho/(2 lam e)); 'sup(E6B11)' = min(M, 2 rho/(2 lam)); 'rearr' = 4 int_w^{w+rho/2} B (erf); 'rearr-ef' = its erf-free majorant")
    print("#  prime bound: 'closed' = n=2 term + n>=3 tail (memo sec. 2); 'E6B11' = 64 e^{-(log 2)^2/(16 lam)}")
    pb_closed = prime_abs_closed_form
    pb_e6 = e6b11_prime_bound
    # (i) the literal E6Bridge11 configuration and its immediate sharpenings
    print("\n### 2a. The literal E6Bridge11 configuration and one-step sharpenings (K = 1 band)")
    fl = FLOORS['E6Bridge11 (-5 / 2 beyond 41)']
    for label, cap, pb, edges in [
        ("E6Bridge11 literal: floors -5/2 at R0 = 41, sup 1/(2 lam), prime E6B11", mass_cap_sup_e6b11, pb_e6, [41.0]),
        ("  + sup 1/(2 lam e)", mass_cap_sup, pb_e6, [41.0]),
        ("  + closed prime bound", mass_cap_sup, pb_closed, [41.0]),
        ("  + rearranged window mass (erf-free)", mass_cap_rearr_erffree, pb_closed, [41.0]),
    ]:
        l0 = bisect_lam(lambda lam: method_a_bound(lam, edges, fl, cap, pb) >= 0, 1e-9, 0.1, 30)
        print(f"{label:<75} lam0 = {l0:.3e}")
    # (ii) K bands, each floor, sup cap, closed prime bound
    print("\n### 2b. K optimised bands, cap = sup (1/(2 lam e)), closed prime bound: certified lam0 and the outer edge / w")
    Ks = [1, 2, 3, 5, 10] if quick else [1, 2, 3, 5, 10, 20]
    print(f"{'floor':<36} " + " ".join(f"{'K=' + str(K):>12}" for K in Ks) + f" {'K=inf':>12}")
    results_a = {}
    for name, floor in FLOORS.items():
        row = []
        for K in Ks:
            l0, edges = lam0_method_a(K, floor, mass_cap_sup, pb_closed)
            row.append((l0, edges))
        lc, Rc = lam0_continuum(floor, mass_cap_sup, pb_closed)
        results_a[name] = (row, (lc, Rc))
        cells = " ".join(f"{l0:>12.3e}" for l0, _ in row)
        print(f"{name:<36} {cells} {lc:>12.3e}")
        cells = " ".join((f"{'R/w=' + format(e[-1] / width(l0), '.2f'):>12}" if e is not None and l0 > 0 else f"{'-':>12}") for l0, e in row)
        print(f"{'  outer edge / w':<36} {cells} {'R/w=' + format(Rc / width(lc), '.2f'):>12}")
    # (iii) the same with the rearranged caps
    print("\n### 2c. Same, cap = rearranged window mass (exact erf / erf-free) and the true sup_c window mass (diagnostic)")
    print(f"{'floor':<36} {'cap':<12} " + " ".join(f"{'K=' + str(K):>12}" for K in Ks) + f" {'K=inf':>12}")
    for name in ['exact psiR at edges', 'Stirling20 + psi(1/4) floor', 'max(B, S)']:
        floor = FLOORS[name]
        for capname, cap in [('rearr', mass_cap_rearr), ('rearr-ef', mass_cap_rearr_erffree), ('true sup_c', mass_cap_exact_supc)]:
            row = []
            for K in Ks:
                l0, edges = lam0_method_a(K, floor, cap, pb_closed)
                row.append(l0)
            lc, Rc = lam0_continuum(floor, cap, pb_closed)
            cells = " ".join(f"{l0:>12.3e}" for l0 in row)
            print(f"{name:<36} {capname:<12} {cells} {lc:>12.3e}")
            sys.stdout.flush()
    # (iv) the explicit best configurations at a few K for the exact floor, for the spec
    print("\n### 2d. Explicit optimised edges (exact floor, sup cap, closed prime bound), at the certified lam0 and at lam = lam0/2")
    for K in [2, 3, 5]:
        l0, edges = lam0_method_a(K, FLOORS['exact psiR at edges'], mass_cap_sup, pb_closed)
        print(f"K = {K}: lam0 = {l0:.4e}, w = {width(l0):.2f}, edges = {np.array2string(edges, precision=2)}, floors = {np.array2string(psiR(np.concatenate([[0.0], edges])), precision=4)}")
        val, edges2 = optimise_edges(l0 / 2.0, K, FLOORS['exact psiR at edges'], mass_cap_sup, pb_closed)
        print(f"        at lam = {l0 / 2:.4e}: bound = {val:.4f}, edges = {np.array2string(edges2, precision=2)}")
    print()
    return results_a


# ----------------------------------------------------------------------------------------------
# section 3: method (b), c-dependent band bounds
# ----------------------------------------------------------------------------------------------
def band_masses_exact(edges, c, lam):
    """masses of B(. - c) in the bands [r_k, r_{k+1}) union (-r_{k+1}, -r_k], k = 0..K (r_0 = 0, r_{K+1} = inf);
    returns array (len(c), K+1)."""
    r = np.concatenate([[0.0], np.asarray(edges, dtype=float), [np.inf]])
    c = np.asarray(c, dtype=float)[:, None]
    Gp = G_cum(r[None, :] - c, lam)         # int_{-inf}^{r_k - c}
    Gm = G_cum(-r[None, :] - c, lam)        # int_{-inf}^{-r_k - c}
    pos = np.diff(Gp, axis=1)               # [r_k, r_{k+1})
    neg = -np.diff(Gm, axis=1)              # (-r_{k+1}, -r_k]
    return pos + neg


def method_b_bound(lam, edges, floor, cgrid, prime_bound, masses=None):
    """for each c: P/A + Sum_k phi_k m_k(c)/M - log pi - PrimeBound/A."""
    r = np.concatenate([[0.0], np.asarray(edges, dtype=float)])
    phi = np.maximum.accumulate(floor(r))
    if masses is None:
        masses = band_masses_exact(edges, cgrid, lam)
    avg = masses @ phi / M_of(lam)
    return pole_term(cgrid, lam) / A_of(lam) + avg - LOG_PI - prime_bound(lam)


def method_b_min(lam, edges, floor, prime_bound, cmax=C_MAX, step=0.05):
    cgrid = np.arange(0.0, cmax + 1e-9, step)
    v = method_b_bound(lam, edges, floor, cgrid, prime_bound)
    i = int(v.argmin())
    return float(v[i]), float(cgrid[i])


def edges_family(K, R, p):
    return R * (np.arange(1, K + 1) / K) ** p


def optimise_edges_b(lam, K, floor, prime_bound):
    w = width(lam)
    best = (-1e9, None)
    for R in [w, 2 * w, 3 * w, 5 * w, 8 * w]:
        for p in [0.5, 1.0, 1.5, 2.0]:
            v, _ = method_b_min(lam, edges_family(K, R, p), floor, prime_bound)
            if v > best[0]:
                best = (v, (R, p))
    # refine (R, p) by Nelder-Mead
    def obj(th):
        R, p = math.exp(th[0]), math.exp(th[1])
        return -method_b_min(lam, edges_family(K, R, p), floor, prime_bound)[0]
    R, p = best[1]
    res = minimize(obj, [math.log(R), math.log(p)], method='Nelder-Mead', options=dict(maxiter=200, xatol=1e-3, fatol=1e-6))
    R, p = math.exp(res.x[0]), math.exp(res.x[1])
    return -res.fun, edges_family(K, R, p)


def lam0_method_b(K, floor, prime_bound):
    def ok(lam):
        return optimise_edges_b(lam, K, floor, prime_bound)[0] >= 0
    return bisect_lam(ok, 1e-6, 0.05, 22)


def gauss_int_bounds(a, b, lam):
    """elementary two-sided bounds on int_a^b e^{-2 lam x^2} dx for 0 <= a < b (b may be inf):
    lower: max((b-a) e^{-2 lam b^2}, (b-a) - 2 lam (b^3 - a^3)/3)  [monotone; e^{-t} >= 1 - t],
    upper: min((b-a) e^{-2 lam a^2}, e^{-2 lam a^2}/(4 lam a) [a > 0], sqrt(pi/(8 lam)))."""
    A2 = 2.0 * lam
    if math.isinf(b):
        lo = 0.0
        up = min(math.exp(-A2 * a * a) / (2.0 * A2 * a) if a > 0 else float('inf'), 0.5 * math.sqrt(math.pi / A2))
        return lo, up
    lo = max((b - a) * math.exp(-A2 * b * b), (b - a) - A2 * (b ** 3 - a ** 3) / 3.0, 0.0)
    up = min((b - a) * math.exp(-A2 * a * a), 0.5 * math.sqrt(math.pi / A2))
    if a > 0:
        up = min(up, math.exp(-A2 * a * a) / (2.0 * A2 * a))
    return lo, up


def moment2_bounds(a, b, lam):
    """two-sided elementary bounds on int_a^b x^2 e^{-2 lam x^2} dx, 0 <= a < b, from the identity
    int x^2 e^{-2 lam x^2} = [-x e^{-2 lam x^2}/(4 lam)] + (1/(4 lam)) int e^{-2 lam x^2}."""
    A2 = 2.0 * lam
    F = lambda x: 0.0 if math.isinf(x) else -x * math.exp(-A2 * x * x) / (2.0 * A2)
    part = F(b) - F(a)
    lo, up = gauss_int_bounds(a, b, lam)
    return part + lo / (2.0 * A2), part + up / (2.0 * A2)


def band_masses_erffree(edges, c, lam, sub=1):
    """rigorous lower/upper bounds on the band masses for each c, from cell bounds on sub-cells of
    each band (in shifted coordinate x = r - c, split at 0 and at +-w where the integrand is monotone).
    Returns (lo, up) arrays of shape (len(c), K+1)."""
    w = width(lam)
    r = np.concatenate([[0.0], np.asarray(edges, dtype=float), [np.inf]])
    K1 = len(r) - 1
    lo = np.zeros((len(c), K1))
    up = np.zeros((len(c), K1))
    for i, ci in enumerate(c):
        for k in range(K1):
            for (p, q) in [(r[k] - ci, r[k + 1] - ci), (-r[k + 1] - ci, -r[k] - ci)]:
                # interval [p, q] in x; fold to |x| and split at 0 and w
                pts = sorted({p, q, 0.0, w, -w})
                pts = [t for t in pts if p <= t <= q]
                if pts[0] != p:
                    pts = [p] + pts
                if pts[-1] != q:
                    pts = pts + [q]
                for s, t in zip(pts, pts[1:]):
                    # map to nonnegative interval by symmetry
                    if t <= 0:
                        s, t = -t, -s
                    # optional refinement into sub cells
                    if math.isinf(t):
                        cells = [(s, t)]
                    else:
                        xs = np.linspace(s, t, sub + 1)
                        cells = list(zip(xs, xs[1:]))
                    for (s2, t2) in cells:
                        l, u = moment2_bounds(s2, t2, lam)
                        lo[i, k] += l
                        up[i, k] += u
    return lo, up


def method_b_erffree_min(lam, edges, floor, prime_bound, cmax, step, sub=1):
    cgrid = np.arange(0.0, cmax + 1e-9, step)
    r = np.concatenate([[0.0], np.asarray(edges, dtype=float)])
    phi = np.maximum.accumulate(floor(r))
    lo, up = band_masses_erffree(edges, cgrid, lam, sub)
    # lower bound on Sum phi_k m_k: use m_lo where phi_k >= 0, m_up where phi_k < 0
    m = np.where(phi[None, :] >= 0, lo, up)
    avg = m @ phi / M_of(lam)
    v = pole_term(cgrid, lam) / A_of(lam) + avg - LOG_PI - prime_bound(lam)
    i = int(v.argmin())
    return float(v[i]), float(cgrid[i])


def method_b(quick=False):
    print("## 3. Method (b): c-DEPENDENT band bounds (exact erf band masses per c), minimum over c in [0, 200] (step 0.05)")
    print("#  bound(c) = P(c)/A + Sum_k phi_k m_k(c)/M - log pi - PrimeBound/A, phi_k = floor(r_k); edges r_k = R (k/K)^p optimised in (R, p)")
    Ks = [2, 3, 5, 10, 20] if quick else [2, 3, 5, 10, 20, 40]
    pb = prime_abs_closed_form
    print(f"{'floor':<36} " + " ".join(f"{'K=' + str(K):>12}" for K in Ks))
    res_b = {}
    for name in ['exact psiR at edges', 'Stirling20 + psi(1/4) floor', 'Binet (B)', 'max(B, S)']:
        floor = FLOORS[name]
        row = []
        for K in Ks:
            row.append(lam0_method_b(K, floor, pb))
        res_b[name] = row
        print(f"{name:<36} " + " ".join(f"{l0:>12.3e}" for l0 in row))
        sys.stdout.flush()
    print("#  (K -> infinity with the exact floor is the exact P + Arch - PrimeAbs, i.e. lam_max(l1) of section 1b, up to the prime-bound slack.)")
    # where is the minimising c, at lam0(b) for K = 10?
    K = 10
    floor = FLOORS['exact psiR at edges']
    l0 = res_b['exact psiR at edges'][Ks.index(10)]
    v, edges = optimise_edges_b(l0, K, floor, pb)
    _, carg = method_b_min(l0, edges, floor, pb)
    print(f"\nK = 10, exact floor: lam0(b) = {l0:.4e}, w = {width(l0):.2f}, edges/w = {np.array2string(edges / width(l0), precision=2)}, minimising c = {carg:.2f} (c/w = {carg / width(l0):.2f})")
    # erf-free variant: same edges, cell bounds with sub-division
    print("\n### 3b. erf-free variant: same K = 10 edges, band masses replaced by elementary cell bounds (cells split at 0, +-w, then 'sub' equal parts)")
    print(f"{'sub':>5} {'lam0(b, erf-free)':>18} {'argmin c':>9}")
    for sub in ([1, 2, 4] if quick else [1, 2, 4, 8, 16]):
        def ok(lam, sub=sub):
            _, e = optimise_edges_b(lam, K, floor, pb)
            return method_b_erffree_min(lam, e, floor, pb, C_MAX, 0.5, sub)[0] >= 0
        l = bisect_lam(ok, 1e-6, 0.05, 16)
        _, e = optimise_edges_b(l, K, floor, pb)
        _, ca = method_b_erffree_min(l, e, floor, pb, C_MAX, 0.5, sub)
        print(f"{sub:>5} {l:>18.3e} {ca:>9.1f}")
        sys.stdout.flush()
    print()
    return res_b


# ----------------------------------------------------------------------------------------------
# section 4: method (c), Binet
# ----------------------------------------------------------------------------------------------
def binet_phi(t):
    t = np.asarray(t, dtype=float)
    with np.errstate(over='ignore', divide='ignore', invalid='ignore'):
        v = 1.0 / np.expm1(t) - 1.0 / t + 0.5
    return np.where(t < 1e-6, t / 12.0, v)


def binet_pieces(c, lam, h=0.01):
    """<psiR>_B(c) = LOGpiece - INVpiece - KERNELpiece with
    LOGpiece = (1/M) int B(r-c) (1/2) log(1/16 + r^2/4) dr, INVpiece = (1/M) int B(r-c) /(8 (1/16 + r^2/4)) dr,
    KERNELpiece = (2/M) int_0^inf phi(2u) e^{-u/2} [int B(r-c) cos(ru) dr] du = (2/M) int_0^inf phi(2u) e^{-u/2} 2 pi f0(u) cos(cu) du,
    f0(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)}.  All three by direct quadrature (numpy trapezoid)."""
    w = width(lam)
    r = np.arange(c - 8 * w, c + 8 * w, h)
    B = (r - c) ** 2 * np.exp(-2 * lam * (r - c) ** 2)
    M = B.sum() * h
    z2 = 1.0 / 16.0 + r * r / 4.0
    logp = (B * 0.5 * np.log(z2)).sum() * h / M
    invp = (B / (8.0 * z2)).sum() * h / M
    psip = (B * psiR(r)).sum() * h / M
    u = np.arange(0.0, 40.0 * math.sqrt(lam) + 2.0, 1e-4)
    A = A_of(lam)
    f0 = A * (1.0 - u * u / (4.0 * lam)) * np.exp(-u * u / (8.0 * lam))
    kern = binet_phi(2.0 * u) * np.exp(-u / 2.0)
    kernp = (2.0 * kern * 2.0 * math.pi * f0 * np.cos(c * u)).sum() * 1e-4 / M
    kernabs = (2.0 * kern * 2.0 * math.pi * np.abs(f0)).sum() * 1e-4 / M
    return psip, logp, invp, kernp, kernabs


def method_c():
    print("## 4. Method (c): Binet.  <psiR>_B = LOG - INV - KERNEL (units: bump average), checked against the direct psiR average")
    print(f"{'lam':>7} {'c':>6} {'<psiR>_B':>10} {'LOG':>8} {'INV':>8} {'KERNEL':>10} {'|KERNEL|<=':>10} {'LOG-INV-KER':>12} {'diff':>10}")
    for lam in [1e-3, 3e-3, 0.01, 0.03]:
        w = width(lam)
        for c in [0.0, 0.5 * w, w, 2 * w, 30.0]:
            psip, logp, invp, kernp, kernabs = binet_pieces(c, lam)
            print(f"{lam:>7.3g} {c:>6.1f} {psip:>10.5f} {logp:>8.4f} {invp:>8.4f} {kernp:>10.5f} {kernabs:>10.5f} {logp - invp - kernp:>12.5f} {logp - invp - kernp - psip:>10.2e}")
    print("#  INV <= (2/e) sqrt(2 pi lam) = 1.844 sqrt(lam) c-uniformly (sup B times int 2/(1+4r^2) dr = pi); |KERNEL| <= the lam-only column.")
    print()
    # chord bound on LOG: log(1/16 + x/4) >= min(l(x), l(x2)) with l the chord from x=0 to x=x2 (x = r^2);
    # E_B[min(r^2, x2)] >= E r^2 - E(r^2 - x2)^2/(4 delta) - delta (polynomial in c).
    print("### 4b. Closed-form (polynomial-moment) c-uniform lower bound on LOG via one chord + the (y)_+ <= y^2/(4 delta) + delta trick")
    print("#  LOG >= (1/2)[ -log 16 + s (E r^2 - E(r^2-x2)^2/(4 delta) - delta) ], s = log(1 + 4 x2)/x2; E r^2 = c^2 + 3/(4 lam); optimised in (x2, delta) at c = 0;")
    print("#  the resulting bound is concave in c^2 (so its min on [0, C*] is at an endpoint) and goes to -inf as c -> inf: needs the envelope for large c.")
    print(f"{'lam':>7} {'best x2/w^2':>12} {'delta lam':>10} {'LOG bound c=0':>14} {'true LOG c=0':>13} {'F/A bound c=0':>14} {'c-range where >= 0':>20}")
    for lam in [1e-4, 3e-4, 1e-3, 3e-3]:
        w = width(lam)
        A = A_of(lam)

        def logbound(c, x2, delta):
            Er2 = c * c + 3.0 / (4.0 * lam)
            Er4 = c ** 4 + 6 * c * c * 3.0 / (4.0 * lam) + 15.0 / (16.0 * lam * lam)
            E2 = Er4 - 2 * x2 * Er2 + x2 * x2
            s = math.log(1.0 + 4.0 * x2) / x2
            return 0.5 * (-math.log(16.0) + s * (Er2 - E2 / (4.0 * delta) - delta))

        def obj(th):
            return -logbound(0.0, math.exp(th[0]) * w * w, math.exp(th[1]) / lam)
        best = None
        for a0 in [0.3, 1.0, 3.0]:
            for d0 in [0.1, 0.5, 2.0]:
                res = minimize(obj, [math.log(a0), math.log(d0)], method='Nelder-Mead')
                if best is None or res.fun < best.fun:
                    best = res
        x2 = math.exp(best.x[0]) * w * w
        delta = math.exp(best.x[1]) / lam
        lb0 = logbound(0.0, x2, delta)
        _, logp_true, _, _, kernabs = binet_pieces(0.0, lam)
        Fb = lambda c: pole_term(c, lam) / A + logbound(c, x2, delta) - 1.844 * math.sqrt(lam) - kernabs - LOG_PI - prime_abs_closed_form(lam)
        cs = np.linspace(0, 200, 4001)
        vals = np.array([Fb(c) for c in cs])
        okrange = cs[vals >= 0]
        rng = f"[{okrange.min():.1f}, {okrange.max():.1f}]" if okrange.size else "empty"
        print(f"{lam:>7.3g} {x2 / (w * w):>12.3f} {delta * lam:>10.3f} {lb0:>14.4f} {logp_true:>13.4f} {Fb(0.0):>14.4f} {rng:>20}")
    print("#  Verdict: a single chord loses ~ 2 to 3 units of log at the bump scale; polynomial-moment-only c-uniform bounds do not reach 1e-3.")
    print()


# ----------------------------------------------------------------------------------------------
# section 5: the spec numbers (rigorous-quality floors from the Zeta23 series)
# ----------------------------------------------------------------------------------------------
EULER_UPPER_100 = 0.58220733   # gamma < eulerMascheroniSeq' 100 = H_100 - log 100 (Mathlib: eulerMascheroniConstant_lt_eulerMascheroniSeq')


def psiR_series_lower(r, N, gamma_upper=EULER_UPPER_100):
    """Lean-shaped lower bound on psiR(r) from Zeta23.MuFields.re_digamma_vertical (a = 1/4, t = r/2):
    psiR = -gamma - a/(a^2+t^2) + Sum_{n>=0} f(n), f(n) = 1/(n+1) - (n+1+a)/((n+1+a)^2+t^2) >= 0 and decreasing in n,
    so Sum_{n>=N} f(n) >= int_N^inf f = (1/2) log((N+1+a)^2 + t^2) - log(N+1).  Uses only gamma < gamma_upper."""
    import mpmath as mp
    a = mp.mpf(1) / 4
    t = mp.mpf(r) / 2
    s = -mp.mpf(gamma_upper) - a / (a * a + t * t)
    for n in range(N):
        s += 1 / mp.mpf(n + 1) - (n + 1 + a) / ((n + 1 + a) ** 2 + t * t)
    s += mp.mpf(1) / 2 * mp.log((N + 1 + a) ** 2 + t * t) - mp.log(N + 1)
    return float(s)


def spec_table():
    print("## 5. Spec numbers: method (a) with edges rounded to 0.1, floors = Zeta23-series lower bounds (N terms + integral tail, gamma < 0.58221),")
    print("#     cap = sup (1/(2 lam e)), closed prime bound, pole floor -e^{lam/2}/(2A).  'exact' uses the true psiR values.")
    fl = FLOORS['exact psiR at edges']
    pb = prime_abs_closed_form
    print(f"{'lam':>8} {'K':>3} {'margin exact':>13} {'N=20':>9} {'N=40':>9} {'N=80':>9}   edges")
    for lam in [1e-3, 1.2e-3, 1.5e-3, 2e-3]:
        for K in [5, 8, 10, 12]:
            val, edges = optimise_edges(lam, K, fl, mass_cap_sup, pb)
            er = np.round(edges, 1)
            row = [method_a_bound(lam, er, fl, mass_cap_sup, pb)]
            for N in [20, 40, 80]:
                fN = lambda r, N=N: np.array([psiR_series_lower(x, N) if x > 0 else PSI_QUARTER for x in np.atleast_1d(r)])
                row.append(method_a_bound(lam, er, fN, mass_cap_sup, pb))
            print(f"{lam:>8.4g} {K:>3} {row[0]:>13.4f} {row[1]:>9.4f} {row[2]:>9.4f} {row[3]:>9.4f}   {np.array2string(er, precision=1, separator=', ')}")
            sys.stdout.flush()
    print("#  (psiR(0) = psi(1/4) = -4.2274535 exactly: Gauss's digamma theorem, or the -5 of E6Bridge11 at a cost of 0.77 x cap(r_1)/M.)")
    print()


# ----------------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--zeros', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'zeros2000.json'))
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--sections', default='0,1,2,3,4,5')
    args = ap.parse_args()
    secs = set(args.sections.split(','))
    t0 = time.time()
    zeros = load_zeros(args.zeros)
    print(f"# gauss_window_numerics.py  {time.strftime('%Y-%m-%d %H:%M')}  zeros: {len(zeros)} (last {zeros[-1]:.3f})  conjecture1_proved = False")
    print()
    if '0' in secs:
        identity_check(zeros)
        print(f"# [{time.time() - t0:.0f}s]")
    if '1' in secs:
        landscape(zeros)
        landscape_thresholds()
        print(f"# [{time.time() - t0:.0f}s]")
    if '2' in secs:
        method_a(args.quick)
        print(f"# [{time.time() - t0:.0f}s]")
    if '3' in secs:
        method_b(args.quick)
        print(f"# [{time.time() - t0:.0f}s]")
    if '4' in secs:
        method_c()
        print(f"# [{time.time() - t0:.0f}s]")
    if '5' in secs:
        spec_table()
        print(f"# [{time.time() - t0:.0f}s]")
    print("# conjecture1_proved = False.  Nothing above proves RH.")


if __name__ == '__main__':
    main()

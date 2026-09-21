#!/usr/bin/env python3
"""seam_b_small_lam.py -- numerics for the Wall's small-width seam (seam B, 2026-09-21).

The two-parameter Wall functional (zero side)

    F(c, lam) = Re sum_rho m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2),
    gamma_rho = (rho - 1/2)/i,

equals, by the explicit formula for the Gaussian-derivative test phi(u) = K u e^{-u^2/(4 lam)} e^{-icu}
with f = phi * phi~ (E6Bridge5 autocorr),

    F(c, lam) = arch(c, lam) - prime(c, lam),

    f(u)          = A (1 - u^2/(4 lam)) exp(-u^2/(8 lam)) exp(-i c u),   A = 1/(8 sqrt(2 pi) lam^{3/2}),
    prime(c, lam) = sum_{n >= 2} Lambda(n) n^{-1/2} (f(log n) + f(-log n)),
    arch(c, lam)  = G(i/2) + G(-i/2) - f(0) log pi + (1/2pi) int B(r) Re psi(1/4 + i r/2) dr,
    G(z)          = (z - c)^2 exp(-2 lam (z - c)^2),   B(r) = G(r) = (r - c)^2 exp(-2 lam (r - c)^2).

This script tabulates arch, prime and F over a grid of centres c and widths lam through the prime
side (mpmath quadrature for the archimedean integral, the Lambda-sum cut at the Gaussian tail), and
cross-checks against the zero side using the first N zeros (mpmath.zetazero) plus a density tail
estimate for the mass of B beyond the last computed zero.  It also reports the c-uniform lower
bound of the paper analysis.  Nothing here proves anything; conjecture1_proved = False.

Usage:  PYTHONPATH=telperion/src python3 seam_b_small_lam.py [--zeros N] [--cache FILE]
"""
import argparse
import json
import math
import os
import sys
import tempfile
import time

import mpmath as mp

mp.mp.dps = 20


def A_of(lam):
    return 1 / (8 * mp.sqrt(2 * mp.pi) * lam ** mp.mpf(1.5))


def f_pair(u, c, lam):
    """f(u) + f(-u), real: 2 A (1 - u^2/(4 lam)) exp(-u^2/(8 lam)) cos(c u)."""
    return 2 * A_of(lam) * (1 - u * u / (4 * lam)) * mp.exp(-u * u / (8 * lam)) * mp.cos(c * u)


def von_mangoldt_table(N):
    """Lambda(n) for 2 <= n <= N by a sieve of smallest prime factors."""
    spf = list(range(N + 1))
    for i in range(2, int(N ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
    lam_tab = {}
    for n in range(2, N + 1):
        p = spf[n]
        m = n
        while m % p == 0:
            m //= p
        if m == 1:
            lam_tab[n] = mp.log(p)
    return lam_tab


def prime_side(c, lam, table):
    """sum_{n>=2} Lambda(n)/sqrt(n) (f(log n) + f(-log n)); the Gaussian factor is
    exp(-(log n)^2/(8 lam)) so n beyond exp(sqrt(8 lam * 80)) contributes < e^{-80} relative."""
    total = mp.mpf(0)
    for n, L in table.items():
        u = mp.log(n)
        if u * u / (8 * lam) > 80:
            continue
        total += L / mp.sqrt(n) * f_pair(u, c, lam)
    return total


def prime_tail_estimate(c, lam, N):
    """Heuristic size of the prime sum beyond n = N: with Lambda(n) of mean 1 (PNT) the tail is
    ~ int_N^inf f_pair(log x) x^{-1/2} dx = int_{log N}^inf f_pair(u) e^{u/2} du, taken in absolute
    value of the integrand (no cancellation credited).  This is an ERROR BAR on the prime column,
    not a bound: for lam >= 0.5 and c near 0 it exceeds the true |F| (which is ~ 2 gamma_1^2
    exp(-2 lam gamma_1^2) ~ 0), so those rows read as 0 within the bar."""
    A = A_of(lam)
    return mp.quad(lambda u: 2 * A * abs(1 - u * u / (4 * lam)) * mp.exp(-u * u / (8 * lam)) * mp.exp(u / 2),
                   [mp.log(N), mp.log(N) + 20 * mp.sqrt(lam) + 5])


def G(z, c, lam):
    return (z - c) ** 2 * mp.exp(-2 * lam * (z - c) ** 2)


def arch_side(c, lam):
    A = A_of(lam)
    poles = 2 * mp.re(G(mp.mpc(0, 0.5), c, lam))
    log_pi_term = -A * mp.log(mp.pi)

    def integrand(r):
        return G(r, c, lam) * mp.re(mp.digamma(mp.mpc(0.25, r / 2)))

    w = 1 / mp.sqrt(2 * lam)          # bump width in r
    L = 7 * w                         # Gaussian tail e^{-49} beyond
    pts = sorted({c - L, c - 3 * w, c - w, c, c + w, c + 3 * w, c + L, mp.mpf(-5), mp.mpf(0), mp.mpf(5)})
    pts = [p for p in pts if c - L <= p <= c + L]
    integ = mp.quad(integrand, pts)
    return poles + log_pi_term + integ / (2 * mp.pi), poles, log_pi_term, integ / (2 * mp.pi)


def load_zeros(N, cache):
    zeros = []
    if cache and os.path.exists(cache):
        with open(cache) as fh:
            zeros = [mp.mpf(x) for x in json.load(fh)]
    if len(zeros) < N:
        t0 = time.time()
        for k in range(len(zeros) + 1, N + 1):
            zeros.append(mp.im(mp.zetazero(k)))
            if k % 100 == 0:
                print(f"  zero {k}: {zeros[-1]}  ({time.time() - t0:.0f}s)", file=sys.stderr)
                if cache:
                    with open(cache, "w") as fh:
                        json.dump([str(z) for z in zeros], fh)
        if cache:
            with open(cache, "w") as fh:
                json.dump([str(z) for z in zeros], fh)
    return zeros[:N]


def zero_side(c, lam, zeros):
    """Zero side with the first len(zeros) zeros (both conjugate pairs +-gamma, all simple, on the
    line as verified numerically) plus a smooth tail estimate: mass of B beyond gamma_N via the
    Riemann--von Mangoldt density (1/2pi) log(r/2pi) dr, and its mirror at -gamma_N."""
    s = mp.mpf(0)
    for g in zeros:
        s += G(g, c, lam) + G(-g, c, lam)
    T = zeros[-1]

    def dens(r):
        return G(r, c, lam) * mp.log(abs(r) / (2 * mp.pi)) / (2 * mp.pi)

    w = 1 / mp.sqrt(2 * lam)
    tail = mp.mpf(0)
    if c + 7 * w > T:
        tail += mp.quad(dens, [T, max(T, c + 7 * w)])
    if c - 7 * w < -T:
        tail += mp.quad(dens, [min(-T, c - 7 * w), -T])
    return mp.re(s), tail


def lower_bound_constants():
    """The c-uniform lower bound of the memo (threshold 2 on Re psi beyond R0 = 2 e^3):
    F/A >= (2 - log pi) - 4 e^{2 lam} sqrt(32 pi lam) - 32 e^{-(log 2)^2/(16 lam)}
           - 7 R0 * 8 sqrt(2 pi) sqrt(lam) / (2 pi).
    Returns the largest lam on a fine grid at which the bound is nonnegative."""
    R0 = mp.mpf(41)   # E6Bridge11.R₀: Re psi(1/4 + i r/2) >= 2 for |r| >= 41 (Stirling)

    def rhs(lam):
        return (2 - mp.log(mp.pi)) - 4 * mp.exp(2 * lam) * mp.sqrt(32 * mp.pi * lam) \
            - 64 * mp.exp(-(mp.log(2)) ** 2 / (16 * lam)) - 7 * R0 * 8 * mp.sqrt(2 * mp.pi) * mp.sqrt(lam) / (2 * mp.pi)

    lo, hi = mp.mpf('1e-12'), mp.mpf(1)
    for _ in range(80):
        mid = mp.sqrt(lo * hi)
        if rhs(mid) >= 0:
            lo = mid
        else:
            hi = mid
    return lo, rhs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--zeros", type=int, default=2000)
    ap.add_argument("--cache", default=os.path.join(tempfile.gettempdir(), "seam_b_zeros.json"))
    ap.add_argument("--centers", default="0,1,14.134725,50,1000,10000,100000")
    ap.add_argument("--lams", default="0.005,0.01,0.02,0.05,0.1,0.2,0.5,1")
    ap.add_argument("--no-zero-side", action="store_true")
    ap.add_argument("--dps", type=int, default=20, help="mpmath working precision (digits)")
    args = ap.parse_args()
    mp.mp.dps = args.dps

    centers = [mp.mpf(x) for x in args.centers.split(",")]
    lams = [mp.mpf(x) for x in args.lams.split(",")]

    # Lambda table: n up to exp(sqrt(80 * 8 * lam_max)) = exp(sqrt(640)) ~ e^25 is far too big for
    # lam = 1; the prime sum is only needed where the Gaussian factor is non-negligible, and for
    # lam <= 1 the relative size at n = N is exp(-(log N)^2/8).  N = 10^6 gives e^{-23.9}.
    N = 10 ** 6
    print(f"# sieving Lambda(n), n <= {N}", file=sys.stderr)
    table = von_mangoldt_table(N)

    zeros = None
    if not args.no_zero_side:
        print(f"# loading {args.zeros} zeros", file=sys.stderr)
        zeros = load_zeros(args.zeros, args.cache)
        print(f"# last zero gamma_{len(zeros)} = {zeros[-1]}", file=sys.stderr)

    lam0, rhs = lower_bound_constants()
    print(f"# Lean lower bound (E6Bridge11.re_weilForm_gauss_nonneg): F/A >= (2 - log pi) - 4 e^{{2 lam}} sqrt(32 pi lam) - 64 e^{{-(log 2)^2/(16 lam)}} - 7 R0 8 sqrt(2 pi) sqrt(lam)/(2 pi), R0 = 41")
    print(f"# nonnegative for lam <= {mp.nstr(lam0, 6)} (absolute, c-uniform); the Lean file certifies lam0 = 1e-7 with cruder numerics")
    print()
    hdr = f"{'c':>10} {'lam':>7} {'A':>12} {'arch':>14} {'poles':>12} {'-f0logpi':>12} {'psi-int':>14} {'prime':>14} {'ptail-bar':>10} {'F=arch-prime':>14} {'F/A':>10}"
    if zeros is not None:
        hdr += f" {'zeroside(N)':>14} {'tail':>12} {'zs+tail':>14} {'rel.diff':>10}"
    print(hdr)
    for c in centers:
        for lam in lams:
            A = A_of(lam)
            arch, poles, lp, psi = arch_side(c, lam)
            prime = prime_side(c, lam, table)
            ptail = prime_tail_estimate(c, lam, N)
            F = arch - prime
            if abs(poles) < mp.mpf('1e-300'):
                poles = mp.mpf(0)
            row = f"{mp.nstr(c, 8):>10} {mp.nstr(lam, 4):>7} {mp.nstr(A, 6):>12} {mp.nstr(arch, 8):>14} {mp.nstr(poles, 6):>12} {mp.nstr(lp, 6):>12} {mp.nstr(psi, 8):>14} {mp.nstr(prime, 8):>14} {mp.nstr(ptail, 3):>10} {mp.nstr(F, 8):>14} {mp.nstr(F / A, 6):>10}"
            if zeros is not None:
                zs, tail = zero_side(c, lam, zeros)
                tot = zs + tail
                rel = (tot - F) / F if F != 0 else mp.mpf('nan')
                row += f" {mp.nstr(zs, 8):>14} {mp.nstr(tail, 6):>12} {mp.nstr(tot, 8):>14} {mp.nstr(rel, 4):>10}"
            print(row)
            sys.stdout.flush()


if __name__ == "__main__":
    main()

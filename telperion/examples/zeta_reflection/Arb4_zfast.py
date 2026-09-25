"""Arb4_zfast.py -- lane Arb4: a fast float64 Riemann-Siegel Z(t) (main sum + the C0 correction) for
PLACING grid points only.

Nothing computed here is trusted: the kernel re-derives the sign of every grid point it is given
(`Arb4.ptCheckC`, `H1000Line.ptCheck` mirror in emit_h1000_line.pt_check), and the zero COUNT of every
band comes from the zeta_zero_localization band plan (Turing's method), not from this file.  A
misplaced point only makes the Python mirror refuse it (the planner then tries the next candidate).

  Z(t) = 2 sum_{n <= m} n^(-1/2) cos(theta(t) - t log n) + (-1)^(m-1) (t/2 pi)^(-1/4) C0(p) + O(t^(-5/4)),
  m = floor(sqrt(t / 2 pi)), p = frac(sqrt(t / 2 pi)), C0(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p),
  theta(t) = (t/2) log(t / 2 pi) - t/2 - pi/8 + 1/(48 t) + 7/(5760 t^3).

zeros_between(a, b, n): the n zeros of Z in [a, b] by sign changes on a grid (refined until the count
matches the band plan's n; RuntimeError otherwise).  conjecture1_proved = False.
"""
import math

import numpy as np

TWO_PI = 2.0 * math.pi


def theta(t):
    t = np.asarray(t, dtype=np.float64)
    return t / 2.0 * np.log(t / TWO_PI) - t / 2.0 - math.pi / 8.0 + 1.0 / (48.0 * t) + 7.0 / (5760.0 * t ** 3)


def Z(t):
    """Riemann-Siegel Z at an array of heights t >= 200 (float64, error about 1e-5 or better)."""
    t = np.atleast_1d(np.asarray(t, dtype=np.float64))
    out = np.empty_like(t)
    s = np.sqrt(t / TWO_PI)
    m = np.floor(s).astype(np.int64)
    th = theta(t)
    # group by m (constant on long runs of a sorted grid)
    order = np.argsort(m, kind="stable")
    ms = m[order]
    cut = np.flatnonzero(np.diff(ms)) + 1
    for grp in np.split(order, cut):
        mm = int(m[grp[0]])
        n = np.arange(1, mm + 1, dtype=np.float64)
        tt = t[grp][:, None]
        main = 2.0 * np.sum(np.cos(th[grp][:, None] - tt * np.log(n)[None, :]) / np.sqrt(n)[None, :], axis=1)
        p = s[grp] - mm
        c0 = np.cos(TWO_PI * (p * p - p - 1.0 / 16.0)) / np.cos(TWO_PI * p)
        out[grp] = main + (-1) ** (mm - 1) * (t[grp] / TWO_PI) ** (-0.25) * c0
    return out


def zeros_between(a, b, n, h=0.01, max_refine=4):
    """the n zeros of Z in [a, b] (sign changes on a grid of step h, refined 10x up to max_refine
    times until exactly n are found)."""
    for _ in range(max_refine):
        k = int(math.ceil((b - a) / h))
        ts = np.linspace(a, b, k + 1)
        zs = Z(ts)
        idx = np.flatnonzero(np.sign(zs[:-1]) * np.sign(zs[1:]) < 0)
        if len(idx) == n:
            roots = []
            for i in idx:
                lo, hi = ts[i], ts[i + 1]
                zl = zs[i]
                for _ in range(40):
                    mid = 0.5 * (lo + hi)
                    zm = Z(np.array([mid]))[0]
                    if np.sign(zm) == np.sign(zl):
                        lo, zl = mid, zm
                    else:
                        hi = mid
                roots.append(0.5 * (lo + hi))
            return roots, ts, zs
        h /= 10.0
    raise RuntimeError("zeros_between(%g, %g): %d sign changes, band plan says %d" % (a, b, len(idx), n))

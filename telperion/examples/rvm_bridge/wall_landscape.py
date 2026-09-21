#!/usr/bin/env python3
"""Landscape of the two-parameter Wall F(c, lam) and the bandwidth barrier (2026-09-21).

Vocabulary (Zeta23.Defs / E6Bridge6, same as phase0_gaussian_obligations.py):
    paperFT g z       = int g(u) exp(i z u) du
    gammaOf rho       = (rho - 1/2)/i ;  rho = beta + i t  ->  gamma = t + i (1/2 - beta)
    gaussTest c lam z = (z - c)^2 exp(-2 lam (z - c)^2)                      =: G(z)
    F(c, lam)         = Re sum_rho m(rho) G(gammaOf rho)  over ALL nontrivial zeros (both rho and conj rho)

Explicit formula (Weil, zeta; h = G, g = f the paperFT-inverse of G):
    F = pole + psi - f(0) log pi - prime
    pole  = G(i/2) + G(-i/2) = 2 Re G(i/2)
    psi   = (1/2pi) int G(r) Re digamma(1/4 + i r/2) dr
    prime = sum_n Lambda(n) n^{-1/2} (f(log n) + f(-log n))
Closed form of f = phi * phi~ (phi(u) = K u e^{-u^2/(4 lam)} e^{-i c u}, K = -i/(4 sqrt(pi) lam^{3/2})):
    f(u) = e^{-i c u} f0(u),   f0(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)},   A = f(0) = 1/(8 sqrt(2 pi) lam^{3/2})
so prime = 2 sum_n Lambda(n) n^{-1/2} cos(c log n) f0(log n).  Verified below against direct convolution and
against paperFT.

Everything here MEASURES.  Zeros are the real ones (on the line to working precision); nothing is claimed
about the true zero set beyond the computed windows.  conjecture1_proved = False.

Usage: python3 wall_landscape.py [--quick] [--nmax 100000000]
"""
import argparse
import json
import math
import os
import sys
import time

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad as squad
from scipy.special import digamma

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from phase0_gaussian_obligations import load_zeros  # noqa: E402  (zero cache, quadruple conventions)

SCRATCH = os.environ.get(
    "WALL_SCRATCH",
    "/private/tmp/claude-0/-Users-peterwmurphy/466d3ce5-8284-473c-b6b0-031627e4571a/scratchpad/wall")
os.makedirs(SCRATCH, exist_ok=True)

CS = [0.0, 5.0, 14.1347, 20.0, 50.0, 100.0, 500.0, 1000.0, 5000.0, 1e4]
LAMS = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1, 2, 5, 10, 20, 50]
WINDOW = 120.0   # zeros within +-WINDOW of c are used on the zero side; the rest is bounded analytically
LOG_ZERO_TAIL = 46.0


# ----------------------------------------------------------------------------- closed forms
def A_of(lam):
    return 1.0 / (8.0 * math.sqrt(2.0 * math.pi) * lam ** 1.5)


def f0(u, lam):
    u = np.asarray(u, dtype=float)
    return A_of(lam) * (1.0 - u * u / (4.0 * lam)) * np.exp(-u * u / (8.0 * lam))


def G(z, c, lam):
    w = np.asarray(z) - c
    return w * w * np.exp(-2.0 * lam * w * w)


def pole_term(c, lam):
    return 2.0 * G(0.5j, c, lam).real


def psi_term(c, lam, n=32):
    """(1/2pi) int G(r) Re digamma(1/4 + i r/2) dr: composite Gauss-Legendre on [c-R, c+R], panels of width <= 1
    (digamma(1/4 + i r/2) has poles at r = i(2k + 1/2), 0.5 off the real axis, so wide panels near r = 0 lose digits)."""
    R = math.sqrt(LOG_ZERO_TAIL / (2.0 * lam))
    npan = max(8, int(math.ceil(2.0 * R)))
    edges = np.linspace(c - R, c + R, npan + 1)
    x, w = leggauss(n)
    a, b = edges[:-1], edges[1:]
    r = (0.5 * (b - a))[:, None] * x[None, :] + (0.5 * (a + b))[:, None]
    vals = G(r, c, lam) * digamma(0.25 + 0.5j * r).real
    val = ((vals * w[None, :]).sum(axis=1) * 0.5 * (b - a)).sum()
    return val / (2.0 * math.pi)


def verify_closed_forms():
    """f0 vs direct convolution phi * phi~, and paperFT f vs G (mpmath, 3 points each)."""
    import mpmath as mp
    mp.mp.dps = 25
    worst_conv = 0.0
    worst_ft = 0.0
    for lam in (0.5, 1.0, 10.0):
        for c in (0.0, 50.0):
            K = 1.0 / (4.0 * math.sqrt(math.pi) * lam ** 1.5)     # |K|; the phase -i cancels in phi * phi~
            for u in (0.0, 0.5, 1.0, 2.5):
                R = 12.0 * math.sqrt(lam) + abs(u) + 5.0
                v = np.linspace(-R, R, 200001)
                dv = v[1] - v[0]
                conv = (K * K * v * (v - u) * np.exp(-(v * v + (v - u) ** 2) / (4.0 * lam))).sum() * dv
                conv = conv * np.exp(-1j * c * u)
                ex = np.exp(-1j * c * u) * f0(u, lam)
                worst_conv = max(worst_conv, abs(conv - ex))
            for z in (mp.mpc(c, 0), mp.mpc(c + 0.7, 0.5), mp.mpc(c - 1.3, -0.5)):
                Am = 1 / (8 * mp.sqrt(2 * mp.pi) * mp.mpf(lam) ** mp.mpf(1.5))
                fm = lambda uu: Am * (1 - uu * uu / (4 * lam)) * mp.exp(-uu * uu / (8 * lam)) * mp.exp(-1j * c * uu) * mp.exp(1j * z * uu)
                Ru = 4 * lam + math.sqrt(320 * lam) + 10
                val = mp.quad(fm, mp.linspace(-Ru, Ru, 81))
                ex = (z - c) ** 2 * mp.exp(-2 * lam * (z - c) ** 2)
                worst_ft = max(worst_ft, float(abs(val - ex)))
    return worst_conv, worst_ft


# ----------------------------------------------------------------------------- zeros
def zero_windows(first, window10000):
    """Return dict c -> ordinates within +-WINDOW of c (t > 0 only; the -t images are added in F_zero)."""
    out = {}
    for c in CS:
        if c <= 1000.0:
            src = first
        elif c == 1e4:
            src = window10000
        else:
            src = load_window(c)
        if c <= 1000.0:
            sel = src[src <= c + WINDOW]   # keep everything below c too (cheap; matters only for c near 0)
        else:
            sel = src[np.abs(src - c) <= WINDOW]
        out[c] = sel
    return out


def load_window(c):
    path = os.path.join(SCRATCH, f"zeros_window_{int(c)}.json")
    if os.path.exists(path):
        with open(path) as fh:
            return np.array(json.load(fh)["t"])
    import flint

    def NT(T):
        return T / (2 * math.pi) * math.log(T / (2 * math.pi * math.e)) + 7.0 / 8.0

    n_lo = max(1, int(NT(c - WINDOW - 10)) - 5)
    n_hi = int(NT(c + WINDOW + 10)) + 5
    zs = flint.acb.zeta_zeros(n_lo, n_hi - n_lo + 1)
    t = np.array([float(z.imag.mid()) for z in zs])
    offline = max(abs(float(z.real.mid()) - 0.5) for z in zs)
    assert t[0] < c - WINDOW and t[-1] > c + WINDOW, (t[0], t[-1])
    with open(path, "w") as fh:
        json.dump({"t": t.tolist(), "n_lo": n_lo, "n_hi": n_hi, "max_offline": offline}, fh)
    return t


def F_zero(c, lam, t):
    """Re sum over images +t and -t of G (all on the line)."""
    return float(G(t, c, lam).sum() + G(-t, c, lam).sum())


def zero_tail_bound(c, lam, t):
    """Bound on on-line images outside the used window: crude density (log(T/2pi)/2pi + 1) times the Gaussian tail."""
    X = min(abs(t.max() - c), abs(c - t.min())) if c > 1000.0 else abs(t.max() - c)
    T = max(t.max(), 20.0)
    dens = math.log(T / (2 * math.pi)) / (2 * math.pi) + 1.0
    integral = X * math.exp(-2 * lam * X * X) / (4 * lam) + math.sqrt(math.pi / (2 * lam)) * math.erfc(X * math.sqrt(2 * lam)) / (8 * lam)
    return 2 * dens * integral, X


# ----------------------------------------------------------------------------- primes
def von_mangoldt(nmax):
    """Prime powers n <= nmax with Lambda(n), as (n float64, Lambda float64), n ascending."""
    t = time.time()
    sieve = np.ones(nmax + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(nmax ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    primes = np.nonzero(sieve)[0]
    del sieve
    ns = [primes.astype(np.float64)]
    ls = [np.log(primes)]
    for p in primes[primes <= int(nmax ** 0.5)]:
        q = int(p) * int(p)
        lp = math.log(p)
        while q <= nmax:
            ns.append(np.array([q], dtype=np.float64))
            ls.append(np.array([lp]))
            q *= int(p)
    n = np.concatenate(ns)
    L = np.concatenate(ls)
    order = np.argsort(n)
    n, L = n[order], L[order]
    return n, L, time.time() - t


class PrimeSide:
    def __init__(self, nmax):
        self.n, self.L, self.secs = von_mangoldt(nmax)
        self.logn = np.log(self.n)
        self.wt = self.L / np.sqrt(self.n)
        self.nmax = nmax

    def u_cut(self, lam, L=50.0):
        return 2.0 * lam + math.sqrt(8.0 * lam * L) + 1.0

    def prime_sum(self, c, lam):
        """2 sum Lambda(n) n^{-1/2} cos(c log n) f0(log n) over n <= N_used; returns (value, N_used, tail_bound)."""
        ucut = self.u_cut(lam)
        k = int(np.searchsorted(self.logn, ucut))
        u = self.logn[:k]
        val = 2.0 * (self.wt[:k] * np.cos(c * u) * f0(u, lam)).sum()
        N_used = min(math.exp(ucut), float(self.nmax))
        return float(val), N_used, prime_tail_bound(N_used, lam)


def prime_tail_bound(N, lam):
    """Rigorous-ish bound on 2 sum_{n>N} Lambda(n) n^{-1/2} |f0(log n)|.

    Abel summation with psi(x) <= 1.04 x (all x) and psi(N) >= 0.998 N for N >= 1.32e6 (Rosser-Schoenfeld),
    W(x) = x^{-1/2} 2 |f0(log x)| decreasing for log x >= 4.
    """
    A = A_of(lam)

    def Wu(u):   # W(e^u) e^u  (integrand in u)
        return 2.0 * A * abs(1.0 - u * u / (4.0 * lam)) * math.exp(-u * u / (8.0 * lam) + 0.5 * u)

    u0 = math.log(N)
    up = 2.0 * lam
    pts = [u0] + [x for x in (up, up + math.sqrt(8 * lam), up + 2 * math.sqrt(8 * lam)) if x > u0]
    integral = 0.0
    for a, b in zip(pts, pts[1:]):
        integral += squad(Wu, a, b, limit=200)[0]
    integral += squad(Wu, pts[-1], pts[-1] + 12 * math.sqrt(8 * lam) + 40, limit=200)[0]
    boundary = (1.04 - (0.998 if N >= 1.32e6 else 0.0)) * Wu(u0)
    return 1.04 * integral + boundary


def N_cutoff(lam, eps):
    """Smallest N with prime_tail_bound(N, lam) <= eps * f(0): the exact Gaussian cutoff.  Returns log N."""
    target = eps * A_of(lam)
    lo, hi = 4.0, 2.0 * lam + math.sqrt(8.0 * lam * (math.log(1 / eps) + 60.0)) + 20.0
    if prime_tail_bound(math.exp(lo), lam) <= target:
        return lo
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if prime_tail_bound(math.exp(mid), lam) <= target:
            hi = mid
        else:
            lo = mid
    return hi


# ----------------------------------------------------------------------------- Task 1
def task1(zw, first, ps, out, quick):
    print("\n" + "=" * 100)
    print("TASK 1: landscape F(c, lam) = pole + psi - f(0) log pi - prime  vs  zero side")
    print("=" * 100)
    print("zero side: cached zeros within the window (+-%g) both images, tail bounded; 'ztail' = that bound." % WINDOW)
    print("prime: DIRECT sum over prime powers n <= N_used when the tail bound ptail <= 1e-3 f(0) (else the entry is")
    print("       INFERRED = arch - F_zero and marked '*'); 'diff' = F_zero - (arch - prime_direct) when direct.")
    rows = {}
    hdr = f"{'c':>8} {'lam':>6} | {'F_zero':>11} {'ztail':>8} | {'pole':>11} {'psi':>11} {'-f0logpi':>11} {'arch':>11} | {'prime':>12} {'N_used':>8} {'ptail':>8} | {'diff':>9} {'rel':>8}"
    print(hdr)
    for c in CS:
        t = zw[c]
        for lam in LAMS:
            Fz = F_zero(c, lam, t)
            ztail, _ = zero_tail_bound(c, lam, t)
            pole = pole_term(c, lam)
            psi = psi_term(c, lam)
            f0lp = -A_of(lam) * math.log(math.pi)
            arch = pole + psi + f0lp
            pv, N_used, ptail = ps.prime_sum(c, lam)
            direct = ptail <= 1e-3 * A_of(lam)
            if direct:
                Farch = arch - pv
                diff = Fz - Farch
                rel = abs(diff) / max(abs(Fz), abs(arch), 1e-300)
                prime = pv
            else:
                prime = arch - Fz
                diff = float("nan")
                rel = float("nan")
            rows[f"{c}_{lam}"] = {"c": c, "lam": lam, "F_zero": Fz, "ztail": ztail, "pole": pole, "psi": psi,
                                  "m_f0logpi": f0lp, "arch": arch, "prime": prime, "prime_direct": direct,
                                  "N_used": N_used, "ptail": ptail, "diff": diff, "rel": rel,
                                  "n_zeros_window": int(len(t))}
            mark = " " if direct else "*"
            print(f"{c:8.4f} {lam:6.3f} | {Fz:11.4e} {ztail:8.1e} | {pole:11.4e} {psi:11.4e} {f0lp:11.4e} {arch:11.4e} | "
                  f"{prime:12.4e}{mark} {N_used:8.1e} {ptail:8.1e} | " + (f"{diff:9.1e} {rel:8.1e}" if direct else f"{'(inferred)':>18}"))
    out["landscape"] = rows

    # sign check
    neg = [(r["c"], r["lam"], r["F_zero"]) for r in rows.values() if r["F_zero"] < 0]
    print(f"\nnegative F_zero cells: {len(neg)} (must be 0: every image is on the line, each term is >= 0)")
    negA = [(r["c"], r["lam"], r["arch"] - r["prime"]) for r in rows.values() if r["prime_direct"] and r["arch"] - r["prime"] < 0]
    print(f"negative arch - prime_direct cells: {len(negA)}" + ("" if not negA else f"  {negA}"))
    for c, lam, v in negA:
        r = rows[f"{c}_{lam}"]
        print(f"   c={c} lam={lam}: arch-prime={v:.3e}, F_zero={r['F_zero']:.3e}, ptail={r['ptail']:.1e}, |diff|={abs(r['diff']):.1e}"
              " -> " + ("within the prime tail bound / rounding: NOT a real negative" if abs(v) <= r["ptail"] + 1e-13 * abs(r["arch"]) else "INVESTIGATE"))
    # agreement digits
    dd = [r for r in rows.values() if r["prime_direct"]]
    print(f"direct cells: {len(dd)} / {len(rows)}; worst |diff| = {max(abs(r['diff']) for r in dd):.2e}; "
          f"worst rel (vs max(|F|,|arch|)) = {max(r['rel'] for r in dd):.2e}; "
          f"median rel = {np.median([r['rel'] for r in dd]):.1e}")
    for lam in LAMS:
        sub = [r for r in dd if r["lam"] == lam]
        if sub:
            print(f"   lam={lam:<6g}: {len(sub):2d} direct cells, worst rel {max(r['rel'] for r in sub):.1e}, N_used {sub[0]['N_used']:.1e}, ptail/f(0) {sub[0]['ptail']/A_of(lam):.1e}")

    # mechanism: |prime| / arch
    print("\nsmall-lam mechanism: |prime| / arch (direct cells only; '-' = arch <= 0, 'inf' n/a)")
    print(f"{'c':>8} | " + " ".join(f"{lam:>8g}" for lam in LAMS if lam <= 2))
    lam0 = {}
    thresholds = {}
    for c in CS:
        line = []
        first_over = {0.01: None, 0.1: None, 0.5: None}
        for lam in LAMS:
            r = rows[f"{c}_{lam}"]
            if not r["prime_direct"] or lam > 2:
                continue
            if r["arch"] <= 0:
                line.append(f"{'-':>8}")
                continue
            ratio = abs(r["prime"]) / r["arch"]
            line.append(f"{ratio:8.2e}")
            for th in first_over:
                if first_over[th] is None and ratio > th:
                    first_over[th] = lam
        # lam0(c) = sup{lam : |prime| <= arch/2 (and arch > 0) for all lam' <= lam}, on a fine log grid
        lam0[c] = lam0_of(c, ps)
        thresholds[c] = {str(k): v for k, v in first_over.items()}
        l0, lim = lam0[c]
        print(f"{c:8.4f} | " + " ".join(line) + f"   first > 1%/10%/50% of arch at lam = {first_over[0.01]}/{first_over[0.1]}/{first_over[0.5]}; "
              f"lam0(c) = {l0}" + (" (>=, feasibility-limited)" if lim else ""))
    out["lam0"] = {str(c): {"lam0": v[0], "feasibility_limited": v[1]} for c, v in lam0.items()}
    out["prime_frac_thresholds"] = {str(c): v for c, v in thresholds.items()}
    # c-uniform bound: |prime| <= 2 sum Lambda n^{-1/2} |f0(log n)| =: P_abs(lam), independent of c
    print("\nc-uniform envelope: |prime(c,lam)| <= P_abs(lam) := 2 sum Lambda(n) n^{-1/2} |f0(log n)| for every c;")
    print("arch(c,lam) ~ f(0) (log(c/2pi) + o(1)) for c >> 1.  P_abs/f(0) and the c needed for arch/2 >= P_abs:")
    env = {}
    for lam in [l for l in LAMS if l <= 2]:
        ucut = ps.u_cut(lam)
        k = int(np.searchsorted(ps.logn, ucut))
        u = ps.logn[:k]
        Pabs = 2.0 * (ps.wt[:k] * np.abs(f0(u, lam))).sum() + prime_tail_bound(min(math.exp(ucut), ps.nmax), lam)
        ratio = Pabs / A_of(lam)
        c_need = 2 * math.pi * math.exp(2 * ratio)   # arch/f0 ~ log(c/2pi) >= 2 ratio
        env[str(lam)] = {"Pabs_over_f0": ratio, "c_needed_for_arch_half": c_need}
        print(f"   lam={lam:<6g}: P_abs/f(0) = {ratio:9.3e}   ->  arch/2 >= P_abs needs log(c/2pi) >= {2*ratio:.3g}, i.e. c >= {c_need:.3g}")
    out["prime_envelope"] = env


def lam0_of(c, ps, lo=0.001, hi=2.0, n=200):
    """sup{lam : arch(c,l) > 0 and |prime(c,l)| <= arch(c,l)/2 for all l <= lam} on a log grid (direct prime only)."""
    grid = np.exp(np.linspace(math.log(lo), math.log(hi), n))
    last = None
    limited = False
    for lam in grid:
        pv, N_used, ptail = ps.prime_sum(c, lam)
        if ptail > 1e-3 * A_of(lam):
            limited = True       # direct prime side no longer feasible with this nmax: lam0 is only a lower bound
            break
        arch = pole_term(c, lam) + psi_term(c, lam, 16) - A_of(lam) * math.log(math.pi)
        if arch > 0 and abs(pv) + ptail <= arch / 2:
            last = float(lam)
        else:
            break
    return (None if last is None else round(last, 4)), limited


# ----------------------------------------------------------------------------- Task 2
def task2(zw, out):
    print("\n" + "=" * 100)
    print("TASK 2: near-zero regime, lam >= 1: F vs truncated sum over |t - c| <= D, and the strip tail bound")
    print("=" * 100)
    print("tail_D := e^{lam/2} sum_{|t-c|>D} ((t-c)^2 + 1/4) e^{-2 lam (t-c)^2} over cached zeros (both images) + beyond-window bound")
    print("(the bound seam C's instrument uses for UNCERTIFIED zeros anywhere in the strip |y| <= 1/2)")
    Ds = [1, 2, 5, 50]
    lams = [1, 2, 5, 10, 20, 50]
    res = {}
    cs = [c for c in CS if c >= 14.0]
    print(f"{'c':>8} {'lam':>4} {'F':>10} | " + " ".join(f"{'D='+str(D)+': F-F_D':>13} {'tail_D':>9}" for D in Ds))
    for c in cs:
        t = zw[c]
        for lam in lams:
            F = F_zero(c, lam, t)
            line = []
            rec = {"F": F}
            for D in Ds:
                near = t[np.abs(t - c) <= D]
                FD = F_zero(c, lam, near) if len(near) else 0.0
                far = t[np.abs(t - c) > D]
                tb = tail_D(c, lam, far, t, D)
                rec[f"D{D}"] = {"F_D": FD, "omitted": F - FD, "tail_bound": tb, "n_near": int(len(near))}
                line.append(f"{F-FD:13.2e} {tb:9.1e}")
            res[f"{c}_{lam}"] = rec
            print(f"{c:8.1f} {lam:4d} {F:10.3e} | " + " ".join(line))
    out["near_zero"] = res

    print("\nlam_1(c, D): smallest lam (log grid 0.05..200) beyond which the CERTIFIED near part beats tail_D for all larger lam;")
    print("three readings of 'near term': the near SUM, the LARGEST single near term, the SMALLEST single near term.")
    print(f"{'c':>8} | {'D=2: sum':>9} {'max':>7} {'min':>7} | {'D=5: sum':>9} {'max':>7} {'min':>7} | nearest gap |t-c|")
    grid = np.exp(np.linspace(math.log(0.05), math.log(200), 300))
    l1 = {}
    for c in cs:
        t = zw[c]
        rec = {}
        parts = []
        for D in (2, 5):
            near = t[np.abs(t - c) <= D]
            far = t[np.abs(t - c) > D]
            th = {}
            for name, fn in (("sum", lambda g, l: G(g, c, l).sum() + G(-g, c, l).sum()),
                             ("max", lambda g, l: G(g, c, l).max()),
                             ("min", lambda g, l: G(g, c, l).min())):
                ok = np.array([fn(near, l) > tail_D(c, l, far, t, D) for l in grid])
                bad = np.where(~ok)[0]
                if len(bad) == 0:
                    th[name] = float(grid[0])
                elif bad[-1] + 1 < len(grid):
                    th[name] = float(grid[bad[-1] + 1])
                else:
                    th[name] = None
            rec[f"D{D}"] = th
            parts.append(f"{fmt(th['sum']):>9} {fmt(th['max']):>7} {fmt(th['min']):>7}")
        l1[str(c)] = rec
        print(f"{c:8.1f} | " + " | ".join(parts) + f" | {np.min(np.abs(t - c)):.3f}")
    out["lam1"] = l1


def fmt(x):
    return "never" if x is None else f"{x:.3g}"


def tail_D(c, lam, far, t, D):
    w = far - c
    s = (math.exp(lam / 2) * ((w * w + 0.25) * np.exp(-2 * lam * w * w)).sum())
    w2 = -far - c
    s += math.exp(lam / 2) * ((w2 * w2 + 0.25) * np.exp(-2 * lam * w2 * w2)).sum()
    # images -t of the near zeros are far too (c >= 14): include
    near = t[np.abs(t - c) <= D]
    w3 = -near - c
    s += math.exp(lam / 2) * ((w3 * w3 + 0.25) * np.exp(-2 * lam * w3 * w3)).sum()
    zb, _ = zero_tail_bound(c, lam, t)
    return s + math.exp(lam / 2) * zb * 1.25


# ----------------------------------------------------------------------------- Task 3
def task3(zw, out, quick):
    print("\n" + "=" * 100)
    print("TASK 3: the bandwidth barrier")
    print("=" * 100)
    print("prime side needs n <= N(lam, eps): tail bound 2 sum_{n>N} Lambda(n) n^{-1/2} |f0(log n)| <= eps f(0).")
    print("Exact cutoff from the closed form: the term envelope is Lambda(n) n^{-1/2} |f0(log n)| ~ e^{u/2} (u^2/4lam) e^{-u^2/8lam}")
    print("= e^{lam/2} (u^2/4lam) e^{-(u - 2 lam)^2/(8 lam)}: the n^{-1/2} against the prime density e^{u} SHIFTS the Gaussian")
    print("centre to u = 2 lam, so log N = 2 lam + sqrt(8 lam (log(1/eps) + lam/2 + log(...))), not sqrt(8 lam log(1/eps)).")
    lams = [0.1, 0.5, 1, 2, 4, 8, 16, 32]
    epss = [1e-3, 1e-10, 1e-30]
    print(f"{'lam':>5} | " + " | ".join(f"{'eps='+f'{e:g}':>22}" for e in epss) + " | naive sqrt(8 lam log 1/eps) for eps=1e-10")
    tab = {}
    for lam in lams:
        parts = []
        rec = {}
        for eps in epss:
            lN = N_cutoff(lam, eps)
            N = math.exp(lN)
            tag = "sieve" if N <= 1e9 else ("heroic" if N <= 1e12 else "IMPOSSIBLE")
            rec[str(eps)] = {"logN": lN, "N": N, "tag": tag}
            parts.append(f"{N:9.2e} ({tag:>10})")
        tab[str(lam)] = rec
        naive = math.exp(math.sqrt(8 * lam * math.log(1e10)))
        print(f"{lam:5g} | " + " | ".join(parts) + f" | {naive:9.2e}")
    out["N_cutoff"] = tab

    print("\nO2 crossover in these terms.  lam*(y, x1) = log(x1^2/(2 y^2)) / (2 (x1^2 + y^2)) (PHASE0 lam_nn1, matches lam* to 3-4 digits)")
    print("x1 = typical gap 2 pi / log(c/2pi).  y0 solves lam*(y0, x1) = Lam_max: zeros with |beta - 1/2| < y0 are NOT detectable")
    print("by a Gaussian of bandwidth lam <= Lam_max (in the nearest-neighbour model, c = t0 exactly).")
    Lmax = [1, 2, 4, 8]
    print(f"{'c':>8} {'x1':>7} {'x1/sqrt2':>8} | " + " ".join(f"{'Lam='+str(L):>9}" for L in Lmax) + "   [y0 model]")
    y0 = {}
    for c in (100.0, 1e4, 1e6, 1e12):
        x1 = 2 * math.pi / math.log(c / (2 * math.pi))
        rec = {"x1": x1}
        vals = []
        for L in Lmax:
            y = solve_y0(x1, L)
            rec[str(L)] = y
            vals.append(y)
        y0[str(c)] = rec
        print(f"{c:8.0e} {x1:7.3f} {x1/math.sqrt(2):8.3f} | " + " ".join(f"{v:9.4f}" for v in vals))
    out["y0_model"] = y0

    print("\nSame question against the REAL neighbours (replace mode, quadruple at the ordinate of the zero nearest c, c scanned")
    print("over t0 +- 1 step 0.005, lam on a log grid up to Lam_max): y0_real = inf{y : some (c', lam) has F_zero < 0}, bisected;")
    print("'signal' = most negative F_zero found at y = 1.5 y0_real (the absolute accuracy the prime side would need).")
    print("For c = 1e6 and 1e12 no zeros are cached: PROXY = the 10000-window rescaled about t0 so the mean gap equals")
    print("2 pi / log(c/2pi) (local GUE-like statistics assumed; order of magnitude only).  y0 at the 1e-6 floor prints '<1e-6'.")
    print(f"{'c':>8} {'t0':>10} {'x1_real':>8} | " + " ".join(f"{'Lam='+str(L)+': y0 / signal':>22}" for L in Lmax))
    y0r = {}
    cases = [(100.0, None), (1e4, None), (1e6, "proxy"), (1e12, "proxy")] if quick else \
            [(100.0, None), (1000.0, None), (1e4, None), (1e6, "proxy"), (1e12, "proxy")]
    for c, kind in cases:
        t = zw[1e4] if kind == "proxy" else zw[c]
        i = int(np.argmin(np.abs(t - (1e4 if kind == "proxy" else c))))
        t0 = float(t[i])
        if kind == "proxy":
            scale = (2 * math.pi / math.log(c / (2 * math.pi))) / (2 * math.pi / math.log(1e4 / (2 * math.pi)))
            t = t0 + (t - t0) * scale
            t = t[np.abs(t - t0) <= 60.0]
        tl = np.delete(t, int(np.argmin(np.abs(t - t0))))
        x1r = float(np.min(np.abs(tl - t0)))
        rec = {"t0": t0, "x1_real": x1r, "proxy": kind == "proxy"}
        parts = []
        for L in Lmax:
            y, sig = y0_real(tl, t0, L, quick)
            rec[str(L)] = {"y0": y, "signal": sig}
            parts.append((f"{'<1e-6':>8}" if y < 2e-6 else f"{y:8.4f}") + f" / {sig:10.2e}")
        y0r[str(c)] = rec
        print(f"{c:8.0e} {t0:10.3f} {x1r:8.3f} | " + " ".join(f"{p:>22}" for p in parts) + ("   [PROXY]" if kind == "proxy" else ""))
    out["y0_real"] = y0r


def solve_y0(x1, L):
    lo, hi = 1e-12, x1 / math.sqrt(2) * (1 - 1e-12)
    lamstar = lambda y: math.log(x1 * x1 / (2 * y * y)) / (2 * (x1 * x1 + y * y))
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if lamstar(mid) > L:
            lo = mid
        else:
            hi = mid
    return hi


def y0_real(tl, t0, Lmax, quick):
    cs = np.arange(t0 - 1.0, t0 + 1.0 + 1e-9, 0.01 if quick else 0.005)
    lams = np.exp(np.linspace(math.log(0.05), math.log(Lmax), 40 if quick else 80))

    def minF(y):
        best = float("inf")
        for lam in lams:
            X = tl[None, :] - cs[:, None]
            S = (X * X * np.exp(-2 * lam * X * X)).sum(axis=1)
            Xn = -tl[None, :] - cs[:, None]
            S += (Xn * Xn * np.exp(-2 * lam * Xn * Xn)).sum(axis=1)
            for sgn in (1, -1):
                w = (sgn * t0 - cs) + 1j * y
                S += 2.0 * (w * w * np.exp(-2 * lam * w * w)).real
            best = min(best, float(S.min()))
        return best

    lo, hi = 1e-6, 0.5
    if minF(hi) >= 0:
        return float("nan"), float("nan")
    for _ in range(22 if quick else 28):
        mid = math.sqrt(lo * hi)
        if minF(mid) < 0:
            hi = mid
        else:
            lo = mid
    return hi, minF(1.5 * hi)


# ----------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--nmax", type=int, default=None)
    args = ap.parse_args()
    np.seterr(all="ignore")
    T = time.time()
    nmax = args.nmax or (10_000_000 if args.quick else 100_000_000)

    print("closed-form checks: f0 vs direct convolution phi*phi~, paperFT f vs gaussTest (mpmath)")
    wc, wf = verify_closed_forms()
    print(f"  max |conv - f| = {wc:.2e}   max |paperFT f - G| = {wf:.2e}   ({'OK' if wc < 1e-9 and wf < 1e-12 else 'FAIL'})")
    out = {"closed_form_check": {"conv": wc, "ft": wf}, "quick": args.quick, "nmax": nmax}

    first, window, check = load_zeros(2000)
    zw = zero_windows(first, window)
    print(f"zeros: first 2000 (t <= {first[-1]:.2f}), window around 10000, window around 5000 ({len(zw[5000.0])} zeros); "
          f"max |Re rho - 1/2| = {check['max_|Re-1/2|']:.1e}")
    import mpmath as mp
    mp.mp.dps = 30
    ddig = max(abs(complex(mp.digamma(mp.mpc(0.25, 0.5 * r))) - digamma(0.25 + 0.5j * r)) for r in (0.0, 1.0, 14.1, 1e4))
    print(f"scipy complex digamma vs mpmath (4 points): max abs diff {ddig:.1e}")
    out["digamma_check"] = ddig
    # psi quadrature self-check
    dpsi = max(abs(psi_term(c, lam, 32) - psi_term(c, lam, 64)) / abs(psi_term(c, lam, 64))
               for c in (0.0, 5.0, 14.1347, 1e4) for lam in (0.005, 0.05, 1, 50))
    print(f"psi quadrature self-check (32 vs 64 nodes per panel, worst relative): {dpsi:.1e}")
    out["psi_selfcheck"] = dpsi
    ps = PrimeSide(nmax)
    print(f"prime powers up to {nmax:.0e}: {len(ps.n)} terms, sieve {ps.secs:.1f}s")

    task1(zw, first, ps, out, args.quick)
    task2(zw, out)
    task3(zw, out, args.quick)
    with open(os.path.join(SCRATCH, f"landscape{'_quick' if args.quick else ''}.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    print(f"\ntotal {time.time()-T:.1f}s; json in {SCRATCH}")
    print("conjecture1_proved = False  (numerics only; nothing proved about the true zero set)")


if __name__ == "__main__":
    main()

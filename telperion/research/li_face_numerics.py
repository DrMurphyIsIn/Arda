#!/usr/bin/env python3
"""Numerics for the Li face brief (docs/LI_FACE_BRIEF_2026-09-21.md), 2026-09-21.

conjecture1_proved = False.  Nothing in this file proves, or is meant to prove, anything about the
Riemann Hypothesis.  Everything here MEASURES (floats, or ball arithmetic reported as midpoints):
Li coefficients computed two independent ways, the termwise lemma of section 3 checked on grids, the
low-height box of section 4, Lemma B, and the Gaussian-face resonance at fixed width.

Tasks (see li_face_numerics.md for the tables and the conclusions):
  1. lambda_N, N = 1..NMAX, (a) from the paired zero sum over the first M zeros plus a smooth tail,
     (b) from the Taylor series of log xi(1/(1-z)) at z = 0 (ball arithmetic, python-flint acb_series;
     mpmath mp.taylor as a low-order cross-check), (c) vs the certified lower bounds in
     examples/li_positivity/lean/LiPositivity.lean (hlo, index n = N - 1).
  2. Termwise lemma: Re P_N(beta, gamma) = 2 - (r^N + r^-N) cos(N theta) on a (beta, gamma) grid;
     Theorem C region check; gamma_min(N) = sup{gamma : some beta has Re P_N < 0} and gamma_min(N)/N.
  3. Box region gamma >= sqrt(3)/2, (beta - 1/2)^2 <= gamma^2/3 - 1/4: min of Re P_N for N = 1..8.
  4. Lemma B: |log r| <= |theta| <= 1/gamma on beta in (0,1), gamma >= 1; the smallest gamma where
     |log r| <= |theta| can fail.
  5. Sanity: lambda_N >= 0 and min_N lambda_N / (N log N / 2).
  6. Gaussian-face resonance at lam = 0.7 and 1.0: sup of prime(c, lam)/A over c in [0, 1e6] vs the
     coefficient l1 bound, reusing examples/rvm_bridge/fixed_width_band.py.

Conventions.  N = n + 1 where n is the li-island rung index; lambda_N = sum_rho [1 - (1 - 1/rho)^N]
(Bombieri-Lagarias), generating function d/dz log xi(1/(1-z)) = sum_{n>=0} lambda_{n+1} z^n, i.e.
lambda_m = m * [z^m] log xi(1/(1-z)).  xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s).
For rho = beta + i gamma:  w = rho/(rho-1) = r e^{i theta},
    log r = (1/2) log((beta^2 + gamma^2) / ((1-beta)^2 + gamma^2)),
    |theta| = arctan(beta/gamma) + arctan((1-beta)/gamma),
    Re P_N = 2 - 2 cosh(N log r) cos(N theta).
The pair is symmetric under beta -> 1 - beta (log r -> -log r) and gamma -> -gamma (theta -> -theta),
so beta in (0, 1/2], gamma > 0 suffices.

Usage: python3 li_face_numerics.py [--quick] [--nmax 2000] [--zeros 100000] [--procs 24]
"""
import argparse
import json
import math
import os
import sys
import time
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RVM = os.path.join(HERE, "..", "examples", "rvm_bridge")
SCRATCH = os.environ.get(
    "LI_SCRATCH",
    "/private/tmp/claude-0/-Users-peterwmurphy/466d3ce5-8284-473c-b6b0-031627e4571a/scratchpad/li_face")
os.makedirs(SCRATCH, exist_ok=True)

SQ3_2 = math.sqrt(3.0) / 2.0

# Certified lower bounds from LiPositivity.lean (hlo, index n = N - 1), verbatim rationals.
LEAN_HLO = {
    0: (230957089661, 10000000000000), 1: (23086433807, 250000000000), 2: (103819460277, 500000000000),
    3: (92197619873, 250000000000), 4: (575542714461, 1000000000000), 5: (413783006141, 500000000000),
    6: (112446011757, 100000000000), 7: (73287783857, 50000000000), 8: (92545802419, 50000000000),
    9: (227933936319, 100000000000), 10: (137518041911, 50000000000), 11: (163162766031, 50000000000),
    12: (47715500723, 12500000000), 13: (110286941967, 25000000000), 14: (252253968601, 50000000000),
    15: (285855412443, 50000000000), 16: (642658287211, 100000000000), 17: (717248093829, 100000000000),
    18: (795374309431, 100000000000), 19: (876927687209, 100000000000),
}


def banner(s):
    print("\n" + "=" * 100)
    print(s)
    print("=" * 100)


# ----------------------------------------------------------------------------- Task 1b: Taylor series (ball arithmetic)
def li_series_flint(nmax, prec_bits):
    """lambda_1..lambda_nmax as (mid, rad) from the acb_series of log xi(1/(1-z)).  ~1.2 bits lost per order."""
    from flint import acb, acb_series, ctx
    ctx.prec = prec_bits
    L = nmax + 2
    ctx.cap = L
    z = acb_series([0, 1], prec=L)
    one = acb_series([1], prec=L)
    s = one / (one - z)                 # s = 1/(1-z), s(0) = 1
    sm1 = z / (one - z)                 # s - 1
    zd = s.zeta(deflate=True)           # zeta(s) - 1/(s-1), analytic at s = 1
    xi = s * (sm1 * zd + one) * (s * (-acb.pi().log() / 2)).exp() * (s / 2).gamma() / 2
    lg = xi.log()
    mids = np.empty(nmax)
    rads = np.empty(nmax)
    imag = 0.0
    for m in range(1, nmax + 1):
        c = lg[m] * m
        mids[m - 1] = float(c.real.mid())
        rads[m - 1] = float(c.real.rad())
        imag = max(imag, abs(float(c.imag.mid())) + float(c.imag.rad()))
    return mids, rads, imag


def li_taylor_mpmath(nmax, dps):
    """lambda_1..lambda_nmax via mpmath mp.taylor of log xi(1/(1-z)) at 0 (numerical differentiation)."""
    import mpmath as mp
    mp.mp.dps = dps

    def xi(s):
        s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
        sm1z = mp.mpf(1) if s == 1 else (s - 1) * mp.zeta(s)
        return mp.mpf(1) / 2 * s * sm1z * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2)

    def logphi(z):
        return mp.log(xi(1 / (1 - z)))

    co = mp.taylor(logphi, 0, nmax)
    return np.array([float(co[m] * m) for m in range(1, nmax + 1)])


# ----------------------------------------------------------------------------- Task 1a: zero sum
def _zeros_chunk(args):
    n0, cnt = args
    import flint
    flint.ctx.prec = 64
    zs = flint.acb.zeta_zeros(n0, cnt)
    off = max(abs(float(z.real.mid()) - 0.5) for z in zs)
    return n0, [float(z.imag.mid()) for z in zs], off


def zeros_first(M, procs):
    """Ordinates of the first M zeros (flint, 64-bit, parallel chunks), cached; also max |Re - 1/2|."""
    path = os.path.join(SCRATCH, f"zeros_{M}.json")
    if os.path.exists(path):
        with open(path) as fh:
            d = json.load(fh)
        return np.array(d["gam"]), d["offline"], d["secs"]
    t = time.time()
    chunk = 2500
    jobs = [(n0, min(chunk, M - n0 + 1)) for n0 in range(1, M + 1, chunk)]
    with Pool(procs) as pool:
        res = pool.map(_zeros_chunk, jobs)
    res.sort()
    gam = np.concatenate([np.array(r[1]) for r in res])
    off = max(r[2] for r in res)
    assert len(gam) == M and np.all(np.diff(gam) > 0)
    secs = time.time() - t
    with open(path, "w") as fh:
        json.dump({"gam": gam.tolist(), "offline": off, "secs": secs}, fh)
    return gam, off, secs


def n_smooth(t):
    return t / (2 * math.pi) * math.log(t / (2 * math.pi * math.e)) + 7.0 / 8.0


def zero_sum_lambda(gam, Ns):
    """(a) paired zero sum: sum_j 2(1 - cos(N theta_j)), theta_j = 2 arctan(1/(2 gamma_j)) (r = 1 on the line)."""
    th = 2.0 * np.arctan(1.0 / (2.0 * gam))
    out = np.empty(len(Ns))
    for i, N in enumerate(Ns):
        out[i] = float((4.0 * np.sin(0.5 * N * th) ** 2).sum())
    return out


def smooth_tail(Tstar, Ns):
    """sum over zeros above T* of 2(1 - cos(N theta)) with the smooth density (1/2pi) log(t/2pi) dt."""
    from scipy.integrate import quad

    def integrand(u, N):   # u = 1/t; 2(1 - cos x) = 4 sin^2(x/2) (no cancellation at small angles)
        th = 2.0 * math.atan(0.5 * u)
        return 4.0 * math.sin(0.5 * N * th) ** 2 * math.log(1.0 / (2 * math.pi * u)) / (2 * math.pi) / (u * u)

    out = np.empty(len(Ns))
    for i, N in enumerate(Ns):
        out[i] = quad(integrand, 0.0, 1.0 / Tstar, args=(N,), limit=400)[0]
    return out


def smooth_tail_mp(Tstar, N):
    """mpmath quadrature of the same tail (cross-check of the scipy version)."""
    import mpmath as mp
    mp.mp.dps = 30
    f = lambda t: 4 * mp.sin(N * mp.atan(1 / (2 * t))) ** 2 * mp.log(t / (2 * mp.pi)) / (2 * mp.pi)
    return float(mp.quad(f, [Tstar, 10 * Tstar, 1000 * Tstar, mp.inf]))


def task1(args, out):
    banner("TASK 1: Li coefficients lambda_N three ways")
    nmax = args.nmax
    # (b) ball arithmetic series
    prec = int(1.5 * nmax) + 400
    t = time.time()
    lam_b, rad_b, imag_b = li_series_flint(nmax, prec)
    tb = time.time() - t
    print(f"(b) acb_series of log xi(1/(1-z)), order {nmax}, {prec} bits: {tb:.1f}s; max radius {rad_b.max():.1e} (0 = below float64 range), "
          f"max |Im| {imag_b:.1e}; lambda_1 = {lam_b[0]:.15f}, lambda_{nmax} = {lam_b[-1]:.6f}")
    # (b') mpmath taylor cross-check (low order; numerical differentiation)
    nm = 12 if args.quick else 24
    t = time.time()
    lam_mp = li_taylor_mpmath(nm, 60)
    tm = time.time() - t
    dmp = np.abs(lam_mp - lam_b[:nm]) / np.abs(lam_b[:nm])
    print(f"(b') mpmath mp.taylor order {nm} at 60 dps: {tm:.1f}s; max rel diff vs (b) = {dmp.max():.1e} "
          f"({-math.log10(max(dmp.max(), 1e-17)):.1f} digits, float64 limited); mp.taylor is numerical differentiation, unusable at order 2000")
    # (a) zero sum
    gam, off, zs_secs = zeros_first(args.zeros, args.procs)
    M = len(gam)
    print(f"(a) first {M} zeros (flint acb.zeta_zeros, 64-bit, parallel): {zs_secs:.0f}s; gamma_M = {gam[-1]:.3f}; "
          f"max |Re rho - 1/2| = {off:.1e}")
    import mpmath as mp
    mp.mp.dps = 20
    chk = [1, 2, 10, 100, 1000, M]
    mpz = {n: float(mp.zetazero(n).imag) for n in chk if n <= 2000}
    chkd = {n: abs(mpz[n] - gam[n - 1]) for n in mpz}
    print(f"    cross-check vs mpmath.zetazero: " + ", ".join(f"n={n}: {d:.1e}" for n, d in chkd.items()))
    # T*: smooth count equals M (tail starts where the smooth density has counted exactly M zeros)
    lo, hi = gam[-1] * 0.9, gam[-1] * 1.1
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        if n_smooth(mid) < M:
            lo = mid
        else:
            hi = mid
    Tstar = hi
    Ns = np.arange(1, nmax + 1)
    t = time.time()
    S = zero_sum_lambda(gam, Ns)
    tail = smooth_tail(Tstar, Ns)
    lam_a = S + tail
    ta = time.time() - t
    print(f"    T* (smooth count = M) = {Tstar:.3f}; sum + tail for N = 1..{nmax}: {ta:.1f}s; tail cross-check scipy vs mpmath: "
          + ", ".join(f"N={N}: {abs(tail[N-1] - smooth_tail_mp(Tstar, N))/tail[N-1]:.1e}" for N in (1, 10, nmax)))
    rel = np.abs(lam_a - lam_b) / np.abs(lam_b)
    digits = -np.log10(np.maximum(rel, 1e-300))
    print(f"\n{'N':>5} {'lambda_N (b) series':>22} {'rad(b)':>9} {'(a) M zeros':>16} {'tail':>12} {'(a) total':>18} {'rel diff':>9} {'digits':>6}")
    show = [1, 2, 3, 4, 5, 10, 20, 50, 100, 200, 500, 1000, 1500, 2000]
    for N in show:
        if N <= nmax:
            i = N - 1
            print(f"{N:5d} {lam_b[i]:22.12f} {rad_b[i]:9.1e} {S[i]:16.8f} {tail[i]:12.6f} {lam_a[i]:18.8f} {rel[i]:9.1e} {digits[i]:6.1f}")
    print(f"\n    agreement (a) vs (b): min digits over N = {digits.min():.1f} (at N = {int(Ns[np.argmin(digits)])}), "
          f"median {np.median(digits):.1f}; tail/lambda at N = {nmax}: {tail[-1]/lam_b[-1]:.2e}")
    print("    (the tail uses the smooth zero density N_smooth(t) started at T* with N_smooth(T*) = M; the residual is the fluctuation")
    print("     of the zero count above T*, which enters only through the slowly varying weight 4 sin^2(N theta/2) ~ N^2/t^2)")
    # (c) vs Lean hlo
    print(f"\n(c) Lean certified lower bounds (LiPositivity.lean hlo, n = N - 1) vs (b):")
    print(f"{'n':>3} {'N':>3} {'hlo':>16} {'lambda_N (b)':>22} {'lambda - hlo':>13} {'ok':>3}")
    okc = True
    for n in range(20):
        p, q = LEAN_HLO[n]
        hlo = p / q
        d = lam_b[n] - hlo
        ok = d >= -rad_b[n]
        okc &= ok
        print(f"{n:3d} {n+1:3d} {hlo:16.12f} {lam_b[n]:22.14f} {d:13.2e} {'yes' if ok else 'NO'}")
    print(f"    all 20 hlo <= lambda_N: {'yes' if okc else 'NO'}; hlo are the Arb enclosure lower ends rounded down at ~1e-11")
    out["task1"] = {"nmax": nmax, "prec_bits": prec, "series_secs": tb, "max_rad": float(rad_b.max()),
                    "mp_taylor_order": nm, "mp_taylor_max_rel": float(dmp.max()),
                    "M": M, "gamma_M": float(gam[-1]), "Tstar": Tstar, "offline": off, "zetazero_check": {str(k): v for k, v in chkd.items()},
                    "min_digits": float(digits.min()), "median_digits": float(np.median(digits)),
                    "lean_ok": bool(okc),
                    "lambda_series": lam_b.tolist(), "lambda_rad": rad_b.tolist(), "lambda_zerosum": lam_a.tolist(), "tail": tail.tolist()}
    return lam_b


# ----------------------------------------------------------------------------- Task 2: termwise lemma
def logr_theta(beta, gam):
    beta = np.asarray(beta, dtype=float)
    gam = np.asarray(gam, dtype=float)
    lr = 0.5 * np.log((beta * beta + gam * gam) / ((1.0 - beta) ** 2 + gam * gam))
    th = np.arctan(beta / gam) + np.arctan((1.0 - beta) / gam)
    return lr, th


def rePN_sign(beta, gam, N):
    """Returns (fails, val): fails = Re P_N < 0 (computed in log form, overflow-safe); val = Re P_N (may be -inf)."""
    lr, th = logr_theta(beta, gam)
    a = np.abs(N * lr)
    b = N * th
    cb = np.cos(b)
    logcosh = a + np.log1p(np.exp(-2.0 * a)) - math.log(2.0)
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        fails = (cb > 0) & (logcosh + np.log(np.where(cb > 0, cb, 1.0)) > 0)
        val = 2.0 - 2.0 * np.exp(np.minimum(logcosh, 700.0)) * cb
    return fails, val


def task2(args, out):
    banner("TASK 2: termwise lemma  Re P_N(beta, gamma) = 2 - (r^N + r^-N) cos(N theta)")
    nmax = args.nmax
    res = {}
    # (i) Theorem C region check: gamma >= max(1, 2N/pi), all beta.  Grid: gamma in [max(1, 2N/pi), 200] (N <= 314) and
    #     a strip [2N/pi, 2N/pi + 60] for every N; beta in (0, 1/2].
    betas = np.concatenate([[1e-6, 1e-4, 1e-3], np.linspace(0.005, 0.5, 200)])
    t = time.time()
    nfail = 0
    worst = (np.inf, None)
    Ns_all = range(1, nmax + 1)
    for N in Ns_all:
        g0 = max(1.0, 2.0 * N / math.pi)
        gs = np.concatenate([np.linspace(g0, g0 + 60.0, 3000 if N <= 314 else 1200),
                             np.linspace(g0, 200.0, 2000) if g0 < 200 else np.array([g0])])
        f, v = rePN_sign(betas[:, None], gs[None, :], N)
        nfail += int(f.sum())
        i = np.unravel_index(int(np.argmin(v)), v.shape)
        if v[i] < worst[0]:
            worst = (float(v[i]), (N, float(betas[i[0]]), float(gs[i[1]])))
    print(f"(i) Theorem C region gamma >= max(1, 2N/pi), N = 1..{nmax}, {len(betas)} betas x up to 5000 gammas per N: "
          f"{time.time()-t:.0f}s; grid points with Re P_N < 0: {nfail}; min Re P_N = {worst[0]:.3e} at (N, beta, gamma) = {worst[1]}")
    res["theoremC_grid_failures"] = nfail
    res["theoremC_min"] = worst

    # (ii) gamma_min(N) = sup{gamma : exists beta with Re P_N < 0}.  For gamma > N/(2 pi), N theta < 2 pi for every beta, so
    #      a failure needs cos(N theta) > 0 with N theta in (3pi/2, 2pi): scan gamma from 2N/(3pi) + 2 downwards.
    t = time.time()
    betas2 = np.concatenate([[1e-8, 1e-6, 1e-5, 1e-4, 1e-3, 3e-3], np.linspace(0.005, 0.5, 200)])
    betas_fine = np.concatenate([[1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3], np.linspace(0.002, 0.5, 2000)])
    Ns2 = list(range(1, min(nmax, 400) + 1)) + [n for n in range(450, nmax + 1, 50)]
    gmin = {}
    for N in Ns2:
        top = max(2.0 * N / (3.0 * math.pi) + 2.0, 3.0)
        bot = max(0.5, (N - 2.0 * math.pi) / (2.0 * math.pi) - 2.0)
        gs = np.arange(top, bot, -0.01)
        f, _ = rePN_sign(betas2[:, None], gs[None, :], N)
        anyf = f.any(axis=0)
        if not anyf.any():
            gmin[N] = (0.5, None, "no failure found for gamma >= 0.5")
            continue
        j = int(np.argmax(anyf))            # first (largest gamma) failing grid point
        g_fail = gs[j]
        g_ok = gs[j - 1] if j > 0 else top + 0.01
        # bisection on the top edge with the fine beta grid
        for _ in range(40):
            mid = 0.5 * (g_fail + g_ok)
            fm, _ = rePN_sign(betas_fine, mid, N)
            if fm.any():
                g_fail = mid
            else:
                g_ok = mid
        fm, _ = rePN_sign(betas_fine, g_fail, N)
        bstar = float(betas_fine[np.argmax(fm)])
        # also the lowest failing gamma seen (the failing set is a union of windows, one per multiple of 2 pi)
        _, th_half = logr_theta(0.5, g_fail)
        gmin[N] = (float(g_fail), bstar, float(N * th_half / (2 * math.pi)))
    el = time.time() - t
    print(f"\n(ii) gamma_min(N) = sup of the failing gamma (top edge, bisected to 1e-12 on {len(betas_fine)} betas): {el:.0f}s")
    print(f"{'N':>5} {'gamma_min':>12} {'gamma_min/N':>12} {'2N/pi':>10} {'ratio to 2N/pi':>15} {'beta at edge':>13} {'N theta(1/2)/2pi':>17} {'gamma_min - N/2pi':>18}")
    for N in [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 30, 50, 75, 100, 150, 200, 300, 400, 500, 1000, 1500, 2000]:
        if N in gmin and gmin[N][1] is not None:
            g, b, cyc = gmin[N]
            print(f"{N:5d} {g:12.6f} {g/N:12.6f} {2*N/math.pi:10.3f} {g/(2*N/math.pi):15.4f} {b:13.1e} {cyc:17.4f} {g - N/(2*math.pi):18.4f}")
        elif N in gmin:
            print(f"{N:5d} {'none >= 0.5':>12}   {gmin[N][2]}")
    vals = np.array([gmin[N][0] / N for N in Ns2 if gmin[N][1] is not None])
    big = np.array([gmin[N][0] / N for N in Ns2 if gmin[N][1] is not None and N >= 500])
    print(f"    gamma_min(N)/N: last values {vals[-5:]}, mean over N >= 500: {(big.mean() if len(big) else float('nan')):.6f}; 1/(2 pi) = {1/(2*math.pi):.6f}; "
          f"2/pi = {2/math.pi:.6f}")
    print(f"    gamma_min(N) - N/(2 pi) for N >= 500: {[round(gmin[N][0] - N/(2*math.pi), 4) for N in Ns2 if N >= 500][:6]} ... "
          f"(prediction from the beta -> 0 edge: 1/2)")
    print("    reading: the exchange rate 2N/pi of Theorem C is 4x conservative; the true threshold is N/(2 pi) + 1/2, reached as beta -> 0+.")
    print("    Failures occur ONLY in windows where N theta is within O(N |log r|) of a positive multiple of 2 pi; the first such window")
    print("    (N theta near 2 pi) has its top edge at gamma = N/(2 pi) + 1/2 + o(1).  Between 2N/(3 pi) and 2N/pi nothing fails (cos <= 0 or Lemma A).")
    # (iii) first failing rung per (beta, gamma): smallest N with Re P_N < 0 on a small table
    print(f"\n(iii) first failing rung N*(beta, gamma) (smallest N <= {nmax} with Re P_N < 0):")
    gtab = [0.9, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0, 14.13, 20.0, 50.0, 100.0, 200.0]
    btab = [0.5, 0.49, 0.45, 0.4, 0.3, 0.2, 0.1, 0.01, 0.001]
    hdr = "beta / gamma"
    print(f"{hdr:>13} | " + " ".join(f"{g:>7g}" for g in gtab))
    nstar = {}
    Nv = np.arange(1, nmax + 1)
    for b in btab:
        row = []
        for g in gtab:
            f, _ = rePN_sign(b, g, Nv)
            k = int(np.argmax(f)) + 1 if f.any() else None
            row.append(k)
            nstar[f"{b}_{g}"] = k
        print(f"{b:13g} | " + " ".join(f"{('-' if k is None else k):>7}" for k in row))
    print("    ('-' = no failing rung up to nmax; beta = 1/2 never fails; the first failing N is ~ 2 pi gamma - O(1) for small |log r|)")
    res["gamma_min"] = {str(N): gmin[N] for N in Ns2}
    res["nstar"] = nstar
    out["task2"] = res


# ----------------------------------------------------------------------------- Task 3: box region
def task3(args, out):
    banner("TASK 3: box region gamma >= sqrt(3)/2, (beta - 1/2)^2 <= gamma^2/3 - 1/4: min Re P_N, N = 1..8")
    from scipy.optimize import minimize
    res = {}
    # gamma range: Theorem C covers gamma >= max(1, 2N/pi); grid up to that + 1.
    print(f"{'N':>3} {'min Re P_N':>14} {'beta*':>10} {'gamma*':>10} {'on boundary':>12} {'sign':>5}   {'grid min':>12} {'(beta, gamma) grid':>20}")
    for N in range(1, 9):
        gtop = max(1.0, 2.0 * N / math.pi) + 1.0
        gs = np.linspace(SQ3_2, gtop, 4001 if args.quick else 12001)
        bs = np.linspace(0.0, 0.5, 1001 if args.quick else 4001)
        B, Gm = np.meshgrid(bs, gs, indexing="ij")
        inside = (B - 0.5) ** 2 <= Gm * Gm / 3.0 - 0.25
        _, v = rePN_sign(B, Gm, N)
        v = np.where(inside, v, np.inf)
        i = np.unravel_index(int(np.argmin(v)), v.shape)
        gb, gg, gv = float(bs[i[0]]), float(gs[i[1]]), float(v[i])

        def obj(x):
            b, g = x
            if g < SQ3_2 or g > gtop or b < 0.0 or b > 0.5:
                return 1e9
            slack = g * g / 3.0 - 0.25 - (b - 0.5) ** 2
            _, val = rePN_sign(b, g, N)
            return float(val) + (0.0 if slack >= 0 else 1e6 * (-slack))

        best = (gv, gb, gg)
        for x0 in ((gb, gg), (max(gb, 1e-3), gg + 0.01), (gb, max(gg, SQ3_2 + 1e-3))):
            r = minimize(obj, np.array(x0), method="Nelder-Mead", options={"xatol": 1e-12, "fatol": 1e-14, "maxiter": 4000})
            if r.fun < best[0]:
                best = (float(r.fun), float(r.x[0]), float(r.x[1]))
        mv, mb, mg = best
        slack = mg * mg / 3.0 - 0.25 - (mb - 0.5) ** 2
        onb = abs(slack) < 1e-6 or abs(mg - SQ3_2) < 1e-6
        if abs(mg - gtop) < 1e-6:
            onb = False
            note = f"  (min at the truncation edge gamma = {gtop:.3f}: Re P_N > 0 on the box, inf 0 only as gamma -> inf, ~ N^2/gamma^2)"
        else:
            note = ""
        res[str(N)] = {"min": mv, "beta": mb, "gamma": mg, "on_boundary": bool(onb), "grid_min": gv, "grid_pt": [gb, gg]}
        print(f"{N:3d} {mv:14.6e} {mb:10.6f} {mg:10.6f} {'yes' if onb else 'no':>12} {'>=0' if mv >= -1e-12 else '<0':>5}   {gv:12.6e} ({gb:.4f}, {gg:.4f}){note}")
    ok5 = all(res[str(N)]["min"] >= -1e-12 for N in range(1, 6))
    neg6 = res["6"]["min"] < 0
    print(f"    N = 1..5 nonnegative on the box: {'yes' if ok5 else 'NO'};  N = 6 negative: {'yes' if neg6 else 'NO'} "
          f"(brief section 4 says N = 6 fails near (0.64, 0.9))")
    # the quantity cosh(a) cos(b) on the box for N <= 5 (brief claims <= 0.5 in the dangerous window)
    for N in (4, 5):
        gs = np.linspace(SQ3_2, 3.0, 4001)
        bs = np.linspace(0.0, 0.5, 2001)
        B, Gm = np.meshgrid(bs, gs, indexing="ij")
        inside = (B - 0.5) ** 2 <= Gm * Gm / 3.0 - 0.25
        lr, th = logr_theta(B, Gm)
        cc = np.cosh(N * lr) * np.cos(N * th)
        win = inside & (np.cos(N * th) > 0) & (N * th > math.pi)
        print(f"    N = {N}: max cosh(a) cos(b) on the box = {cc[inside].max():.4f}; in the window b in (3pi/2, 2pi): "
              f"{(cc[win].max() if win.any() else float('nan')):.4f}")
    out["task3"] = res


# ----------------------------------------------------------------------------- Task 4: Lemma B
def task4(args, out):
    banner("TASK 4: Lemma B  |log r| <= |theta| <= 1/gamma")
    from scipy.optimize import brentq, minimize_scalar
    bs = np.concatenate([[1e-9, 1e-7, 1e-5, 1e-4, 1e-3], np.linspace(0.002, 0.998, 4001), [1 - 1e-3, 1 - 1e-4, 1 - 1e-5, 1 - 1e-7, 1 - 1e-9]])
    gs = np.concatenate([np.linspace(1.0, 10.0, 9001), np.geomspace(10.0, 1e6, 5000)])
    lr, th = logr_theta(bs[:, None], gs[None, :])
    d1 = th - np.abs(lr)
    d2 = 1.0 / gs[None, :] - th
    print(f"grid beta in (0,1) ({len(bs)} pts), gamma in [1, 1e6] ({len(gs)} pts):")
    print(f"    min(|theta| - |log r|) = {d1.min():.6e} at beta = {bs[np.unravel_index(np.argmin(d1), d1.shape)[0]]:.3g}, "
          f"gamma = {gs[np.unravel_index(np.argmin(d1), d1.shape)[1]]:.4g}  ({'holds' if d1.min() >= 0 else 'FAILS'})")
    print(f"    min(1/gamma - |theta|)  = {d2.min():.6e}  ({'holds' if d2.min() >= 0 else 'FAILS'})")
    # worst beta is beta -> 0 (|log r| max, |theta| min there); the edge: (1/2) log(1 + 1/g^2) = arctan(1/g)
    def edge(g):
        return math.atan(1.0 / g) - 0.5 * math.log1p(1.0 / (g * g))
    g_star = brentq(edge, 0.05, 1.0)
    # confirm with a 2D search: for gamma slightly above g_star, min over beta of (|theta| - |log r|) >= 0; below it fails
    def minb(g):
        r = minimize_scalar(lambda b: float(logr_theta(b, g)[1] - abs(logr_theta(b, g)[0])), bounds=(1e-12, 0.5), method="bounded",
                            options={"xatol": 1e-14})
        return r.fun, r.x
    gs2 = np.geomspace(0.1, 1.0, 400)
    fails = [(g, minb(g)) for g in gs2]
    top_fail = max([g for g, (v, b) in fails if v < 0], default=None)
    print(f"    smallest gamma above which |log r| <= |theta| holds for ALL beta: gamma* = {g_star:.9f} (solves arctan(1/g) = (1/2) log(1 + 1/g^2), the beta -> 0 edge)")
    print(f"    2D scan gamma in [0.1, 1]: largest failing gamma on the scan = {top_fail:.5f}; example: gamma = {g_star*0.98:.4f} gives min_beta = "
          f"{minb(g_star*0.98)[0]:.2e} at beta = {minb(g_star*0.98)[1]:.1e}; gamma = {g_star*1.02:.4f} gives {minb(g_star*1.02)[0]:.2e}")
    print(f"    compare: 2/pi = {2/math.pi:.6f}, sqrt(3)/2 = {SQ3_2:.6f}, 1: all comfortably above gamma*")
    # the box region: min over the box of (|theta| - |log r|)
    gsb = np.linspace(SQ3_2, 5.0, 8001)
    bsb = np.linspace(0.0, 0.5, 2001)
    B, Gm = np.meshgrid(bsb, gsb, indexing="ij")
    inside = (B - 0.5) ** 2 <= Gm * Gm / 3.0 - 0.25
    lrb, thb = logr_theta(B, Gm)
    db = np.where(inside, thb - np.abs(lrb), np.inf)
    i = np.unravel_index(int(np.argmin(db)), db.shape)
    print(f"    on the box (gamma >= sqrt(3)/2, confinement): min(|theta| - |log r|) = {db[i]:.6f} at (beta, gamma) = ({bsb[i[0]]:.4f}, {gsb[i[1]]:.4f}); "
          f"the brief's claim (1-beta)/gamma <= 0.91 for gamma < 1 on the box: max (1-beta)/gamma there = "
          f"{((1-B)/Gm)[inside & (Gm < 1)].max():.4f}")
    # the brief's intermediate bound |log r| <= (1/2)|2 beta - 1| / (min(beta,1-beta)^2 + gamma^2) <= 1/(2 gamma^2)
    bnd = 0.5 * np.abs(2 * bs[:, None] - 1) / (np.minimum(bs, 1 - bs)[:, None] ** 2 + gs[None, :] ** 2)
    print(f"    brief's bound |log r| <= (1/2)|2b-1|/(min(b,1-b)^2 + g^2): min slack on the gamma >= 1 grid = {(bnd - np.abs(lr)).min():.3e} "
          f"({'holds' if (bnd - np.abs(lr)).min() >= -1e-15 else 'FAILS'}); and |theta| >= pi/(4 gamma) for gamma >= 1: min slack = {(th - math.pi/4/gs[None, :]).min():.3e}")
    out["task4"] = {"min_theta_minus_logr_g_ge_1": float(d1.min()), "min_inv_gamma_minus_theta": float(d2.min()),
                    "gamma_star": g_star, "box_min_slack": float(db[i]), "box_min_at": [float(bsb[i[0]]), float(gsb[i[1]])]}


# ----------------------------------------------------------------------------- Task 5
def task5(lam, out):
    banner("TASK 5: sanity lambda_N >= 0 and lambda_N / (N log N / 2)")
    N = np.arange(1, len(lam) + 1)
    neg = int((lam < 0).sum())
    ratio = lam[1:] / (N[1:] * np.log(N[1:]) / 2.0)
    i = int(np.argmin(ratio))
    print(f"    lambda_N < 0 for {neg} of {len(lam)} values (N = 1..{len(lam)}); min lambda_N = {lam.min():.6e} at N = {int(N[np.argmin(lam)])}")
    print(f"    min over N >= 2 of lambda_N / (N log N / 2) = {ratio[i]:.6f} at N = {int(N[1:][i])}; at N = {len(lam)}: {ratio[-1]:.6f}")
    print(f"    (Bombieri-Lagarias/Coffey asymptotic under RH: lambda_N ~ (N/2)(log N - log(2 pi) + gamma_E - 1) + ..., i.e. the ratio -> 1 from below;")
    c = (math.log(2 * math.pi) - 0.5772156649015329 + 1)
    print(f"     at N = {len(lam)}: (N/2)(log N - {c:.4f}) = {len(lam)/2*(math.log(len(lam)) - c):.3f} vs lambda_N = {lam[-1]:.3f})")
    out["task5"] = {"n_negative": neg, "min_lambda": float(lam.min()), "min_ratio": float(ratio[i]), "argmin_ratio_N": int(N[1:][i]),
                    "ratio_at_nmax": float(ratio[-1])}


# ----------------------------------------------------------------------------- Task 6: Gaussian face resonance
def task6(args, out):
    banner("TASK 6: Gaussian-face resonance: sup_c prime(c, lam)/A over c in [0, 1e6] vs the coefficient l1 bound")
    sys.path.insert(0, RVM)
    import fixed_width_band as fwb
    from wall_landscape import A_of, f0, N_cutoff, prime_tail_bound, PrimeSide
    ps = PrimeSide(20_000_000)
    cmax = 1e5 if args.quick else 1e6
    h = 0.1
    res = {}
    for lam in (0.7, 1.0):
        # l1 bound over ALL prime powers (cutoff at 1e-6 relative tail + rigorous tail bound), as in fixed_width_band.task1
        lN = N_cutoff(lam, 1e-6)
        k = int(np.searchsorted(ps.logn, lN))
        u = ps.logn[:k]
        wabs = ps.wt[:k] * np.abs(f0(u, lam))
        tailS = prime_tail_bound(min(math.exp(lN), float(ps.nmax)), lam) / A_of(lam)
        S_l1 = 2.0 * wabs.sum() / A_of(lam) + tailS
        # the value at c = 0 (all cosines = 1): the coherent peak, with signs
        P0 = 2.0 * (ps.wt[:k] * f0(u, lam)).sum() / A_of(lam)
        sw = fwb.Sweeper(ps, lam, eps=1e-3)
        sw.prepare(h)
        K = int(cmax / h) + 1
        n_blocks = int(math.ceil(K / sw.J))
        t = time.time()
        sup_all = (-np.inf, None)
        sup_decade = {}
        cands = []
        nb = 512
        for b0 in range(0, n_blocks, nb):
            k0s = np.arange(b0, min(b0 + nb, n_blocks)) * sw.J
            vals = sw.block(k0s)
            cs = (k0s[0] + np.arange(len(vals))) * h
            m = cs <= cmax
            vals, cs = vals[m], cs[m]
            i = int(np.argmax(vals))
            if vals[i] > sup_all[0]:
                sup_all = (float(vals[i]), float(cs[i]))
            for lo, hi in ((0, 10), (10, 100), (100, 1e3), (1e3, 1e4), (1e4, 1e5), (1e5, 1e6)):
                mm = (cs >= lo) & (cs < hi)
                if mm.any():
                    j = int(np.argmax(np.where(mm, vals, -np.inf)))
                    if vals[j] > sup_decade.get((lo, hi), (-np.inf, None))[0]:
                        sup_decade[(lo, hi)] = (float(vals[j]), float(cs[j]))
            idx = np.argsort(vals)[-4:]
            cands += [(float(vals[q]), float(cs[q])) for q in idx]
            mm = cs >= 100.0
            if mm.any():
                idx = np.argsort(np.where(mm, vals, -np.inf))[-4:]
                cands += [(float(vals[q]), float(cs[q])) for q in idx]
        el = time.time() - t

        def refine(cs_):
            best = (-np.inf, None)
            for v, c in sorted(cs_, key=lambda p: -p[0])[:12]:
                loc = c + np.linspace(-h, h, 801)
                loc = loc[loc >= 0]
                pv = sw.direct(loc)
                i = int(np.argmax(pv))
                if pv[i] > best[0]:
                    best = (float(pv[i]), float(loc[i]))
            return best
        sup_r = refine(cands)
        sup_far = refine([p for p in cands if p[1] >= 100.0])
        print(f"\nlam = {lam}: {sw.N} terms at eps = 1e-3 (tail {sw.tail:.1e}), sweep c in [0, {cmax:.0e}] step {h}: {el:.0f}s")
        print(f"    l1 bound S_l1 = 2 sum Lambda n^-1/2 |f0(log n)| / A = {S_l1:.4f} (tail part {tailS:.2e}, {k} prime powers)")
        print(f"    P(0) (all cosines = 1, signed) = {P0:.4f} = {P0/S_l1:.4f} S_l1")
        print(f"    sup on [0, {cmax:.0e}] = {sup_r[0]:.4f} at c = {sup_r[1]:.4f}  ->  sup / S_l1 = {sup_r[0]/S_l1:.4f}")
        print(f"    sup on [100, {cmax:.0e}] (away from the coherent c ~ 0 peak) = {sup_far[0]:.4f} at c = {sup_far[1]:.3f}  ->  {sup_far[0]/S_l1:.4f} S_l1")
        print(f"    per-decade sup of P/A: " + ", ".join(f"[{lo:g},{hi:g}): {v[0]:.3f} (c={v[1]:.2f})" for (lo, hi), v in sorted(sup_decade.items())))
        # heuristic size of c needed to align the K_eff dominant phases within delta: Kronecker box counting
        wts = 2.0 * ps.wt[:k] * np.abs(f0(u, lam)) / A_of(lam)
        order = np.argsort(-wts)
        cum = np.cumsum(wts[order])
        K90 = int(np.searchsorted(cum, 0.9 * cum[-1])) + 1
        # count primes (not prime powers) among the top K90 weights: independent phases
        nprime = int(sum(1 for q in order[:K90] if ps.L[q] == math.log(ps.n[q])))
        print(f"    weight structure: {K90} prime powers carry 90% of the l1 mass, {nprime} of them primes (independent phases);")
        print(f"    to align {nprime} independent phases within 0.1 turn each needs c ~ 10^{nprime} (Kronecker box counting), "
              f"far beyond 1e6: the envelope S_l1 is unreachable in any sweep, consistent with sup/S_l1 stuck at {sup_far[0]/S_l1:.2f} for c >= 100")
        res[str(lam)] = {"S_l1": S_l1, "P0": P0, "sup": sup_r, "sup_over_S": sup_r[0] / S_l1, "sup_far": sup_far, "sup_far_over_S": sup_far[0] / S_l1,
                         "per_decade": {f"{lo:g}-{hi:g}": v for (lo, hi), v in sup_decade.items()}, "K90": K90, "nprime90": nprime,
                         "cmax": cmax, "h": h, "N_terms": sw.N, "secs": el}
    out["task6"] = res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--nmax", type=int, default=2000)
    ap.add_argument("--zeros", type=int, default=100000)
    ap.add_argument("--procs", type=int, default=24)
    ap.add_argument("--skip", default="", help="comma list of task numbers to skip")
    args = ap.parse_args()
    if args.quick:
        args.nmax = min(args.nmax, 300)
        args.zeros = min(args.zeros, 5000)
    skip = set(args.skip.split(",")) if args.skip else set()
    np.seterr(all="ignore")
    T0 = time.time()
    out = {"quick": args.quick, "nmax": args.nmax, "zeros": args.zeros}
    print("conjecture1_proved = False.  Numerics for the Li face brief; nothing here proves RH.")
    lam = None
    if "1" not in skip:
        lam = task1(args, out)
    if "2" not in skip:
        task2(args, out)
    if "3" not in skip:
        task3(args, out)
    if "4" not in skip:
        task4(args, out)
    if "5" not in skip:
        if lam is None:
            lam, _, _ = li_series_flint(args.nmax, int(1.5 * args.nmax) + 400)
        task5(lam, out)
    if "6" not in skip:
        task6(args, out)
    with open(os.path.join(SCRATCH, f"li_face{'_quick' if args.quick else ''}.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    print(f"\ntotal {time.time()-T0:.1f}s")
    print("conjecture1_proved = False  (numerics only; nothing proved)")


if __name__ == "__main__":
    main()

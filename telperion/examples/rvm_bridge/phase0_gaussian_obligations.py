#!/usr/bin/env python3
"""Phase-0 numeric de-risk of the two analytic obligations of E6Bridge6.lean (2026-09-21).

Vocabulary (Zeta23.Defs / E6Bridge6):
    paperFT g z      = int g(u) exp(i z u) du
    gammaOf rho      = (rho - 1/2)/i ;  rho = beta + i t  ->  gamma = t + i (1/2 - beta) =: x + i y
    quadruple images rho, 1 - conj rho, conj rho, 1 - rho  ->  gamma, conj gamma, -conj gamma, -gamma
    gaussTest c lam z = (z - c)^2 exp(-2 lam (z - c)^2)
    zeroSide H       = sum_rho m(rho) H(gammaOf rho)      (over ALL images)
    hermitianTransform g z = h(z) conj(h(conj z)),  h = paperFT g

O2 GaussianDominance: every off-line zero admits (c, lam) with Re zeroSide(gaussTest c lam) < 0.
O1' GaussianApprox : gaussTest c lam is the strip-limit of hermitianTransform(g_n), g_n smooth compactly
                     supported, with a truncation-uniform bound C/(1 + |z|^2).

This script MEASURES; it claims nothing about the true zeros beyond the computed window.
Zeros are on the line to 1e-12 (flint / mpmath); off-line zeros are INJECTED synthetically.
conjecture1_proved = False.

Usage: python3 phase0_gaussian_obligations.py [--quick] [--mode replace|add] [--N 2000]
"""
import argparse
import json
import math
import os
import sys
import time

import numpy as np

SCRATCH = os.environ.get(
    "PHASE0_SCRATCH",
    "/private/tmp/claude-0/-Users-peterwmurphy/466d3ce5-8284-473c-b6b0-031627e4571a/scratchpad/phase0")
os.makedirs(SCRATCH, exist_ok=True)

LAMS = [1, 2, 5, 10, 20, 50, 100, 200]
BETAS = [0.6, 0.55, 0.51, 0.501]
T0S = [50, 1000, 10000]
# zero index near t0 = 10000 (Riemann-von Mangoldt count ~ 10142); window of indices
WINDOW_10000 = (9542, 1200)


# ----------------------------------------------------------------------------- zeros
def load_zeros(N):
    """Ordinates of the first N zeros plus a window around height 10000.  Cached as JSON."""
    path = os.path.join(SCRATCH, f"zeta_zeros_N{N}.json")
    if os.path.exists(path):
        with open(path) as f:
            d = json.load(f)
        return np.array(d["first"]), np.array(d["window10000"]), d["check"]
    t = time.time()
    try:
        import flint
        zs = flint.acb.zeta_zeros(1, N)
        first = [float(z.imag.mid()) for z in zs]
        offline = max(abs(float(z.real.mid()) - 0.5) for z in zs)
        zw = flint.acb.zeta_zeros(*WINDOW_10000)
        window = [float(z.imag.mid()) for z in zw]
        offline = max(offline, max(abs(float(z.real.mid()) - 0.5) for z in zw))
        src = "flint.acb.zeta_zeros"
    except ImportError:
        import mpmath as mp
        mp.mp.dps = 20
        first = [float(mp.zetazero(n).imag) for n in range(1, N + 1)]
        window = [float(mp.zetazero(n).imag)
                  for n in range(WINDOW_10000[0], WINDOW_10000[0] + WINDOW_10000[1])]
        offline = 0.0
        src = "mpmath.zetazero"
    # cross-check a few against mpmath
    import mpmath as mp
    mp.mp.dps = 20
    chk = {}
    for n in [1, 100, N]:
        chk[n] = abs(float(mp.zetazero(n).imag) - first[n - 1])
    n = WINDOW_10000[0] + 600
    chk[n] = abs(float(mp.zetazero(n).imag) - window[600])
    check = {"source": src, "max_|Re-1/2|": offline,
             "mpmath_crosscheck_abs_diff": {str(k): v for k, v in chk.items()},
             "seconds": time.time() - t}
    with open(path, "w") as f:
        json.dump({"first": first, "window10000": window, "check": check}, f)
    return np.array(first), np.array(window), check


# ----------------------------------------------------------------------------- Part A
def gauss_term(w, lam):
    """gaussTest at w = z - c (vectorised, complex)."""
    return w ** 2 * np.exp(-2.0 * lam * w ** 2)


def zero_side(c, lam, tline, quads):
    """Re zeroSide(gaussTest c lam) split into components.

    tline : ordinates t > 0 of on-line zeros (each contributes images t and -t, y = 0)
    quads : list of (beta, t0) injected off-line zeros, each contributing the 4 images
    """
    x = tline - c
    bg = gauss_term(x.astype(complex), lam).real.sum()          # images  gamma = t
    bg_neg = gauss_term((-tline - c).astype(complex), lam).real.sum()  # images gamma = -t
    pair = 0.0
    pair_far = 0.0
    for beta, t0 in quads:
        y = 0.5 - beta
        w = (t0 - c) + 1j * y
        pair += 2.0 * gauss_term(w, lam).real                    # gamma, conj gamma
        wf = (-t0 - c) + 1j * y
        pair_far += 2.0 * gauss_term(wf, lam).real               # -gamma, -conj gamma
    return {"total": bg + bg_neg + pair + pair_far, "bg": bg, "bg_neg": bg_neg,
            "pair": pair, "pair_far": pair_far}


def zero_side_grid(cs, lam, tline, quads):
    """Vectorised Re zeroSide over a grid of centres cs (float array)."""
    X = tline[None, :] - cs[:, None]
    S = (X ** 2 * np.exp(-2.0 * lam * X ** 2)).sum(axis=1)
    Xn = -tline[None, :] - cs[:, None]
    S += (Xn ** 2 * np.exp(-2.0 * lam * Xn ** 2)).sum(axis=1)
    for beta, t0 in quads:
        y = 0.5 - beta
        w = (t0 - cs) + 1j * y
        S += 2.0 * gauss_term(w, lam).real
        wf = (-t0 - cs) + 1j * y
        S += 2.0 * gauss_term(wf, lam).real
    return S


def inject(tline, beta, t0, mode):
    """Return (on-line ordinates after injection, quads, info)."""
    i = int(np.argmin(np.abs(tline - t0)))
    tnear = tline[i]
    if mode == "replace":
        tl = np.delete(tline, i)
    else:
        tl = tline
    # nearest surviving on-line zero to t0
    x1 = float(np.min(np.abs(tl - t0)))
    return tl, [(beta, t0)], {"t_near_removed": float(tnear) if mode == "replace" else None,
                              "dist_t0_to_replaced": float(abs(tnear - t0)),
                              "x1_nearest_online_after": x1}


def crossover(tline, quads, c, lo=1e-2, hi=1e6, ngrid=600):
    """Smallest lam with S(c, lam) < 0 on a log grid, refined by bisection.  None if never."""
    grid = np.exp(np.linspace(math.log(lo), math.log(hi), ngrid))
    vals = np.array([zero_side(c, l, tline, quads)["total"] for l in grid])
    neg = np.where(vals < 0)[0]
    if len(neg) == 0:
        return None, False
    k = neg[0]
    if k == 0:
        return grid[0], bool((vals[k:] < 0).all())
    a, b = grid[k - 1], grid[k]
    for _ in range(60):
        m = math.sqrt(a * b)
        if zero_side(c, m, tline, quads)["total"] < 0:
            b = m
        else:
            a = m
    stays_neg = bool((vals[k:] < 0).all())
    return b, stays_neg


def tail_bound(c, lam, tincl):
    """Analytic bound on the omitted on-line images beyond the included ordinates.

    Uses density (1/2pi) log(T/2pi) + 1 (crude majorant of the local count) times
    2 int_X^inf x^2 exp(-2 lam x^2) dx, X = distance from c to the nearer edge of the window.
    """
    from math import erfc, sqrt, pi, exp, log
    X = min(abs(tincl.max() - c), abs(c - tincl.min()))
    if X <= 0:
        return float("inf"), X
    dens = log(max(tincl.max(), 20.0) / (2 * pi)) / (2 * pi) + 1.0
    integral = X * exp(-2 * lam * X * X) / (4 * lam) + sqrt(pi / (2 * lam)) * erfc(X * sqrt(2 * lam)) / (8 * lam)
    return 2 * dens * integral, X


def part_a(first, window, args, out):
    print("\n" + "=" * 78)
    print("PART A: O2 GaussianDominance on real zeros + injected off-line quadruple")
    print("=" * 78)
    mode = args.mode
    print(f"injection mode = {mode}   (replace: drop the on-line zero nearest t0, insert quadruple at (beta, t0))")
    N = len(first)

    def zeros_for(t0):
        return window if t0 == 10000 else first

    # ---------------- control: no injection, S >= 0 everywhere
    print("\n[A.0] CONTROL (no injected zero): min over c-grid x lam of Re zeroSide(gaussTest)")
    ctrl = {}
    for t0 in T0S:
        tl = zeros_for(t0)
        cs = np.arange(t0 - 3, t0 + 3 + 1e-9, 0.01)
        mn, arg = float("inf"), None
        for lam in LAMS:
            S = zero_side_grid(cs, lam, tl, [])
            j = int(np.argmin(S))
            if S[j] < mn:
                mn, arg = float(S[j]), (float(cs[j]), lam)
        ctrl[t0] = {"min": mn, "at": arg}
        print(f"  t0={t0:6d}: min S = {mn:.6e} at c={arg[0]:.2f}, lam={arg[1]}   (>= 0: {mn >= 0})")
    out["control"] = ctrl

    # ---------------- (i) at c = t0 exactly + (iii) crossover table
    print("\n[A.i / A.iii] c = t0 EXACTLY: components, smallest listed lam with S<0, continuous crossover lam*")
    print("  y = 1/2 - beta (sign irrelevant: pair {gamma, conj gamma} is even in y); pair = -2 y^2 e^{2 lam y^2} at x=0; bg = on-line background")
    print("  x1 = distance from t0 to the nearest surviving on-line zero; B(1) = bg at lam=1; 'stays<0' = S<0 for all lam >= lam* on the log grid")
    print("  lam_paper = (1/(2y^2)) log(B(1)/(2y^2)) with the lam=1 background B(1) held fixed")
    print("  lam_nn    = log(x1^2/y^2) / (2 (x1^2 + y^2))  nearest-on-line-zero model, both images at distance x1 (conservative)")
    print("  lam_nn1   = log(x1^2/(2 y^2)) / (2 (x1^2 + y^2))  same with the single image t1 - c = x1 (optimistic)")
    rows = []
    hdr = f"{'beta':>6} {'t0':>6} {'y':>6} {'x1':>7} {'B(1)':>9} {'first lam<0':>11} {'lam*':>10} {'lam_paper':>10} {'lam_nn1':>8} {'lam_nn':>8} {'stays<0':>7}"
    print("  " + hdr)
    for t0 in T0S:
        tl0 = zeros_for(t0)
        for beta in BETAS:
            y = 0.5 - beta
            tl, quads, info = inject(tl0, beta, t0, mode)
            x1 = info["x1_nearest_online_after"]
            comps = {lam: zero_side(t0, lam, tl, quads) for lam in LAMS}
            first_neg = next((lam for lam in LAMS if comps[lam]["total"] < 0), None)
            lam_star, stays = crossover(tl, quads, t0)
            B1 = comps[1]["bg"] + comps[1]["bg_neg"]
            lam_paper = math.log(B1 / (2 * y * y)) / (2 * y * y) if B1 > 2 * y * y else float("nan")
            lam_nn = math.log(x1 * x1 / (y * y)) / (2 * (x1 * x1 + y * y))
            lam_nn1 = math.log(x1 * x1 / (2 * y * y)) / (2 * (x1 * x1 + y * y))
            rows.append({"beta": beta, "t0": t0, "y": y, "x1": x1, "B1": B1, "first_neg_lam": first_neg,
                         "lam_star": lam_star, "lam_paper": lam_paper, "lam_nn": lam_nn, "lam_nn1": lam_nn1, "stays_neg": stays,
                         "components": {str(l): comps[l] for l in LAMS}, "inject": info})
            ls = f"{lam_star:10.4g}" if lam_star is not None else f"{'none':>10}"
            lp = f"{lam_paper:10.4g}" if lam_paper == lam_paper else f"{'<=0':>10}"
            print(f"  {beta:6.3f} {t0:6d} {y:+6.3f} {x1:7.3f} {B1:9.3e} {str(first_neg):>11} {ls} {lp} {lam_nn1:8.3f} {lam_nn:8.3f} {str(stays):>7}")
    out["c_eq_t0"] = rows
    # component detail for one case per t0
    print("\n  component detail (beta=0.51, |y|=0.01) at c=t0:")
    for r in rows:
        if r["beta"] == 0.51:
            print(f"   t0={r['t0']}: " + "  ".join(
                f"lam={l}: S={r['components'][str(l)]['total']:+.3e} (bg {r['components'][str(l)]['bg']:.3e}, pair {r['components'][str(l)]['pair']:+.3e})"
                for l in [1, 10, 50, 200]))

    # ---------------- (ii) c off t0
    print("\n[A.ii] c = t0 + delta, delta in [-3, 3] step 0.01: sign structure of S(c, lam)")
    print("  band = |delta| < y (pair exponent y^2 - delta^2 > 0).  Reported per lam: fraction of grid with S<0,")
    print("  number of sign changes along c, fraction of the band with S<0, and whether S<0 occurs outside the band.")
    grid_out = {}
    for t0 in T0S:
        tl0 = zeros_for(t0)
        for beta in BETAS:
            y = 0.5 - beta
            tl, quads, info = inject(tl0, beta, t0, mode)
            cs = np.arange(t0 - 3, t0 + 3 + 1e-9, 0.01)
            band = np.abs(cs - t0) < abs(y)
            line = []
            rec = {}
            for lam in LAMS:
                S = zero_side_grid(cs, lam, tl, quads)
                sg = np.sign(S)
                changes = int((sg[1:] * sg[:-1] < 0).sum())
                frac = float((S < 0).mean())
                fband = float((S[band] < 0).mean()) if band.any() else float("nan")
                outside = bool((S[~band] < 0).any())
                rec[str(lam)] = {"frac_neg": frac, "sign_changes": changes, "frac_band_neg": fband,
                                 "neg_outside_band": outside, "minS": float(S.min()),
                                 "c_at_min": float(cs[int(np.argmin(S))])}
                line.append(f"lam={lam:3d}: neg {frac:5.3f} chg {changes:3d} band {fband:4.2f} out {'Y' if outside else 'n'}")
            grid_out[f"{beta}_{t0}"] = rec
            print(f"  beta={beta:5.3f} t0={t0:5d} (y={y:+.3f}, band |delta|<{abs(y):.3f} = {int(band.sum())} grid pts)")
            for i in range(0, len(line), 2):
                print("     " + " | ".join(line[i:i + 2]))
            if args.save_grids:
                np.savez(os.path.join(SCRATCH, f"grid_{beta}_{t0}.npz"), cs=cs,
                         **{f"lam{l}": zero_side_grid(cs, l, tl, quads) for l in LAMS})
    out["c_grid"] = grid_out

    # genericity: large-lam sign as a function of delta, compared with the tie rule x1(c)^2 = delta^2 - y^2
    print("\n[A.ii-b] GENERICITY: large-lam sign of S vs the exponent race (pair: y^2-delta^2, on-line: -x1(c)^2)")
    print("  predicted: pair dominates (sign oscillates in lam) iff y^2 - delta^2 > -x1(c)^2; tie set = bad c (measure zero)")
    gen = {}
    for t0 in [50, 1000]:
        tl0 = zeros_for(t0)
        beta = 0.55
        y = 0.5 - beta
        tl, quads, info = inject(tl0, beta, t0, mode)
        cs = np.arange(t0 - 3, t0 + 3 + 1e-9, 0.01)
        x1c = np.min(np.abs(tl[None, :] - cs[:, None]), axis=1)
        pair_dom = (y * y - (cs - t0) ** 2) > -(x1c ** 2)
        S200 = zero_side_grid(cs, 200, tl, quads)
        S500 = zero_side_grid(cs, 500, tl, quads)
        pred_pos = ~pair_dom
        # where on-line dominates, S must be > 0 at large lam
        viol = int(((S200 < 0) & pred_pos).sum()) + int(((S500 < 0) & pred_pos).sum())
        neg_any = (S200 < 0) | (S500 < 0)
        margin = np.abs((y * y - (cs - t0) ** 2) + x1c ** 2)
        gen[t0] = {"frac_pair_dominated": float(pair_dom.mean()), "violations_of_prediction": viol,
                   "frac_neg_at_lam200_or_500_within_pair_dominated": float(neg_any[pair_dom].mean()),
                   "min_exponent_margin_on_grid": float(margin.min())}
        print(f"  t0={t0}, beta={beta}: pair-dominated fraction of grid {pair_dom.mean():.3f}; "
              f"S<0 (lam 200 or 500) inside it: {neg_any[pair_dom].mean():.3f}; "
              f"S<0 where on-line should dominate: {viol} grid pts; min |exponent gap| on grid {margin.min():.2e}")
    out["genericity"] = gen

    # ---------------- (iv) truncation
    print("\n[A.iv] TRUNCATION at c = t0 (beta=0.55): S using only on-line zeros with |t - t0| <= X, vs all cached zeros,")
    print("  and the analytic tail bound 2 (log(T/2pi)/2pi + 1) int_X^inf x^2 e^{-2 lam x^2} dx.  Also N=1000 vs N=2000.")
    tr = {}
    for t0 in T0S:
        tl0 = zeros_for(t0)
        tl, quads, _ = inject(tl0, 0.55, t0, mode)
        for lam in [1, 5, 20]:
            full = zero_side(t0, lam, tl, quads)["total"]
            line = []
            rec = {"S_all": full}
            for X in [1, 2, 3, 5, 10]:
                sub = tl[np.abs(tl - t0) <= X]
                Sx = zero_side(t0, lam, sub, quads)["total"]
                bound, _ = tail_bound(t0, lam, np.array([t0 - X, t0 + X]))
                rec[f"X{X}"] = {"omitted": full - Sx, "bound": bound}
                line.append(f"X={X:2d}: omitted {full-Sx:8.1e} <= bound {bound:8.1e}{'' if full-Sx <= bound*1.0000001 else ' VIOLATED'}")
            if t0 != 10000:
                r1 = zero_side(t0, lam, inject(first[:1000], 0.55, t0, mode)[0], quads)["total"]
                rec["S_N1000"] = r1
                line.append(f"N1000 vs N{N}: diff {full-r1:.1e}")
            tr[f"{t0}_{lam}"] = rec
            print(f"  t0={t0:5d} lam={lam:3d} S_all={full:+.6e}: " + " | ".join(line))
    out["truncation"] = tr


# ----------------------------------------------------------------------------- Part B
def K_const(lam):
    """paperFT[K u e^{-u^2/(4 lam)} e^{-icu}](z) = (z-c) e^{-lam (z-c)^2}  <=>  K = -i /(4 sqrt(pi) lam^{3/2})."""
    return -1j / (4.0 * math.sqrt(math.pi) * lam ** 1.5)


def phi(u, lam, c):
    return K_const(lam) * u * np.exp(-u * u / (4.0 * lam)) * np.exp(-1j * c * u)


def h_exact(z, lam, c):
    w = z - c
    return w * np.exp(-lam * w * w)


def gauss_test(z, lam, c):
    w = z - c
    return w ** 2 * np.exp(-2.0 * lam * w ** 2)


def _F(s):
    return np.where(s > 0, np.exp(-1.0 / np.maximum(s, 1e-300)), 0.0)


def chi(t):
    """C^infty cutoff: 1 on |t|<=1, 0 on |t|>=2 (standard exp(-1/s) construction)."""
    a = np.abs(t)
    num = _F(2.0 - a)
    den = num + _F(a - 1.0)
    return np.where(den > 0, num / np.where(den > 0, den, 1.0), 0.0)


def verify_K(lam, c):
    """mpmath quad of phi(u) e^{izu} vs h(z) at 5 strip points."""
    import mpmath as mp
    mp.mp.dps = 30
    K = mp.mpc(0, -1) / (4 * mp.sqrt(mp.pi) * mp.mpf(lam) ** mp.mpf(1.5))
    zs = [mp.mpc(c, 0), mp.mpc(c + 0.3, 0.5), mp.mpc(c - 1.1, -0.5), mp.mpc(c + 2.0, 0.25), mp.mpc(c - 3.0, 0.5)]
    worst = 0.0
    for z in zs:
        f = lambda u: K * u * mp.exp(-u * u / (4 * lam)) * mp.exp(-1j * c * u) * mp.exp(1j * z * u)
        R = 12 * math.sqrt(lam) + 5
        val = mp.quad(f, mp.linspace(-R, R, 41))
        ex = (z - c) * mp.exp(-lam * (z - c) ** 2)
        worst = max(worst, float(abs(val - ex)))
    return worst


def transform_on_grid(n, lam, c, xs, du):
    """h_n(z) = trapezoid int_{-2n}^{2n} phi(u) chi(u/n) e^{izu} du at z = xs + i*{-1/2,0,1/2}."""
    u = np.arange(-2.0 * n, 2.0 * n + du / 2, du)
    g = phi(u, lam, c) * chi(u / n)
    # trapezoid weights (g vanishes at the ends so plain sum is the trapezoid rule)
    rows = {}
    for im in (-0.5, 0.0, 0.5):
        vals = np.empty(len(xs), dtype=complex)
        ew = np.exp(-im * u)  # e^{i (x + i im) u} = e^{i x u} e^{-im u}
        gw = g * ew
        CH = 128
        for k in range(0, len(xs), CH):
            xb = xs[k:k + CH]
            E = np.exp(1j * np.outer(xb, u))
            vals[k:k + CH] = E @ gw * du
        rows[im] = vals
    return u, g, rows


def ibp_constants(u, g, du):
    """int |g^{(k)}(u)| e^{|u|/2} du for k = 0,1,2 (constants from k integrations by parts on the strip)."""
    w = np.exp(np.abs(u) / 2)
    g1 = np.gradient(g, du)
    g2 = np.gradient(g1, du)
    return [float((np.abs(gk) * w).sum() * du) for gk in (g, g1, g2)]


def part_b(args, out):
    print("\n" + "=" * 78)
    print("PART B: O1' GaussianApprox constants")
    print("=" * 78)
    print("[B.0] K = -i / (4 sqrt(pi) lam^{3/2}); check paperFT[phi] = (z-c) e^{-lam (z-c)^2} at 5 strip points (mpmath)")
    kchk = {}
    for lam in (1, 10):
        for c in (0, 50):
            e = verify_K(lam, c)
            kchk[f"{lam}_{c}"] = e
            print(f"  lam={lam:2d} c={c:2d}: max |quad - h| = {e:.2e}  ({'OK' if e < 1e-10 else 'FAIL'} at 1e-10)")
    out["K_check"] = kchk

    du = 0.008 if args.quick else 0.004
    xstep = 1.0 if args.quick else 0.5
    ns = [1, 2, 4, 8, 16] if args.quick else [1, 2, 4, 8, 16, 32, 64]
    xs = np.arange(-200.0, 200.0 + 1e-9, xstep)
    print(f"\n[B.1] strip grid Re z in [-200,200] step {xstep}, Im z in {{-1/2,0,1/2}}; u-grid du={du}; n in {ns}")
    print("  columns: sup(1+|z|)|h_n|  sup(1+|z|^2)|h_n|  sup(1+|z|^2)|H_n|  sup(1+|z|^2)^2|H_n|  max|H_n-G|  max|h_n-h|  T0 T1 T2")
    print("  T_k = int |g_n^{(k)}| e^{|u|/2} du (k integrations by parts give |h_n(z)| <= T_k/|Re z|^k on the strip)")
    res = {}
    for lam in (1, 10):
        for c in (0, 50):
            climit = max(float(np.max((1 + np.abs(xs + 1j * im) ** 2) * np.abs(gauss_test(xs + 1j * im, lam, c))))
                         for im in (-0.5, 0, 0.5))
            res[f"{lam}_{c}_limit"] = climit
            print(f"  --- lam={lam}, c={c}   (limit G itself: sup(1+|z|^2)|G| on grid = {climit:.4g})")
            for n in ns:
                t = time.time()
                u, g, rows = transform_on_grid(n, lam, c, xs, du)
                T = ibp_constants(u, g, du)
                sup1 = sup2 = supH = supH2 = errH = errh = 0.0
                for im in (-0.5, 0.0, 0.5):
                    z = xs + 1j * im
                    hn = rows[im]
                    Hn = hn * np.conj(rows[-im])
                    az = np.abs(z)
                    sup1 = max(sup1, float(np.max((1 + az) * np.abs(hn))))
                    sup2 = max(sup2, float(np.max((1 + az ** 2) * np.abs(hn))))
                    supH = max(supH, float(np.max((1 + az ** 2) * np.abs(Hn))))
                    supH2 = max(supH2, float(np.max((1 + az ** 2) ** 2 * np.abs(Hn))))
                    errH = max(errH, float(np.max(np.abs(Hn - gauss_test(z, lam, c)))))
                    errh = max(errh, float(np.max(np.abs(hn - h_exact(z, lam, c)))))
                res[f"{lam}_{c}_{n}"] = {"sup_1z_h": sup1, "sup_1z2_h": sup2, "sup_1z2_H": supH,
                                         "sup_1z2sq_H": supH2, "err_H": errH, "err_h": errh, "T": T}
                print(f"   n={n:2d}: {sup1:10.4g} {sup2:10.4g} {supH:10.4g} {supH2:12.4g} {errH:10.3e} {errh:10.3e}  "
                      f"{T[0]:.3g} {T[1]:.3g} {T[2]:.3g}   [{time.time()-t:.1f}s]")
    out["strip"] = res
    # trapezoid self-check: halve du on one case
    print("\n[B.2] quadrature self-check (n=1, lam=10, c=50): max |h_n(du) - h_n(du/2)| on the strip grid")
    _, _, r1 = transform_on_grid(1, 10, 50, xs, du)
    _, _, r2 = transform_on_grid(1, 10, 50, xs, du / 2)
    d = max(float(np.max(np.abs(r1[im] - r2[im]))) for im in (-0.5, 0.0, 0.5))
    print(f"  {d:.3e}")
    out["quad_selfcheck"] = d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--mode", choices=["replace", "add"], default="replace")
    ap.add_argument("--N", type=int, default=2000)
    ap.add_argument("--save-grids", action="store_true")
    ap.add_argument("--skip-b", action="store_true")
    args = ap.parse_args()
    np.seterr(all="ignore")
    t = time.time()
    first, window, check = load_zeros(args.N)
    print(f"zeros: first {len(first)} (t <= {first[-1]:.2f}) + window of {len(window)} around 10000 "
          f"(t in [{window[0]:.1f}, {window[-1]:.1f}]); source {check['source']}; "
          f"max |Re rho - 1/2| = {check['max_|Re-1/2|']:.1e}; mpmath cross-check {check['mpmath_crosscheck_abs_diff']}")
    out = {"args": vars(args), "zeros_check": check}
    part_a(first, window, args, out)
    if not args.skip_b:
        part_b(args, out)
    with open(os.path.join(SCRATCH, f"results_{args.mode}{'_quick' if args.quick else ''}.json"), "w") as f:
        json.dump(out, f, indent=1, default=str)
    print(f"\ntotal {time.time()-t:.1f}s; results json in {SCRATCH}")
    print("conjecture1_proved = False  (numerics only; nothing proved about the true zero set)")


if __name__ == "__main__":
    main()

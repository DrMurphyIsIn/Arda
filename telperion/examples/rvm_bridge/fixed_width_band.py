#!/usr/bin/env python3
"""Fixed-width band closure feasibility (2026-09-21): can the residual at a FIXED width lam be closed from primes alone?

At fixed lam,  F(c, lam) = arch(c, lam) - prime(c, lam)  with (see wall_landscape.py, verified there to 1e-15)
    prime(c, lam) = 2 sum_n Lambda(n) n^{-1/2} cos(c log n) f0(log n),   f0(u) = A (1 - u^2/4lam) e^{-u^2/8lam},
    arch(c, lam)  = 2 Re G(i/2) + (1/2pi) int G(r) Re digamma(1/4 + ir/2) dr - A log pi  ~  A log(c/2pi),
so prime/A is a trigonometric polynomial in c with frequencies log n (Gaussian-damped beyond log n ~ 2 lam + O(sqrt lam))
and arch/A grows like log c.  Positivity for ALL c at ONE lam is not RH (only "for all lam" is).

Tasks: (1) N_eff, trivial sup S_triv, archimedean floor, c_triv(lam); (2) the actual sup of prime/A and min of F/A on
[0, min(c_triv, 1e7)] by a dense sweep (block-Vandermonde matmul); (3) zero-side cross-check at c ~ 6.4e5 and 1e6 with
flint zeros; (4) the detection floor y0(lam, t): what fixed-width positivity would say about zeros.

Everything MEASURES (float, not interval).  conjecture1_proved = False.
Usage: python3 fixed_width_band.py [--quick]
"""
import argparse
import json
import math
import os
import sys
import time

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import digamma

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from wall_landscape import A_of, f0, PrimeSide, prime_tail_bound, N_cutoff, solve_y0, SCRATCH  # noqa: E402

T_LADDER = 640000.0
D_LADDER = 2.0
LAMS_ALL = [0.3, 0.5, 0.7, 1.0, 1.5, 2.0]
LAMS_SWEEP = [0.3, 0.5, 0.7, 1.0]
C_FLOOR = [1e3, 1e4, 1e5, 6.4e5, 1e6, 1e7, 1e8, 1e9, 1e12]
LOG_TAIL = 46.0


# ----------------------------------------------------------------------------- archimedean side, offset form
def psi_over_A(c, lam, n=32):
    """(1/2pi) int G(c+w) Re digamma(1/4 + i(c+w)/2) dw / A, built in the offset w (c up to 1e12 is fine)."""
    R = math.sqrt(LOG_TAIL / (2.0 * lam))
    npan = max(8, int(math.ceil(2.0 * R)))
    edges = np.linspace(-R, R, npan + 1)
    x, wts = leggauss(n)
    a, b = edges[:-1], edges[1:]
    w = (0.5 * (b - a))[:, None] * x[None, :] + (0.5 * (a + b))[:, None]
    vals = w * w * np.exp(-2.0 * lam * w * w) * digamma(0.25 + 0.5j * (c + w)).real
    val = ((vals * wts[None, :]).sum(axis=1) * 0.5 * (b - a)).sum()
    return val / (2.0 * math.pi) / A_of(lam)


def pole_over_A(c, lam):
    if c > 200.0:
        return 0.0
    w = 0.5j - c
    return 2.0 * (w * w * np.exp(-2.0 * lam * w * w)).real / A_of(lam)


def arch_over_A(c, lam):
    return pole_over_A(c, lam) + psi_over_A(c, lam) - math.log(math.pi)


# ----------------------------------------------------------------------------- Task 1
def task1(ps, out):
    print("\n" + "=" * 100)
    print("TASK 1: N_eff, trivial sup bound S_triv, archimedean floor arch/A, and c_triv(lam)")
    print("=" * 100)
    print("N_eff = # prime powers n <= N(lam, 1e-6) (tail of 2 sum Lambda n^{-1/2} |f0| below 1e-6 A); S_triv = 2 sum Lambda n^{-1/2} |f0(log n)| / A")
    print("L = 2 sum Lambda n^{-1/2} |f0(log n)| log n / A = Lipschitz constant of prime/A in c; arch/A ~ log(c/2pi) for c >> 1")
    print(f"{'lam':>5} {'log N':>6} {'N_eff':>7} {'S_triv':>8} {'L':>8} | " + " ".join(f"{c:>8.0e}" for c in C_FLOOR) + f" | {'c_triv':>9}")
    res = {}
    for lam in LAMS_ALL:
        lN = N_cutoff(lam, 1e-6)
        k = int(np.searchsorted(ps.logn, lN))
        limited = k >= len(ps.logn)
        u = ps.logn[:k]
        wabs = ps.wt[:k] * np.abs(f0(u, lam))
        tailS = prime_tail_bound(min(math.exp(lN), float(ps.nmax)), lam) / A_of(lam)
        S = 2.0 * wabs.sum() / A_of(lam) + tailS
        L = 2.0 * (wabs * u).sum() / A_of(lam)
        floor = [arch_over_A(c, lam) for c in C_FLOOR]
        # c_triv: arch/A = S_triv (arch/A increasing in c for c > 50)
        lo, hi = math.log(50.0), math.log(1e200)
        if S > 500 or arch_over_A(math.exp(hi), lam) < S:
            ctriv = float("inf")
        else:
            for _ in range(200):
                mid = 0.5 * (lo + hi)
                if arch_over_A(math.exp(mid), lam) >= S:
                    hi = mid
                else:
                    lo = mid
            ctriv = math.exp(hi)
        res[str(lam)] = {"logN": lN, "N_eff": k, "nmax_limited": limited, "S_triv": S, "S_tail_part": tailS, "L": L,
                         "floor": dict(zip(map(str, C_FLOOR), floor)), "c_triv": ctriv}
        print(f"{lam:5g} {lN:6.2f} {k:7d}{'+' if limited else ' '}{S:8.3f} {L:8.2f} | " + " ".join(f"{v:8.3f}" for v in floor) + f" | {ctriv:9.3g}"
              + (f"   (N_eff nmax-limited; tail part of S_triv = {tailS:.2f})" if limited else ""))
    out["task1"] = res
    return res


# ----------------------------------------------------------------------------- Task 2
class Sweeper:
    """prime(c)/A on c = c0 + k h via blocks: P[k0 + j] = Re sum_n (a_n e^{i k0 h w_n}) e^{i j h w_n}, one J x N table."""

    def __init__(self, ps, lam, eps=1e-3, J=1024):
        lN = N_cutoff(lam, eps)
        k = int(np.searchsorted(ps.logn, lN))
        self.w = ps.logn[:k].copy()
        self.a = (2.0 * ps.wt[:k] * f0(self.w, lam) / A_of(lam)).astype(complex)
        self.tail = prime_tail_bound(min(math.exp(lN), float(ps.nmax)), lam) / A_of(lam)
        self.N = k
        self.J = J
        self.lam = lam

    def prepare(self, h):
        self.h = h
        self.Z = np.exp(1j * h * np.outer(np.arange(self.J), self.w))     # J x N

    def block(self, k0s):
        """values at c = (k0 + j) h for each k0 in k0s (array) and j in 0..J-1; returns (len(k0s)*J,) in c order."""
        B = self.a[:, None] * np.exp(1j * self.h * np.outer(self.w, k0s))   # N x nb
        return (self.Z @ B).real.T.ravel()

    def direct(self, cs):
        cs = np.atleast_1d(np.asarray(cs, dtype=float))
        return (np.exp(1j * np.outer(cs, self.w)) @ self.a).real


def sweep(ps, lam, cmax, h, quick, out, t1):
    sw = Sweeper(ps, lam, eps=1e-3)
    sw.prepare(h)
    nb = 1024
    K = int(cmax / h) + 1
    n_blocks = int(math.ceil(K / sw.J))
    print(f"\n  lam={lam}: sweep c in [0, {cmax:.4g}] step h={h}, {K} points, N={sw.N} terms (tail {sw.tail:.1e}), "
          f"{n_blocks} blocks of {sw.J} in batches of {nb}")
    t = time.time()
    # archimedean floor on a log grid in c for interpolation (smooth in log c); exact below 200
    cg = np.concatenate([np.linspace(0.0, 200.0, 2001), np.exp(np.linspace(math.log(200.0), math.log(cmax * 1.01), 400))[1:]])
    ag = np.array([arch_over_A(c, lam) for c in cg])
    best = {"sup": (-np.inf, None), "inf": (np.inf, None), "minF": (np.inf, None), "minF_band": (np.inf, None),
            "minF_mid": (np.inf, None), "minF_low": (np.inf, None), "sup_band": (-np.inf, None)}
    checkpoints = {}
    top_sup, top_minF = [], []
    for b0 in range(0, n_blocks, nb):
        k0s = np.arange(b0, min(b0 + nb, n_blocks)) * sw.J
        vals = sw.block(k0s)
        cs = (k0s[0] + np.arange(len(vals))) * h
        m = cs <= cmax
        vals, cs = vals[m], cs[m]
        FA = np.interp(cs, cg, ag) - vals
        i = int(np.argmax(vals))
        if vals[i] > best["sup"][0]:
            best["sup"] = (float(vals[i]), float(cs[i]))
        i = int(np.argmin(vals))
        if vals[i] < best["inf"][0]:
            best["inf"] = (float(vals[i]), float(cs[i]))
        i = int(np.argmin(FA))
        if FA[i] < best["minF"][0]:
            best["minF"] = (float(FA[i]), float(cs[i]))
        ml = (cs >= 14.0) & (cs < 200.0)
        if ml.any():
            j = int(np.argmin(np.where(ml, FA, np.inf)))
            if FA[j] < best["minF_low"][0]:
                best["minF_low"] = (float(FA[j]), float(cs[j]))
        mm = (cs >= 200.0) & (cs < T_LADDER - D_LADDER)
        if mm.any():
            j = int(np.argmin(np.where(mm, FA, np.inf)))
            if FA[j] < best["minF_mid"][0]:
                best["minF_mid"] = (float(FA[j]), float(cs[j]))
        mb = cs >= T_LADDER - D_LADDER
        if mb.any():
            j = int(np.argmin(np.where(mb, FA, np.inf)))
            if FA[j] < best["minF_band"][0]:
                best["minF_band"] = (float(FA[j]), float(cs[j]))
            j = int(np.argmax(np.where(mb, vals, -np.inf)))
            if vals[j] > best["sup_band"][0]:
                best["sup_band"] = (float(vals[j]), float(cs[j]))
        for ck in (1e3, 1e4, 1e5, 1e6, 3e6, 1e7):
            if cs[0] <= ck and ck not in checkpoints and cs[-1] >= ck:
                checkpoints[ck] = best["sup"][0]
        # keep candidates for refinement
        idx = np.argsort(vals)[-3:]
        top_sup += [(float(vals[q]), float(cs[q])) for q in idx]
        idx = np.argsort(np.where(mb, FA, np.inf))[:3] if mb.any() else []
        top_minF += [(float(FA[q]), float(cs[q])) for q in idx]
    el = time.time() - t
    # refine: fine local grid (h/200) around the best candidates
    def refine(cands, sign):
        bestv, bestc = None, None
        for v, c in sorted(cands, key=lambda p: -sign * p[0])[:8]:
            loc = c + np.linspace(-h, h, 401)
            loc = loc[loc >= 0]
            pv = sw.direct(loc)
            fv = pv if sign > 0 else np.array([arch_over_A(x, lam) for x in loc]) - pv
            i = int(np.argmax(fv)) if sign > 0 else int(np.argmin(fv))
            if bestv is None or (sign > 0 and fv[i] > bestv) or (sign < 0 and fv[i] < bestv):
                bestv, bestc = float(fv[i]), float(loc[i])
        return bestv, bestc
    sup_r = refine(top_sup, +1)
    minF_r = refine(top_minF, -1) if top_minF else (None, None)
    S = t1[str(lam)]["S_triv"]
    L = t1[str(lam)]["L"]
    print(f"    sweep {el:.0f}s.  sup prime/A = {best['sup'][0]:.4f} at c={best['sup'][1]:.2f} (refined {sup_r[0]:.4f} at {sup_r[1]:.4f}); "
          f"S_triv = {S:.3f}; ratio sup/S_triv = {sup_r[0]/S:.3f}")
    print(f"    inf prime/A = {best['inf'][0]:.4f} at c={best['inf'][1]:.2f};  running sup prime/A over [0, X]: "
          + ", ".join(f"X={k:.0e}: {v:.3f}" for k, v in sorted(checkpoints.items())))
    print(f"    min F/A over [0, 14]      = {best['minF'][0]:+.3e} at c={best['minF'][1]:.3f}  (no zeros: F exponentially small, float noise)")
    print(f"    min F/A over [14, 200]    = {best['minF_low'][0]:+.4e} at c={best['minF_low'][1]:.4f}  (isolated low zeros: F ~ 0 at c = t_j, ladder territory)")
    if best["minF_mid"][1] is not None:
        print(f"    min F/A over [200, T-D]   = {best['minF_mid'][0]:+.4f} at c={best['minF_mid'][1]:.3f}  (ladder territory)")
    if best["minF_band"][1] is not None:
        print(f"    BAND [T-D, {cmax:.3g}]: sup prime/A = {best['sup_band'][0]:.4f} at c={best['sup_band'][1]:.2f}; "
              f"min F/A = {best['minF_band'][0]:.4f} at c={best['minF_band'][1]:.3f} (refined {minF_r[0]:.4f} at {minF_r[1]:.4f})")
        mv = minF_r[0]
        margin = mv - sw.tail - 1e-6
        if margin <= 0:
            print(f"    certificate: NO margin ({mv:.3e} minus tail {sw.tail:.1e})")
        else:
            h_cert = margin / L
            ctriv = t1[str(lam)]["c_triv"]
            for name, hi in (("to cmax", cmax), ("to c_triv (margin extrapolated, optimistic)", ctriv)):
                n_eval = (hi - (T_LADDER - D_LADDER)) / h_cert
                n_terms = n_eval * t1[str(lam)]["N_eff"]
                print(f"    certificate {name}: margin {margin:.3f}, L {L:.1f}, h_cert {h_cert:.2e}, evals {n_eval:.2e}, interval terms {n_terms:.2e}"
                      f" -> arb ~3e6/s: {n_terms/3e6/3600:.3g} h; float+error-bound ~1e9/s: {n_terms/1e9/3600:.3g} h")
    else:
        print(f"    BAND [T-D, c_triv] is EMPTY: c_triv = {t1[str(lam)]['c_triv']:.4g} < T - D; the trivial bound closes everything above the ladder at this lam")
    out.setdefault("task2", {})[str(lam)] = {"cmax": cmax, "h": h, "K": K, "N": sw.N, "tail": sw.tail, "seconds": el,
                                              "sup": best["sup"], "sup_refined": sup_r, "inf": best["inf"], "minF": best["minF"],
                                              "minF_mid": best["minF_mid"], "minF_band_refined": minF_r, "minF_band": best["minF_band"],
                                              "minF_low": best["minF_low"], "sup_band": best["sup_band"], "checkpoints": {str(k): v for k, v in checkpoints.items()}}
    return sw


def task2(ps, t1, quick, out):
    print("\n" + "=" * 100)
    print("TASK 2: actual sup of prime/A and min of F/A on [0, min(c_triv, 1e7)] (dense sweep, refined; float)")
    print("=" * 100)
    sweepers = {}
    for lam in LAMS_SWEEP:
        ctriv = t1[str(lam)]["c_triv"]
        cmax = min(ctriv, 1e6 if quick else 1e7)
        h = 0.02 if cmax <= 1e5 else 0.1
        sweepers[lam] = sweep(ps, lam, cmax, h, quick, out, t1)
    return sweepers


# ----------------------------------------------------------------------------- Task 3
def zeros_window(t0, half):
    import flint

    def NT(T):
        return T / (2 * math.pi) * math.log(T / (2 * math.pi * math.e)) + 7.0 / 8.0

    path = os.path.join(SCRATCH, f"zw_{int(t0)}_{int(half)}.json")
    if os.path.exists(path):
        with open(path) as fh:
            return np.array(json.load(fh))
    n_lo = int(NT(t0 - half - 3)) - 3
    n_hi = int(NT(t0 + half + 3)) + 3
    zs = flint.acb.zeta_zeros(n_lo, n_hi - n_lo + 1)
    t = np.array([float(z.imag.mid()) for z in zs])
    assert t[0] < t0 - half and t[-1] > t0 + half, (t[0], t[-1], t0)
    assert max(abs(float(z.real.mid()) - 0.5) for z in zs) == 0.0
    with open(path, "w") as fh:
        json.dump(t.tolist(), fh)
    return t


def task3(ps, sweepers, out):
    print("\n" + "=" * 100)
    print("TASK 3: zero-side cross-check just above the ladder (c in [T-D, T+1000]) and at c ~ 1e6 (flint zeros, window +-25)")
    print("=" * 100)
    cs = [T_LADDER - D_LADDER, T_LADDER + 0.5, T_LADDER + 250.25, T_LADDER + 999.0, 1e6, 1e6 + 0.5, 1e6 + 123.4]
    print(f"{'c':>12} {'lam':>4} {'F_zero/A':>10} {'ztail/A':>8} {'arch/A':>8} {'prime/A':>9} {'F_arch/A':>10} {'diff':>9} {'rel':>8}")
    rec = {}
    for c in cs:
        t = zeros_window(c, 25.0)
        for lam in LAMS_SWEEP:
            w = t - c
            Fz = ((w * w) * np.exp(-2 * lam * w * w)).sum() / A_of(lam)
            X = 25.0
            dens = math.log(c / (2 * math.pi)) / (2 * math.pi) + 1.0
            zt = 2 * dens * (X * math.exp(-2 * lam * X * X) / (4 * lam)) / A_of(lam)
            aA = arch_over_A(c, lam)
            pA = float(sweepers[lam].direct([c])[0])
            Fa = aA - pA
            d = Fz - Fa
            rec[f"{c}_{lam}"] = {"F_zero_A": Fz, "arch_A": aA, "prime_A": pA, "diff": d, "n_zeros": int(len(t))}
            print(f"{c:12.2f} {lam:4g} {Fz:10.5f} {zt:8.1e} {aA:8.4f} {pA:9.5f} {Fa:10.5f} {d:9.1e} {abs(d)/Fz:8.1e}")
    out["task3"] = rec


# ----------------------------------------------------------------------------- Task 4
def y0_real_fixed(tl, t0, lam, quick):
    cs = np.arange(t0 - 1.0, t0 + 1.0 + 1e-9, 0.01 if quick else 0.005)
    X = tl[None, :] - cs[:, None]
    base = (X * X * np.exp(-2 * lam * X * X)).sum(axis=1)

    def minF(y):
        w = (t0 - cs) + 1j * y
        return float((base + 2.0 * (w * w * np.exp(-2 * lam * w * w)).real).min())

    lo, hi = 1e-6, 0.5
    if minF(hi) >= 0:
        return float("nan")
    for _ in range(24):
        mid = math.sqrt(lo * hi)
        if minF(mid) < 0:
            hi = mid
        else:
            lo = mid
    return hi


def task4(out, quick):
    print("\n" + "=" * 100)
    print("TASK 4: what fixed-width positivity would say about zeros: detection floor y0(lam, t)")
    print("=" * 100)
    print("model: lam*(y, x1) = log(x1^2/(2y^2))/(2(x1^2+y^2)), x1 = 2pi/log(t/2pi); y0 solves lam* = lam (nearest-neighbour, c = t0).")
    print("A zero at |beta - 1/2| < y0 leaves F(c, lam) >= 0 for every c at this lam: fixed-width positivity cannot see it.")
    ts = [1e3, 1e5, 1e6, 1e8, 1e12]
    print(f"{'lam':>5} | " + " ".join(f"{'t='+f'{t:.0e}':>10}" for t in ts) + "   [model y0; 'none' = x1 < y sqrt2 for y=1/2: undetectable at any y]")
    mod = {}
    for lam in LAMS_ALL:
        row = []
        for t in ts:
            x1 = 2 * math.pi / math.log(t / (2 * math.pi))
            y = solve_y0(x1, lam)
            row.append(y)
        mod[str(lam)] = dict(zip(map(str, ts), row))
        print(f"{lam:5g} | " + " ".join(f"{v:10.4f}" for v in row))
    out["y0_model"] = mod
    print("\nREAL neighbours (flint zeros at t0 near 6.4e5 and 1e6, replace-mode quadruple at t0, c scanned t0 +- 1, fixed lam):")
    print(f"{'t0':>12} {'x1_real':>8} | " + " ".join(f"{'lam='+str(l):>8}" for l in LAMS_ALL))
    real = {}
    for T0 in ([T_LADDER + 0.5, 1e6] if quick else [T_LADDER + 0.5, T_LADDER + 500.0, 1e6, 1e6 + 500.0]):
        t = zeros_window(T0, 25.0)
        i = int(np.argmin(np.abs(t - T0)))
        t0 = float(t[i])
        tl = np.delete(t, i)
        x1 = float(np.min(np.abs(tl - t0)))
        row = [y0_real_fixed(tl, t0, lam, quick) for lam in LAMS_ALL]
        real[str(t0)] = {"x1": x1, "y0": dict(zip(map(str, LAMS_ALL), row))}
        print(f"{t0:12.3f} {x1:8.3f} | " + " ".join(("    none" if v != v else f"{v:8.4f}") for v in row))
    out["y0_real"] = real


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    np.seterr(all="ignore")
    T = time.time()
    out = {"quick": args.quick}
    ps = PrimeSide(20_000_000)
    print(f"prime powers up to 2e7: {len(ps.n)}  (N(lam=2, 1e-6) needs log N = {N_cutoff(2.0, 1e-6):.1f}, i.e. {math.exp(N_cutoff(2.0, 1e-6)):.2e}: "
          f"{'covered' if math.exp(N_cutoff(2.0, 1e-6)) <= 2e7 else 'NOT covered; S_triv for lam = 2 uses the tail bound beyond 2e7'})")
    t1 = task1(ps, out)
    sweepers = task2(ps, t1, args.quick, out)
    task3(ps, sweepers, out)
    task4(out, args.quick)
    with open(os.path.join(SCRATCH, f"fixed_width{'_quick' if args.quick else ''}.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    print(f"\ntotal {time.time()-T:.1f}s")
    print("conjecture1_proved = False  (float numerics; nothing proved)")


if __name__ == "__main__":
    main()

"""Ordinates of the first K nontrivial zeros of zeta (positive imaginary parts).

Bracket sign changes of Hardy's Z with a vectorized Riemann-Siegel formula (first
correction term C0) on a fine grid, refine each bracket with mpmath.siegelz
(Illinois/Anderson root finder at 25 digits), and check indices against
mpmath.zetazero at spot indices (a missed or extra zero shifts every later index).
Search for structure only; not a certified zero list.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys, time
import numpy as np
import mpmath
from multiprocessing import Pool


def theta_np(t):
    t = np.asarray(t, float)
    return t / 2 * np.log(t / (2 * np.pi)) - t / 2 - np.pi / 8 + 1 / (48 * t) + 7 / (5760 * t ** 3)


def Z_rs(t):
    """Riemann-Siegel Z(t) with the C0 correction; float64; adequate for t > ~60 bracketing."""
    t = np.asarray(t, float)
    out = np.zeros_like(t)
    th = theta_np(t)
    tau = np.sqrt(t / (2 * np.pi))
    N = np.floor(tau).astype(int)
    p = tau - N
    for n in range(1, N.max() + 1):
        m = N >= n
        out[m] += 2 * np.cos(th[m] - t[m] * np.log(n)) / np.sqrt(n)
    C0 = np.cos(2 * np.pi * (p * p - p - 1 / 16)) / np.cos(2 * np.pi * p)
    out += (-1.0) ** (N - 1) * tau ** -0.5 * C0
    return out


def _refine(br):
    lo, hi = br
    mpmath.mp.dps = 25
    try:
        r = mpmath.findroot(mpmath.siegelz, (mpmath.mpf(lo), mpmath.mpf(hi)), solver="anderson", tol=1e-30)
        r = float(r)
        if not (lo - 1e-9 <= r <= hi + 1e-9):
            raise ValueError("escaped bracket")
        return r
    except Exception:
        # bisection fallback
        a, b = mpmath.mpf(lo), mpmath.mpf(hi)
        fa = mpmath.siegelz(a)
        for _ in range(60):
            c = (a + b) / 2
            fc = mpmath.siegelz(c)
            if fa * fc <= 0:
                b = c
            else:
                a, fa = c, fc
        return float((a + b) / 2)


def brackets(Tmax, h=0.004):
    br = []
    # low part with exact siegelz on a grid
    mpmath.mp.dps = 20
    tl = np.arange(10.0, 80.0, 0.02)
    zl = np.array([float(mpmath.siegelz(x)) for x in tl])
    s = np.nonzero(np.sign(zl[:-1]) != np.sign(zl[1:]))[0]
    br += [(tl[i], tl[i + 1]) for i in s]
    # high part RS
    t0 = 80.0
    while t0 < Tmax:
        t1 = min(t0 + 500.0, Tmax)
        tt = np.arange(t0, t1 + h / 2, h)
        zz = Z_rs(tt)
        s = np.nonzero(np.sign(zz[:-1]) != np.sign(zz[1:]))[0]
        br += [(tt[i], tt[i + 1]) for i in s]
        t0 = tt[-1]
    return br


def main(K=10000, out=None, procs=8):
    t = time.time()
    # height of K-th zero ~ via N(T) ~ T/2pi log(T/2pi e) + 7/8 ; overshoot
    T = 20.0
    while T / (2 * np.pi) * np.log(T / (2 * np.pi * np.e)) + 7 / 8 < K + 20:
        T *= 1.05
    br = brackets(T)
    print(f"brackets {len(br)} up to T={T:.1f} in {time.time()-t:.1f}s", flush=True)
    with Pool(procs) as P:
        zs = P.map(_refine, br, chunksize=50)
    zs = np.array(sorted(zs))
    print(f"refined in {time.time()-t:.1f}s", flush=True)
    # SECOND PASS (added after a defect was found): the C0-only RS grid occasionally places the
    # sign change one cell off; siegelz then has equal signs at both bracket ends and the bisection
    # fallback drifts to an endpoint (14 of the first 300 zeros were off by up to 4.3e-3).
    # Re-refine every zero from a local siegelz sign-change search (rerefine_zeros.ref).
    from rerefine_zeros import ref
    with Pool(procs) as P:
        out = P.map(ref, list(zs), chunksize=100)
    zs = np.array([o[0] for o in out])
    assert np.all(np.diff(zs) > 0) and max(o[1] for o in out) < 1e-12
    # value check of the first 300 against mpmath.zetazero
    mpmath.mp.dps = 20
    z300 = np.array([float(mpmath.zetazero(k).imag) for k in range(1, 301)])
    print(f"max |mine - zetazero| over first 300: {np.max(np.abs(zs[:300]-z300)):.2e}", flush=True)
    # spot index check
    mpmath.mp.dps = 20
    checks = []
    for k in [1, 2, 10, 100, 500, 1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000, 9000, 10000]:
        if k <= len(zs):
            zk = float(mpmath.zetazero(k).imag)
            checks.append((k, zs[k - 1], zk, zs[k - 1] - zk))
            print(f"  k={k:6d} mine={zs[k-1]:.12f} zetazero={zk:.12f} diff={zs[k-1]-zk:.2e}", flush=True)
    zs = zs[:K]
    if out:
        np.save(out, zs)
    return zs, checks


if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    out = sys.argv[2] if len(sys.argv) > 2 else "zeros.npy"
    main(K, out)

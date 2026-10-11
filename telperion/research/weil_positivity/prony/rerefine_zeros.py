"""Re-refine every zero of zeros_1e4.npy with a secant iteration on mpmath.siegelz seeded at the
current estimate (fixes brackets mislocated by the C0-only Riemann-Siegel grid), then verify."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys, numpy as np, mpmath
from multiprocessing import Pool

def ref(x):
    mpmath.mp.dps = 25
    x = mpmath.mpf(x)
    # local sign-change search first (radius 0.02), then secant/bisection inside the found bracket
    h = mpmath.mpf("0.0005")
    best = None
    for k in range(0, 41):
        for s in ((1, -1) if k else (1,)):
            lo = x + s * k * h - h / 2; hi = lo + h
            if mpmath.siegelz(lo) * mpmath.siegelz(hi) <= 0:
                best = (lo, hi); break
        if best: break
    if best is None:
        return float("nan"), float("nan")
    r = mpmath.findroot(mpmath.siegelz, best, solver="illinois", tol=1e-40, maxsteps=200, verify=False)
    return float(r), float(abs(mpmath.siegelz(r)))

if __name__ == "__main__":
    z = np.load(sys.argv[1])
    with Pool(8) as P:
        out = P.map(ref, list(z), chunksize=100)
    r = np.array([o[0] for o in out]); res = np.array([o[1] for o in out])
    mv = np.abs(r - z)
    print("nan:", int(np.isnan(r).sum()), " max |Z(root)|:", np.nanmax(res), " max move:", np.nanmax(mv), " n moved > 1e-9:", int((mv > 1e-9).sum()))
    print("strictly increasing:", bool(np.all(np.diff(r) > 0)), " unique:", len(np.unique(np.round(r, 9))) == len(r))
    np.save(sys.argv[2], r)

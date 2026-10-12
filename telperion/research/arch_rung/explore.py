"""Parameter exploration for cert_exact.py: margin (float estimate from the exact Zs) vs Lean cost
(number of psiR floors, matrix size M).  2026-10-11.  Numerical, not kernel-checked.
conjecture1_proved = False.

usage: python explore.py [L-numerator L-denominator]
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import sys
from flint import fmpq
import cert_exact as CE


def grid_geom(R, h0, ratio, hmax):
    """0, h0, ... with widths growing geometrically by `ratio`, capped at hmax, last point R.
    Widths are rounded to multiples of 1/20 so the grid is short rationals."""
    g = [fmpq(0)]
    h = h0
    while g[-1] < R:
        hq = fmpq(max(1, round(h * 20)), 20)
        g.append(min(g[-1] + hq, fmpq(R)))
        h = min(h * ratio, hmax)
    return g


def margin_est(cfg):
    B = CE.build(cfg)
    kf = CE.float_kappa(B)
    eta = float(cfg["eta"])
    m = float(B["sJ"]) - kf - (1 + 1 / eta) * float(B["EPS"])
    return m, kf, float(B["sJ"]), float(B["EPS"]), len(B["grid"])


if __name__ == "__main__":
    if len(sys.argv) > 2:
        L = fmpq(int(sys.argv[1]), int(sys.argv[2]))
    else:
        L = fmpq(1733, 5000)
    base = dict(L=L, eta=fmpq(1, 10000), rho=fmpq(10 ** 6), buf=fmpq(1, 1000),
                logpi=fmpq(1159, 1000), nser=40, mtail=10 ** 6)
    print("L =", L, "(log pi <= 1.159, gamma <= 0.58112, floors psiR_ge_rational N=40)")
    for R in [16, 20, 24, 30, 40]:
        for (h0, ratio, hmax) in [(0.25, 1.0, 0.25), (0.5, 1.0, 0.5), (0.25, 1.15, 2.0), (0.5, 1.2, 4.0)]:
            grid = grid_geom(R, h0, ratio, hmax)
            for M in [24, 32, 40, 48]:
                cfg = dict(base, grid=grid, M=M)
                try:
                    m, kf, sJ, eps, npts = margin_est(cfg)
                except AssertionError as e:
                    print("   assert", e); continue
                print(f"R={R:3d} grid(h0={h0},x{ratio},cap {hmax}) floors={npts:4d} M={M:3d}  "
                      f"sJ={sJ:.4f} kappa={kf:.4f} EPS={eps:.1e}  margin~{m:+.5f}", flush=True)

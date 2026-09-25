"""E threshold: lam_min(E, x) on Neumann spans N = 64, 128, 256 (both sectors), bisection in x."""
import numpy as np, mpmath as mp
from bcore import *
def lamE(x, N):
    A = mp.log(x)/2; fm = Form(A, 'E')
    out = []
    for par in (0, 1):
        Mr, Gr = real_sector(fm, sector_basis(A, N, par, 'neumann'), par)
        out.append(gmin(Mr, Gr)[0])
    return min(out)
for N in (64, 128, 256):
    lo, hi = 19.5, 20.0
    for _ in range(14):
        mid = (lo+hi)/2
        if lamE(mid, N) > 0: lo = mid
        else: hi = mid
    print('N=%d: E threshold in [%.5f, %.5f]' % (N, lo, hi), flush=True)
for x in (19.8, 19.85, 19.9):
    print('x=%.2f lam_E: N=64 %+.3e N=128 %+.3e N=256 %+.3e' % (x, lamE(x, 64), lamE(x, 128), lamE(x, 256)), flush=True)

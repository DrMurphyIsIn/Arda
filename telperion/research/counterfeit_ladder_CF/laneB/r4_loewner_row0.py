"""Check the partial-fraction (Loewner) identity in its row-0 form:
   L = Q - pole (translation-invariant part).  For i != n:
   L_in = (-1)^(i+n) (G(k_n) - G(k_i))/(k_n^2 - k_i^2),  G(k_n) - G(k_0) = (-1)^n (k_n^2 - k_0^2) L_0n.
   So every off-diagonal entry is determined by row 0 alone."""
import numpy as np, mpmath as mp
from bcore import *
for x in (20, 24):
    A = mp.log(x)/2
    for kind in ('ZK', 'E'):
        f = Form(A, kind)
        for par in (0, 1):
            kap = np.array(sector_basis(A, 96, par))
            M, G, P = real_sector(f, list(kap), par, parts=True)
            L = M - P['pole']
            Gk = (-1.0)**np.arange(len(kap)) * (kap**2 - kap[0]**2) * L[0]   # G(k_n)-G(k_0)
            err = 0; scale = 0
            for i in range(1, len(kap)):
                for n in range(1, len(kap)):
                    if i == n: continue
                    pred = (-1)**(i+n) * (Gk[n] - Gk[i]) / (kap[n]**2 - kap[i]**2)
                    err = max(err, abs(pred - L[i, n])); scale = max(scale, abs(L[i, n]))
            print('x=%d %s par%d N=96: max|row0-Loewner - matrix| = %.2e (max |entry| %.2e)' % (x, kind, par, err, scale), flush=True)

import time, numpy as np, mpmath as mp
import icore, bcore
from fractions import Fraction as Fr
for rig in (False, True):
    X = icore.Ctx(rig, 30)
    t = time.time()
    F = icore.Form(X, 24, 'ZK')
    for par in (0, 1):
        M, G, kap = icore.build_sector(F, par, 8)
        fl = lambda v: float(mp.mpf(v.mid) if rig else v)
        Mf = np.array([[fl(v) for v in r] for r in M]); Gf = np.array([[fl(v) for v in r] for r in G])
        fb = bcore.Form(mp.log(24)/2, 'ZK')
        Mb, Gb = bcore.real_sector(fb, bcore.sector_basis(mp.log(24)/2, 8, par, 'neumann'), par)
        w = max(float(mp.mpf(v.delta)) for r in M for v in r) if rig else 0
        print('rig', rig, 'par', par, 'max|M-Mfloat|=%.2e max|G-G|=%.2e  max width=%.2e  %.1fs' % (np.max(abs(Mf-Mb)), np.max(abs(Gf-Gb)), w, time.time()-t))

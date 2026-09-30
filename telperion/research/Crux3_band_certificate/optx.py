"""Smallest window with a band-local (complex, <= 4 modes, free frequencies) negative direction for D."""
import mpmath as mp, numpy as np, sys
from weilfreq import FWindow, gen_eig
mp.mp.dps = 20
for A in [float(v) for v in sys.argv[1].split(',')]:
    Wd = FWindow(A, 'dh'); Wz = FWindow(A, 'zeta')
    best = (1e9,)
    for d in (2, 3, 4):
        for r0 in np.arange(83.0, 88.01, 0.25):
            for dl in (0.8, 1.2, 1.6, 2.0, 2.5):
                ks = [mp.mpf(r0 + dl * (i - (d - 1) / 2)) for i in range(d)]
                Md, G, _, _, _ = Wd.matrices(ks)
                ev, _ = gen_eig(Md, G)
                if ev[0] < best[0]:
                    Mz, _, _, _, _ = Wz.matrices(ks)
                    ez, _ = gen_eig(Mz, G)
                    best = (ev[0], d, r0, dl, ez[0])
    print('A=%.3f x=%.2f: min over bands of D band-eig = %.4f (d=%d r0=%.2f dl=%.2f; zeta there %.4f)' % (A, np.exp(2*A), best[0], best[1], best[2], best[3], best[4]), flush=True)

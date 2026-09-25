import mpmath as mp, numpy as np, sys
from weilfreq import FWindow, gen_eig
mp.mp.dps = 20
for A in [float(v) for v in sys.argv[1].split(',')]:
    Wd = FWindow(A, 'dh'); Wz = FWindow(A, 'zeta')
    for d in (4, 6, 8, 12, 16):
        best = (1e9,)
        for r0 in np.arange(84.0, 88.01, 0.5):
            for dl in (1.2, 1.5, 1.7):
                ks = [mp.mpf(r0 + dl * (i - (d - 1) / 2)) for i in range(d)]
                Md, G, _, _, _ = Wd.matrices(ks)
                ev, _ = gen_eig(Md, G)
                if ev[0] < best[0]:
                    Mz, _, _, _, _ = Wz.matrices(ks)
                    ez, _ = gen_eig(Mz, G)
                    best = (ev[0], d, r0, dl, ez[0])
        print('A=%.3f x=%.2f d=%2d: min D band-eig = %.4e (r0=%.2f dl=%.2f; zeta there %.4e)' % (A, np.exp(2*A), d, best[0], best[2], best[3], best[4]), flush=True)

"""Band-local detection horizon for each Davenport-Heilbronn off-line zero: the smallest window
x = e^{2A} at which some <= 6-mode complex band near gamma0 makes D's Weil form indefinite."""
import mpmath as mp, numpy as np, sys
from weilfreq import FWindow, gen_eig
mp.mp.dps = 20
zeros = [(85.699348, 0.308517), (114.163343, 0.150830), (166.479306, 0.074356), (176.702461, 0.224258)]
def best_band(A, g0, kind='dh'):
    W = FWindow(A, kind)
    best = (1e9,)
    for d in (2, 3, 4, 6):
        for off in np.arange(-1.5, 1.51, 0.5):
            for dl in (1.0, 1.3, 1.6, 2.0):
                ks = [mp.mpf(g0 + off + dl * (i - (d - 1) / 2)) for i in range(d)]
                M, G, _, _, _ = W.matrices(ks)
                try:
                    ev, _ = gen_eig(M, G)
                except Exception:
                    continue
                if ev[0] < best[0]:
                    best = (ev[0], d, off, dl, ks)
    return best
for (g0, b) in zeros:
    lo, hi = 1.5, 3.2
    # coarse scan then bisection on A
    As = np.arange(lo, hi, 0.05)
    first = None
    for A in As:
        bb = best_band(A, g0)
        if bb[0] < 0:
            first = A
            break
    if first is None:
        print('gamma0=%.3f beta=%.4f: no band-local detection up to A=%.2f (x=%.0f)' % (g0, b, hi, np.exp(2 * hi)), flush=True)
        continue
    a, c = first - 0.05, first
    for _ in range(5):
        m = (a + c) / 2
        if best_band(m, g0)[0] < 0:
            c = m
        else:
            a = m
    bb = best_band(c, g0)
    Wz = FWindow(c, 'zeta')
    Mz, G, _, _, _ = Wz.matrices(bb[4])
    ez, _ = gen_eig(Mz, G)
    print('gamma0=%.3f beta=%.4f: band-local horizon A=%.3f x=%.1f (d=%d, D min %.3e; zeta there %.3e)' % (g0, b, c, np.exp(2 * c), bb[1], bb[0], ez[0]), flush=True)

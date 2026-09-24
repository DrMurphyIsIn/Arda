import sys, time
sys.path.insert(0, '/Users/peterwmurphy/arda-crux2/telperion/research/crux_spectral-operator')
import mpmath as mp
import wpw
import flint
from flint import arb
flint.ctx.prec = 200
import galerkin_cos as gc
mp.mp.dps = 45
for (x, N, kind, sector) in [(9, 12, 'zeta', 'even'), (9, 12, 'zeta', 'odd'), (40, 12, 'dh', 'even'), (40, 12, 'dh', 'odd'), (20, 10, 'zeta', 'odd')]:
    t = time.time()
    Qw, Lw = wpw.build(x, N, kind, sector)
    Qg, Lg = gc.build(arb(x), N, kind, sector)
    n = Qg.nrows()
    d = max(abs(float(Qg[i,k].mid()) - float(Qw[i,k])) for i in range(n) for k in range(n))
    # high precision diff
    dd = mp.mpf(0)
    for i in range(n):
        for k in range(n):
            dd = max(dd, abs(mp.mpf(Qg[i,k].mid().str(50, radius=False)) - Qw[i,k]))
    rad = max(float(Qg[i,k].rad()) for i in range(n) for k in range(n))
    print("x=%d N=%d %s %s: max|rigorous - wpw| = %s   max radius %.2e  (%.1fs)" % (x, N, kind, sector, mp.nstr(dd, 5), rad, time.time()-t))

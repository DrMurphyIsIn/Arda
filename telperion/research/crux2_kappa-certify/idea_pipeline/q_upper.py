"""Rayleigh-Ritz UPPER bounds for lam_min(Q_x) per sector from the rigorous cos/sin Galerkin matrices."""
import flint, sys, time
from flint import arb
flint.ctx.prec = 320
flint.ctx.threads = 2
import galerkin_cos as gc
from rmat import min_eig_inverse_iter
import vldlt
x = arb(float(sys.argv[1])) if '/' not in sys.argv[1] else None
if x is None:
    p, q = sys.argv[1].split('/'); a = arb(int(p))/int(q); x = (2*a).exp()
kind = sys.argv[3] if len(sys.argv) > 3 else 'zeta'
for N in [int(v) for v in sys.argv[2].split(',')]:
    for sector in ('even', 'odd'):
        t = time.time()
        Q, L = gc.build(x, N, kind, sector)
        # smallest eigenvalue (can be negative): bisection with floating LDL^T
        def pd(l):
            Lf, D, j, s = vldlt.floating_ldlt(Q, l, b=64)
            return Lf is not None
        # find bracket
        hi = 1.0
        while pd(hi): hi *= 10
        lo = hi / 10
        if not pd(lo):
            # go down
            lo = hi
            k = 0
            while not pd(lo) and k < 400:
                lo = lo / 10 if lo > 1e-300 else -1e-300
                k += 1
                if lo < 1e-200 and lo > 0: lo = -1e-40
            if lo < 0:
                # negative: search negative side
                l = -1e-40
                while not pd(l): l *= 10
                lo, hi = l, l/10
        for _ in range(40):
            m = (lo + hi) / 2
            if pd(m): lo = m
            else: hi = m
        print("%s x=%s N=%d %s: lam_min(Galerkin Q) in [%.4e, %.4e]  (%.1fs)" % (kind, x.mid().str(8, radius=False), N, sector, lo, hi, time.time()-t), flush=True)

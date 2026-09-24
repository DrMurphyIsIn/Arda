import flint, sys, time
from flint import arb
flint.ctx.prec = 256
flint.ctx.threads = 2
import galerkin_cos as gc
import vldlt
def lam_min(Q):
    def pd(l):
        Lf, D, j, s = vldlt.floating_ldlt(Q, l, b=64)
        return Lf is not None
    # bracket in signed log scale
    grid = [10.0**e for e in range(0, -300, -1)]
    if pd(0.0):
        hi = next((g for g in grid if not pd(g)), None)
        if hi is None: return 0.0
        lo = hi/10
        while not pd(lo): lo /= 10
        for _ in range(30):
            m = (lo*hi)**0.5
            if pd(m): lo = m
            else: hi = m
        return lo
    else:
        lo = -1e-300
        while not pd(lo): lo *= 10
        hi = lo/10
        for _ in range(30):
            m = -((lo*hi)**0.5)
            if pd(m): lo = m
            else: hi = m
        return lo
for x in [float(v) for v in sys.argv[1].split(',')]:
    for N in [int(v) for v in sys.argv[2].split(',')]:
        row = []
        for kind in ('zeta', 'dh'):
            for sector in ('even', 'odd'):
                Q, L = gc.build(arb(x), N, kind, sector)
                row.append("%s-%s %.3e" % (kind, sector, lam_min(Q)))
        print("x=%g N=%d: %s" % (x, N, " | ".join(row)), flush=True)

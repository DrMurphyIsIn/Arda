"""Certified UPPER bound on lam*(Q) per sector: explicit rational vector c, Arb-exact Galerkin matrix of the
untruncated Q (galerkin_cos, closed forms), certified Rayleigh quotient c^T Q c / c^T c (Rayleigh-Ritz)."""
import flint, sys, json, time
from flint import arb, fmpq
import mpmath as mp
import galerkin_cos as gc
from sep_cert import neg_vector   # returns bottom eigen-estimate and a rational eigenvector approximation
def run(a_str, N, prec=512, digits=60):
    flint.ctx.prec = prec
    p, q = a_str.split('/') if '/' in a_str else (None, None)
    a = arb(int(p)) / int(q) if p else arb(float(a_str))
    x = (2 * a).exp()
    out = {}
    for sector in ('even', 'odd'):
        t = time.time()
        Q, L = gc.build(x, N, 'zeta', sector)
        ev, c = neg_vector(Q, digits=digits)
        cb = [arb(ci) for ci in c]
        num, den = gc.rayleigh(Q, cb)
        rq = num / den
        out[sector] = dict(eig_estimate=mp.nstr(ev, 8), certified_upper=rq.str(8))
        print("a=%s N=%d %s: bottom eig est %s ; certified Rayleigh quotient (upper bound on lam*) %s  (%.1fs)" % (
            a_str, N, sector, mp.nstr(ev, 6), rq.str(6), time.time() - t), flush=True)
    return out
if __name__ == '__main__':
    r = run(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 512)
    json.dump(r, open('upper_%s_N%s.json' % (sys.argv[1].replace('/', '_'), sys.argv[2]), 'w'), indent=1)

"""Certified zeta-vs-D separation on one explicit finite test space (cos/sin modes on [-L/2,L/2]).
D: certified NEGATIVE Rayleigh quotient c^T Q_D c < 0 for an explicit rational c (=> kappa_D(x) >= 1 per sector).
zeta: verified LDL^T => the Galerkin matrix of Q_zeta on the same space is positive definite (kappa_N = 0)."""
import flint, sys, time, json
from flint import arb, arb_mat, fmpq
import mpmath as mp
import galerkin_cos as gc
import vldlt

def lam_min_pd(Q):
    def pd(l):
        Lf, D, j, s = vldlt.floating_ldlt(Q, l, b=64)
        return Lf is not None
    if not pd(0.0):
        return None
    hi = 1.0
    while pd(hi): hi *= 2
    lo = hi / 2
    while not pd(lo): lo /= 2
    for _ in range(40):
        m = (lo + hi) / 2
        if pd(m): lo = m
        else: hi = m
    return lo

def neg_vector(Q, digits=40):
    n = Q.nrows()
    mp.mp.dps = digits + 20
    A = mp.matrix(n, n)
    for i in range(n):
        for k in range(n):
            A[i, k] = mp.mpf(Q[i, k].mid().str(digits + 15, radius=False))
    E, V = mp.eigsy(A)
    idx = min(range(n), key=lambda i: E[i])
    v = [V[i, idx] for i in range(n)]
    s = max(abs(t) for t in v)
    # exact rationals with 'digits' significant digits
    c = [fmpq(int(mp.nint(t / s * mp.mpf(10) ** digits)), 10 ** digits) for t in v]
    return E[idx], c

def run(x_str, N, prec_zeta=1024, prec_dh=256):
    x = arb(float(x_str)) if '/' not in x_str else arb(int(x_str.split('/')[0])) / int(x_str.split('/')[1])
    rep = dict(x=x_str, N=N, dh={}, zeta={})
    for sector in ('even', 'odd'):
        flint.ctx.prec = prec_dh
        t = time.time()
        QD, L = gc.build(x, N, 'dh', sector)
        ev, c = neg_vector(QD)
        cb = [arb(ci) for ci in c]
        num, den = gc.rayleigh(QD, cb)
        rq = num / den
        rep['dh'][sector] = dict(eig_estimate=mp.nstr(ev, 8), certified_rayleigh_quotient=rq.str(10),
                                 negative=bool(rq < 0), dim=QD.nrows(), seconds=round(time.time() - t, 1))
        print("D   x=%s N=%d %s: eig est %s  certified c^TQc/c^Tc = %s  negative=%s" % (
            x_str, N, sector, mp.nstr(ev, 6), rq.str(8), rq < 0), flush=True)
        flint.ctx.prec = prec_zeta
        t = time.time()
        QZ, L = gc.build(x, N, 'zeta', sector)
        lm = lam_min_pd(QZ)
        if lm is None:
            rep['zeta'][sector] = dict(pd=False)
            print("zeta x=%s N=%d %s: NOT PD at working precision" % (x_str, N, sector), flush=True)
            continue
        lam0 = lm * 0.9
        vr = vldlt.verify(QZ, lam0, b=64)
        rep['zeta'][sector] = dict(lam_min_estimate='%.6e' % lm, lam0='%.4e' % lam0, verified=vr['ok'],
                                   resid_fro=vr['Efro'].str(5) if vr['ok'] else None,
                                   certified_lower=vr['lower'].str(8) if vr['ok'] else None,
                                   max_entry_rad='%.2e' % max(float(QZ[i, k].rad()) for i in range(QZ.nrows()) for k in range(QZ.nrows())),
                                   seconds=round(time.time() - t, 1))
        print("zeta x=%s N=%d %s: lam_min(Galerkin) ~ %.4e ; verified LDL^T at %.3e ok=%s resid %s" % (
            x_str, N, sector, lm, lam0, vr['ok'], vr['Efro'].str(3) if vr['ok'] else '-'), flush=True)
    json.dump(rep, open('sep_x%s_N%d.json' % (x_str.replace('/', '_'), N), 'w'), indent=1)
    return rep

if __name__ == '__main__':
    run(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1024)

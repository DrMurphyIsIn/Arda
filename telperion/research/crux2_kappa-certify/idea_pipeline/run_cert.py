"""Driver: build leading blocks, estimate lam_min, certify at lam0 = frac * estimate, save everything."""
import flint, time, json, sys
from flint import arb, arb_mat
from certify import Window, build_leading, interval_ldlt_pos
import vldlt
from rmat import min_eig_inverse_iter

def parse_a(s):
    if '/' in s:
        p, q = s.split('/')
        return arb(int(p)) / int(q)
    return arb(float(s))

def run(a_str, T, N, prec=256, frac=0.98, tag=None, sectors=('even','odd'), kind='zeta'):
    flint.ctx.prec = prec
    a = parse_a(a_str)
    assert a.rad() == 0
    win = Window(a, T, kind=kind)
    print("[%s] a=%s" % (kind, a_str) + " a=%s (%.8f) T#=%s N=%d prec=%d primes=%s A_L=%s b*=%s" % (a_str, float(a), T, N, prec,
          [n for (n,p) in win.plist], win.AL.str(12), win.bstar.str(12)), flush=True)
    assert win.bstar > 0
    rep = dict(a=a_str, a_float=float(a), Tsharp=T, N=N, prec=prec, primes=[n for (n,p) in win.plist],
               A_L=win.AL.str(25), bstar=win.bstar.str(25), sectors={})
    noderad = arb(0)
    for (t, w, _, r) in win.nodes():
        noderad = noderad.max(arb(r) + (win.a_ * t).rad() / win.a_ + (arb((win.a_ * t).mid()) / win.a_).rad())
    for sector in sectors:
        t0 = time.time()
        M, cmax2 = build_leading(win, sector, N)
        lam_est, vec = min_eig_inverse_iter(M, iters=6)
        lam_est_f = float(lam_est.mid())
        lam0 = arb(float('%.3e' % (frac * lam_est_f)))
        qerr, pert, _ = win.quad_error_bound(cmax2)
        eta = (qerr + pert * noderad) * N
        tb = win.tail_bounds(sector, N)
        vr = vldlt.verify(M, float(lam0.mid()), b=64)
        ok = vr['ok']
        tries = 0
        while not ok and tries < 40:
            # the estimate was not the bottom eigenvalue (or too close): back off geometrically
            lam0 = arb(float('%.3e' % (float(lam0.mid()) * 0.7)))
            vr = vldlt.verify(M, float(lam0.mid()), b=64)
            ok = vr['ok']
            tries += 1
        if ok and tries > 0:
            # refine upward by bisection between the last success and the last failure
            lo_ok = float(lam0.mid()); hi_bad = lo_ok / 0.7
            for _ in range(12):
                mid_ = (lo_ok + hi_bad) / 2
                if vldlt.verify(M, mid_, b=64)['ok']:
                    lo_ok = mid_
                else:
                    hi_bad = mid_
            lam0 = arb(float('%.4e' % (lo_ok * 0.995)))
            vr = vldlt.verify(M, float(lam0.mid()), b=64)
            ok = vr['ok']
        lam_lead = vr['lower'] if ok else arb(0)
        final = (lam_lead - eta).min(win.bstar - tb['epsD']) - tb['epsB']
        s = dict(lam_est=lam_est.mid().str(10, radius=False), lam0=lam0.str(10), ldlt_ok=ok,
                 resid_fro=(vr['Efro'].str(5) if ok else vr.get('reason')), dmin=(vr['dmin'].str(5) if ok else None),
                 quad_err_entry=qerr.str(5), node_pert=(pert*noderad).str(5),
                 eta=eta.str(5), epsB=tb['epsB'].str(5), epsD=tb['epsD'].str(5), Pm=tb['Pm'].str(8),
                 first_tail_order=tb['first_tail'], final_lower=final.str(15) if ok else None,
                 final_positive=bool(ok and final > 0), seconds=round(time.time() - t0, 1))
        rep['sectors'][sector] = s
        print("  %s: lam_est=%s  vLDL^T(M - %s I) ok=%s resid=%s eta=%s epsB=%s epsD=%s  => lam_min(Q_%s) >= %s  (%.0fs)" % (
            sector, lam_est.mid().str(6, radius=False), lam0.str(4), ok, s['resid_fro'], eta.str(3), tb['epsB'].str(3),
            tb['epsD'].str(3), sector, final.str(8) if ok else 'FAIL', time.time() - t0), flush=True)
        # save matrix midpoints/radii (for downstream Lean extraction of leading sub-blocks)
        if tag:
            K = min(N, 48)
            with open('M_%s_%s_lead%d.txt' % (tag, sector, K), 'w') as fh:
                for i in range(K):
                    fh.write(' '.join('%s|%s' % (M[i,k].mid().str(80, radius=False), M[i,k].rad().str(3, radius=False)) for k in range(K)) + '\n')
    if tag:
        json.dump(rep, open('cert_%s.json' % tag, 'w'), indent=1)
    return rep

if __name__ == '__main__':
    a_str = sys.argv[1]; T = float(sys.argv[2]); N = int(sys.argv[3])
    prec = int(sys.argv[4]) if len(sys.argv) > 4 else 256
    tag = sys.argv[5] if len(sys.argv) > 5 else None
    run(a_str, T, N, prec, tag=tag)

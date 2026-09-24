"""Re-bound the quadrature error of an already-computed window-aware block with per-panel optimised Bernstein
ellipses (same nodes).  Far panels / panels away from t = 0: any b with c - A > 0 (A = sqrt(h^2 + b^2)) keeps
Re z > 0 on the ellipse, so psi(1/4 +- i z/2) has no poles there (poles at z = +-i(2k+1/2)); the first panels
near t = 0 keep b < 1/2.  The integrand is entire otherwise (j_n, cos, erf), with |j_n(az)| <= e^{a|Im z|}."""
import math, sys
import flint
from flint import arb, acb
from certify import ellipse_params, psi_sup_on_ellipse
import certify_wa
from certify_wa import WindowWA

def quad_bound_opt(win, cmax2, bmax=24.0, verbose=False):
    total = arb(0)
    pert = arb(0)
    worst = []
    for (lo, hi, kind) in win.eds:
        n = win.near[2] if kind == 'near' else win.far[1]
        hf = (hi - lo) / 2
        c = (lo + hi) / 2
        # candidate b values: pole-free ellipses
        cands = []
        if c - hf > 0.05:
            bm = min(bmax, math.sqrt(max(c * c - hf * hf, 0)) * 0.98)
            cands += [bm * s for s in (1.0, 0.7, 0.5, 0.35, 0.25, 0.15)]
        cands += [0.45, 0.4, 0.3]
        best = None
        for b in cands:
            if b <= 0:
                continue
            A2 = hf * hf + b * b
            if not (c - math.sqrt(A2) > 0.0) and b >= 0.5:
                continue
            try:
                rho, semimajor = ellipse_params(hf, b)
                psup = psi_sup_on_ellipse(c, hf, b, None, z0=win.z0)
            except Exception:
                continue
            comb = arb(0)
            for (cc_, ln, _) in win.coefs:
                comb += abs(cc_) * (arb(b) * ln).cosh()
            y = arb(b) / win.w
            K = 1 + 2 / arb.pi().sqrt() * y * (y * y).exp()
            chisup = K * (2 + K)
            Mpsi = (psup + abs(win.c0) + comb + abs(win.bp)) * chisup
            Mf = Mpsi * cmax2 * (2 * win.a_ * arb(b)).exp() / arb.pi()
            h = arb(hf)
            err = h * arb(64) / 15 * Mf * rho ** (-2 * n) / (rho * rho - 1)
            dist = arb(b).min(semimajor - h)
            pp = 2 * h * Mf / dist
            if best is None or float(err.upper()) < float(best[0].upper()):
                best = (err, pp, b)
        total += best[0]
        pert += best[1]
        worst.append((float(best[0].upper()), lo, hi, best[2]))
    worst.sort(reverse=True)
    if verbose:
        print("  worst panels:", [(("%.2e" % e), l, h_, round(b, 3)) for (e, l, h_, b) in worst[:4]])
    return total, pert

if __name__ == '__main__':
    flint.ctx.prec = 256
    a = arb(307) / 256
    for (Tc, N, sector) in [(1170.0, 2300, 'even'), (2000.0, 2300, 'odd')]:
        win = WindowWA(a, 0.34, Tc, 66.0, gap_k=8.0, gap_max=11.5)
        modes = [2 * k for k in range(N)] if sector == 'even' else [2 * k + 1 for k in range(N)]
        cmax2 = 2 * a * (2 * modes[-1] + 1)
        tot, pert = quad_bound_opt(win, cmax2, verbose=True)
        noderad = arb('1e-70')
        eta = (tot + pert * noderad) * N
        print("%s Tc=%g: per-entry quad bound %s ; pert %s ; eta = N*(...) = %s" % (sector, Tc, tot.str(3), (pert * noderad).str(3), eta.str(3)))

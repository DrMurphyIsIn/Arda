"""Refined rigorous quadrature bound (same nodes) for a window-aware block:
 |E_kl| <= sum_p Q_p G_{p,k} G_{p,l},   ||E||_2 <= ||E||_F <= sum_p Q_p sum_k G_{p,k}^2,
 Q_p = (64/15) h Mpsi_p rho^{-2n}/((rho^2-1) pi),  G_{p,k} = c_k sup_{z in ellipse_p}|j_{n_k}(a z)|,
 |j_n(zeta)| <= min( e^{|Im zeta|}, |zeta|^n e^{|zeta|^2/(2(2n+3))}/(2n+1)!! )   (power series bound).
 Ellipse per panel: pole-free choice as in quad_opt (b < 1/2 only for the panel(s) touching t = 0).
 Node perturbation: Cauchy bound on a small ellipse (b = 0.4 near / 1 far), crude c_max^2."""
import math, sys
import flint
from flint import arb
from certify import ellipse_params, psi_sup_on_ellipse
from certify_wa import WindowWA

def dfact(n):
    return arb(2 * n + 2).gamma() / (arb(2) ** (n + 1) * arb(n + 1).gamma())

_DF = {}
def _dfacts(modes):
    key = (modes[0], modes[-1], len(modes))
    if key in _DF:
        return _DF[key]
    out = []
    d = dfact(modes[0])
    prev = modes[0]
    for n in modes:
        while prev < n:
            prev += 1
            d = d * (2 * prev + 1)
        out.append(d)
    _DF[key] = out
    return out

def Gsum(a, modes, b, Rmax):
    """sum_k G_k^2, G_k = c_k * min(e^{a b}, (a R)^n e^{(aR)^2/(2(2n+3))}/(2n+1)!!); modes ascending.
    Once the power-series bound is below 2^-2000 relative and decreasing geometrically (ratio <= 1/4), the
    remaining terms are bounded by a geometric tail."""
    s = arb(0)
    aR = a * Rmax
    eab = (a * b).exp()
    dfs = _dfacts(modes)
    small = arb(2) ** (-2000)
    for idx, n in enumerate(modes):
        c2 = 2 * a * (2 * n + 1)
        ps = aR ** n * ((aR * aR) / (2 * (2 * n + 3))).exp() / dfs[idx]
        g = eab.min(ps)
        term = c2 * g * g
        s += term
        if ps < eab * small and (aR * aR) / ((2 * n + 3) * (2 * n + 5)) < arb(1) / 8:
            # geometric tail: consecutive (step 2) terms shrink by <= (aR)^4/((2n+3)(2n+5))^2 * (c ratio) < 1/32
            s += term * 2
            break
    return s

def bound(win, N, sector, bmax=24.0):
    a = win.a_
    modes = [2 * k for k in range(N)] if sector == 'even' else [2 * k + 1 for k in range(N)]
    total = arb(0)
    rows = []
    for (lo, hi, kind) in win.eds:
        n = win.near[2] if kind == 'near' else win.far[1]
        hf = (hi - lo) / 2
        c = (lo + hi) / 2
        cands = []
        if c - hf > 0.05:
            bm = min(bmax, math.sqrt(max(c * c - hf * hf, 0)) * 0.98)
            cands += [bm * s for s in (1.0, 0.7, 0.5, 0.35, 0.25, 0.15)]
        cands += [0.45, 0.4, 0.3]
        best = None
        for b in cands:
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
            Mpsi = (psup + abs(win.c0) + comb + abs(win.bp)) * K * (2 + K)
            Qp = arb(hf) * arb(64) / 15 * Mpsi * rho ** (-2 * n) / ((rho * rho - 1) * arb.pi())
            Rmax = arb(c) + semimajor
            val = Qp * Gsum(a, modes, arb(b), Rmax)
            if best is None or float(val.upper()) < float(best[0].upper()):
                best = (val, b)
        total += best[0]
        rows.append((float(best[0].upper()), lo, hi, best[1]))
    rows.sort(reverse=True)
    # node perturbation (crude, small ellipses)
    cmax2 = 2 * a * (2 * modes[-1] + 1)
    pert = arb(0)
    for (lo, hi, kind) in win.eds:
        b = 0.4 if kind == 'near' else 1.0
        hf = (hi - lo) / 2
        rho, semimajor = ellipse_params(hf, b)
        psup = psi_sup_on_ellipse((lo + hi) / 2, hf, b, None, z0=win.z0)
        comb = arb(0)
        for (cc_, ln, _) in win.coefs:
            comb += abs(cc_) * (arb(b) * ln).cosh()
        Mf = (psup + abs(win.c0) + comb + abs(win.bp)) * 4 * cmax2 * (2 * a * arb(b)).exp() / arb.pi()
        pert += 2 * arb(hf) * Mf / (arb(b).min(semimajor - arb(hf)))
    return total, pert, rows[:4]

if __name__ == '__main__':
    flint.ctx.prec = 256
    a = arb(307) / 256
    for (Tc, N, sector) in [(1170.0, 2300, 'even'), (2000.0, 2300, 'odd')]:
        win = WindowWA(a, 0.34, Tc, 66.0, gap_k=8.0, gap_max=11.5)
        noderad = arb(0)
        for (t, wq, _, r) in win.nodes():
            noderad = noderad.max(arb(r) + (win.a_ * t).rad() / win.a_ + (arb((win.a_ * t).mid()) / win.a_).rad())
        tot, pert, worst = bound(win, N, sector)
        eta = tot + pert * noderad * N
        print("%s Tc=%g: ||E_quad||_F <= %s ; node-pert term %s ; noderad %s ; eta = %s ; worst panels %s" % (
            sector, Tc, tot.str(3), (pert * noderad * N).str(3), noderad.str(3), eta.str(3),
            [("%.1e" % e, l, h_, round(b, 2)) for (e, l, h_, b) in worst]), flush=True)

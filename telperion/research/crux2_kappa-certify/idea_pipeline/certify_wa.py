"""WINDOW-AWARE two-stroke reduction of the window Weil form (new; replaces Zhu's pointwise envelope A_L on the
high-frequency range by the window-aware operator bound A' of the compressed prime comb).

Setting: f real, supp f in [-a, a], F(t) = int f e^{itu} du, Phi(t) = Re psi(z0 + it/2) + c0 (zeta: z0=1/4,
c0=-log pi; D: z0=3/4, c0=log(5/pi)), p(t) = sum_{log n < 2a} c_n cos(t log n), c_n = 2 Lambda(n)/sqrt n,
Q(f) = Pole(f) + (1/pi) int_0^inf (Phi - p)|F|^2 dt.

LEMMA A (window-aware comb bound).  For g in L^2(-a', a'), <P g, g> <= A'(a') ||g||^2 with
  A'(a') = sum_n |c_n| cos(pi/(M_n + 1)),  M_n = floor(2a'/log n) + 1,
because P = sum_n (c_n/2)(S_n + S_n^*), S_n the compressed translation by log n, and S_n + S_n^* decomposes
over the translation orbits of [-a', a'] into path-graph adjacencies with <= M_n vertices (norm 2cos(pi/(M+1))).
LEMMA B (localization).  k = 1_[-Tk,Tk] * gaussian_w (erf bump), h = 1 - k, chi = 1 - h^2 = k(2-k).
With g = FT^{-1}(hF) = f - k_check * f,  k_check(s) = sin(Tk s)/(pi s) e^{-w^2 s^2/4}:
  ||g 1_{|u|>a+eps}|| <= eta ||f||,  eta^2 = 2a (2/(pi^2 eps^2)) e^{-w^2 eps^2/2}/(w^2 eps),
  (1/pi) int h^2 p |F|^2 = <P_R g, g> <= A'(a+eps) (1/pi) int h^2 |F|^2 + A_L (2 eta + eta^2) ||f||^2.
REDUCTION.  With b' = log(q Tc/2pi) - 1/Tc - A' > 0 (envelope Phi >= log(q t/2pi) - 1/t for t >= Tc),
  Q(f) >= R''(f) = Pole(f) + (1/pi) int_0^{Tmax} chi (Phi - p - b') |F|^2 dt + b'' ||f||^2,
  b'' = b' - A_L(2 eta + eta^2) - deficit - xi,
  deficit = h(Tc)^2 (A' + |b'| - (psi(z0) + c0))_+   [h increasing on t >= 0, Phi >= psi(z0) + c0],
  xi = erfc((Tmax - Tk)/w) (log(Tmax/2 + 1) + 4/3 + |c0| + A_L + |b'| + |psi(z0)|)   [part beyond Tmax].
The threshold is Tc > 2 pi e^{A'} instead of Zhu's 2 pi e^{A_L}; asymptotically A' ~ A_L/2.
"""
import math
import sys
import time
import json
import flint
from flint import arb, acb, arb_mat
from rmat import sph_j_all, sph_i, sector_modes
from certify import ellipse_params, psi_sup_on_ellipse, gl_rule, make_panels
import galerkin_cos as gc
import vldlt
from rmat import min_eig_inverse_iter


def erf_arb(x):
    return x.erf()


class WindowWA:
    def __init__(self, a, eps, Tc, w, gap_k=10.0, gap_max=12.0, kind='zeta',
                 near=(8.0, 0.5, 48, 0.40), far=(2.0, 48, 2.0)):
        self.kind = kind
        self.a_ = arb(a)
        self.eps = arb(eps)
        self.w = arb(w)
        self.Tc = arb(Tc)
        self.Tk = self.Tc + arb(gap_k) * self.w
        self.Tmax = self.Tk + arb(gap_max) * self.w
        self.near = near
        self.far = far
        two_a = 2 * self.a_
        if kind == 'zeta':
            from rmat import primes_in_window
            pl = primes_in_window(self.a_)
            self.coefs = [(2 * arb(p).log() / arb(n).sqrt(), arb(n).log(), n) for (n, p) in pl]
            self.z0, self.c0, self.q = arb(1) / 4, -arb.pi().log(), arb(1)
        else:
            nmax = int(math.floor(math.exp(2 * float(self.a_.mid())))) + 1
            lam = gc.lambda_dh(nmax)
            self.coefs = []
            for n in range(2, nmax + 1):
                ln = arb(n).log()
                if ln < two_a and not lam[n].is_zero():
                    self.coefs.append((2 * lam[n] / arb(n).sqrt(), ln, n))
            self.z0, self.c0, self.q = arb(3) / 4, (arb(5) / arb.pi()).log(), arb(5)
        self.AL = sum((abs(c) for (c, _, _) in self.coefs), arb(0))
        ap = self.a_ + self.eps
        Ap = arb(0)
        self.Mn = {}
        for (c, ln, n) in self.coefs:
            r = 2 * ap / ln
            M = int(math.floor(float(r.upper()))) + 1       # safe (cos(pi/(M+1)) increasing in M)
            self.Mn[n] = M
            Ap += abs(c) * (arb.pi() / (M + 1)).cos()
        self.Ap = Ap
        self.bp = (self.q * self.Tc / (2 * arb.pi())).log() - 1 / self.Tc - self.Ap
        # error terms
        a_ = self.a_
        e, ww = self.eps, self.w
        eta2 = 2 * a_ * (2 / (arb.pi() ** 2 * e * e)) * (-(ww * e) ** 2 / 2).exp() / (ww * ww * e)
        self.eta = eta2.sqrt()
        self.err = self.AL * (2 * self.eta + eta2)
        hTc = 1 - self.kfun(self.Tc)
        psi0 = self.z0.digamma()
        self.deficit = hTc * hTc * (self.Ap + abs(self.bp) - (psi0 + self.c0)).max(arb(0))
        self.xi = ((self.Tmax - self.Tk) / ww).erfc() * ((self.Tmax / 2 + 1).log() + arb(4) / 3 + abs(self.c0)
                                                        + self.AL + abs(self.bp) + abs(psi0))
        self.bpp = self.bp - self.err - self.deficit - self.xi
        self.eds = make_panels(float(self.Tmax.upper()) + 1e-9, near[0], near[1], far[0])
        # make the last panel end exactly at Tmax (float edges): use float Tmax
        self.Tmax_f = self.eds[-1][1]

    def kfun(self, t):
        return (((t + self.Tk) / self.w).erf() - ((t - self.Tk) / self.w).erf()) / 2

    def chi(self, t):
        k = self.kfun(t)
        return k * (2 - k)

    def phi_minus_p(self, t):
        z = acb(self.z0, t / 2)
        v = z.digamma().real + self.c0
        for (c, ln, n) in self.coefs:
            v -= c * (t * ln).cos()
        return v

    def weight(self, t):
        return self.chi(t) * (self.phi_minus_p(t) - self.bp)

    def nodes(self):
        rn = gl_rule(self.near[2])
        rf = gl_rule(self.far[1])
        out = []
        for pi_, (lo, hi, kind) in enumerate(self.eds):
            rule = rn if kind == 'near' else rf
            c = (arb(lo) + arb(hi)) / 2
            h = (arb(hi) - arb(lo)) / 2
            for (r, wgt) in rule:
                tt = c + h * r
                out.append((arb(tt.mid()), h * wgt, pi_, tt.rad()))
        return out

    def quad_error_bound(self, cmax2):
        total = arb(0)
        pert = arb(0)
        for (lo, hi, kind) in self.eds:
            n, b = (self.near[2], self.near[3]) if kind == 'near' else (self.far[1], self.far[2])
            h = (arb(hi) - arb(lo)) / 2
            hf = (hi - lo) / 2
            rho, semimajor = ellipse_params(hf, b)
            psup = psi_sup_on_ellipse((lo + hi) / 2, hf, b, None, z0=self.z0)
            comb = arb(0)
            for (cc_, ln, _) in self.coefs:
                comb += abs(cc_) * (arb(b) * ln).cosh()
            y = arb(b) / self.w
            K = 1 + 2 / arb.pi().sqrt() * y * (y * y).exp()
            chisup = K * (2 + K)
            Mpsi = (psup + abs(self.c0) + comb + abs(self.bp)) * chisup
            Mf = Mpsi * cmax2 * (2 * self.a_ * arb(b)).exp() / arb.pi()
            total += h * arb(64) / 15 * Mf * rho ** (-2 * n) / (rho * rho - 1)
            dist = arb(b).min(semimajor - h)
            pert += 2 * h * Mf / dist
        return total, pert

    def tail_bounds(self, sector, N, extra_terms=400):
        a = self.a_
        T = arb(self.Tmax_f)
        psi0 = self.z0.digamma()
        psiT = acb(self.z0, T / 2).digamma().real
        Pm = abs(psi0).max(abs(psiT)) + abs(self.c0) + self.AL + abs(self.bp)
        modes = sector_modes(sector, N + extra_terms)
        lead, tail = modes[:N], modes[N:]
        pi = arb.pi()

        def c(n):
            return (2 * a * (2 * n + 1)).sqrt()

        def dfact(n):
            return arb(2 * n + 2).gamma() / (arb(2) ** (n + 1) * arb(n + 1).gamma())
        half = a / 2
        coshh = half.cosh() if self.kind == 'zeta' else arb(0)

        def jbound_int(n):
            return a ** n * T ** (n + 1) / ((n + 1) * dfact(n))

        def pbound(n):
            return c(n) * half ** n * coshh / dfact(n)
        plead = [c(m) * sph_i(m, half) * (1 if self.kind == 'zeta' else 0) for m in lead]
        sum_c_lead = sum((c(m) for m in lead), arb(0))
        sum_p_lead = sum((abs(p) for p in plead), arb(0))
        S1 = arb(0)
        S2 = arb(0)
        col_max = arb(0)
        last1 = last2 = None
        for n in tail:
            t1 = c(n) * jbound_int(n)
            t2 = pbound(n)
            S1 += t1
            S2 += t2
            col_max = col_max.max(sum_c_lead * Pm / pi * t1 + 2 * sum_p_lead * t2)
            last1, last2 = t1, t2
        n_last = tail[-1]
        ratio = (a * T) ** 2 / ((2 * n_last + 3) * (2 * n_last + 5))
        if not (ratio * arb(101) / 100 < arb(45) / 100):
            raise RuntimeError("tail not yet geometric")
        S1 += last1
        S2 += last2
        row_max = arb(0)
        for i, m in enumerate(lead):
            row_max = row_max.max(c(m) * Pm / pi * S1 + 2 * abs(plead[i]) * S2)
        epsB = (row_max * col_max).sqrt()
        m0 = tail[0]
        if not ((a * T) ** 2 * arb(101) / 100 < (2 * m0 + 3) * (2 * m0 + 5)):
            raise RuntimeError("tail rows not decreasing at m0=%d" % m0)
        f_m0 = c(m0) * (a * T) ** m0 / dfact(m0)
        epsD = Pm / pi * f_m0 * S1 + 2 * pbound(m0) * S2
        return dict(epsB=epsB, epsD=epsD, first_tail=m0)


    def tail_bounds_sharp(self, sector, N, n_extra=6):
        """Sharper rigorous tails for n >= n0 > xmax = a*Tmax:
        (i) j_n(x) > 0 and increasing on [0, xmax] (x < n: j_n' = (n/x) j_n - j_{n+1}, j_{n+1} < j_n x/(2n+3-x));
        (ii) j_{n+1}(xmax) <= j_n(xmax) * xmax/(2n+3-xmax)   (minimal-solution continued fraction, Pincherle).
        So sup_{t<=Tmax}|j_n(a t)| <= j_n(xmax) =: J_n, computed rigorously at n0 and propagated by (ii)."""
        from rmat import sph_j_all
        a = self.a_
        T = arb(self.Tmax_f)
        xmax = a * T
        psi0 = self.z0.digamma()
        psiT = acb(self.z0, T / 2).digamma().real
        Pm = abs(psi0).max(abs(psiT)) + abs(self.c0) + self.AL + abs(self.bp)
        modes = sector_modes(sector, N + n_extra)
        lead, tail = modes[:N], modes[N:]
        n0 = tail[0]
        if not (arb(n0) > xmax * arb(102) / 100):
            raise RuntimeError("sharp tails need n0 > 1.02 a Tmax")
        pi = arb.pi()
        def c(n):
            return (2 * a * (2 * n + 1)).sqrt()
        xm = arb(xmax.upper())                      # j_n increasing in x: use the upper endpoint
        js = sph_j_all(xm, n0 + 1)
        Jn0 = abs(js[n0])
        # geometric majorant for sum_{n in tail} c_n J_n (step 2 in n): J_{n+2} <= J_n rho_n rho_{n+1}
        rho = lambda n: xm / (2 * n + 3 - xm)
        q = rho(n0) * rho(n0 + 1) * (c(n0 + 2) / c(n0))
        if not (q < 1):
            raise RuntimeError("tail ratio not < 1")
        SJ = c(n0) * Jn0 / (1 - q)                   # >= sum_{n in tail} c_n J_n  (ratios decrease in n)
        half = a / 2
        coshh = half.cosh() if self.kind == 'zeta' else arb(0)
        def dfact(n):
            return arb(2 * n + 2).gamma() / (arb(2) ** (n + 1) * arb(n + 1).gamma())
        pb0 = c(n0) * half ** n0 * coshh / dfact(n0)
        S2 = 2 * pb0                                # geometric (ratio << 1/2) for the pole tail
        plead = [c(m) * sph_i(m, half) * (1 if self.kind == 'zeta' else 0) for m in lead]
        sum_c_lead = sum((c(m) for m in lead), arb(0))
        sum_p_lead = sum((abs(p) for p in plead), arb(0))
        # coupling rows (m lead): Pm/pi c_m T SJ + 2|p_m| S2 ; columns (n tail): Pm/pi sum_c_lead c_n T J_n + 2 sum_p p_n
        row_max = arb(0)
        for i, m in enumerate(lead):
            row_max = row_max.max(c(m) * Pm / pi * T * SJ + 2 * abs(plead[i]) * S2)
        col_max = sum_c_lead * Pm / pi * c(n0) * T * Jn0 + 2 * sum_p_lead * pb0
        epsB = (row_max * col_max).sqrt()
        epsD = Pm / pi * c(n0) * Jn0 * T * SJ + 2 * pb0 * S2
        return dict(epsB=epsB, epsD=epsD, first_tail=n0, Jn0=Jn0)


def inv_iter_ldl(M, iters=5):
    """Smallest-eigenvalue estimate by inverse iteration with ONE floating Cholesky (at FPREC) and
    high-precision triangular solves (Python loops, O(n^2)).  Estimate only; the certificate is verify_chol."""
    import random
    R, j, s = vldlt.floating_chol(M, 0.0, b=64, fprec=FPREC)
    if R is None:
        raise RuntimeError("not PD at 0")
    n = M.nrows()
    old = flint.ctx.prec
    flint.ctx.prec = FPREC
    try:
        rnd = random.Random(3)
        x = [arb(rnd.uniform(-1, 1)) for _ in range(n)]
        for _ in range(iters):
            z = [None] * n
            for i in range(n):
                acc = x[i]
                Ri = R[i]
                for k in range(i):
                    acc -= Ri[k] * z[k]
                z[i] = arb((acc / Ri[i]).mid())
            y = [None] * n
            for i in range(n - 1, -1, -1):
                acc = z[i]
                for k in range(i + 1, n):
                    acc -= R[k][i] * y[k]
                y[i] = arb((acc / R[i][i]).mid())
            nrm = sum((t * t for t in y), arb(0)).sqrt()
            x = [arb((t / nrm).mid()) for t in y]
        Xm = arb_mat([[t] for t in x])
        Mx = M.mid() * Xm
        num = sum((x[i] * Mx[i, 0] for i in range(n)), arb(0))
        den = sum((t * t for t in x), arb(0))
        return float((num / den).mid())
    finally:
        flint.ctx.prec = old

def inv_iter_estimate(M, iters=8):
    """Rayleigh-quotient estimate of the smallest eigenvalue of a (numerically) PD arb matrix via inverse
    iteration with floating 'approx' solves (no error bounds needed: the certificate is the verified LDL^T)."""
    import random
    n = M.nrows()
    Mm = M.mid()
    rnd = random.Random(7)
    x = arb_mat([[arb(rnd.uniform(-1, 1))] for _ in range(n)])
    lam = None
    for _ in range(iters):
        y = Mm.solve(x, algorithm='approx')
        nrm = sum((float(abs(y[i, 0]).mid()) ** 2 for i in range(n))) ** 0.5
        x = arb_mat([[arb(y[i, 0].mid()) / nrm] for i in range(n)])
        Mx = Mm * x
        num = arb(0)
        den = arb(0)
        for i in range(n):
            num += x[i, 0] * Mx[i, 0]
            den += x[i, 0] * x[i, 0]
        lam = float((num / den).mid())
    return lam


CHUNK = 3000

def build_leading(win, sector, N, verbose=True, chunk=None):
    if chunk is None:
        chunk = CHUNK
    a_ = win.a_
    modes = sector_modes(sector, N)
    nmax = modes[-1]
    cn = [(2 * a_ * (2 * n + 1)).sqrt() for n in modes]
    sg = [(-1 if ((n // 2 if sector == 'even' else (n - 1) // 2) % 2) else 1) for n in modes]
    pi = arb.pi()
    nodes = win.nodes()
    t0 = time.time()
    G = None
    for s in range(0, len(nodes), chunk):
        rows, wrows = [], []
        for (t, wq, _, _) in nodes[s:s + chunk]:
            x = arb((a_ * t).mid())
            t_eff = x / a_
            js = sph_j_all(x, nmax)
            row = [sg[i] * cn[i] * js[modes[i]] for i in range(N)]
            wt = wq * win.weight(t_eff) / pi
            rows.append(row)
            wrows.append([wt * v for v in row])
        Jt = arb_mat(rows).transpose()
        del rows
        WJ = arb_mat(wrows)
        del wrows
        part = Jt * WJ
        del Jt, WJ
        G = part if G is None else G + part
        del part
    y = a_ / 2
    pv = [cn[i] * sph_i(modes[i], y) for i in range(N)]
    sp = ((2 if sector == 'even' else -2) if win.kind == 'zeta' else 0)
    M = arb_mat(N, N)
    for i in range(N):
        for k in range(i, N):
            v = (G[i, k] + G[k, i]) / 2 + sp * pv[i] * pv[k]
            if i == k:
                v += win.bpp
            M[i, k] = v
            M[k, i] = v
    if verbose:
        print("  [WA] leading block %s N=%d nodes=%d (%.1fs)" % (sector, N, len(nodes), time.time() - t0), flush=True)
    cmax2 = max(cn, key=lambda v: float(v.mid())) ** 2
    return M, cmax2


GAPK, GAPM = 7.0, 10.0
SAVE_M = False
FPREC = 384

def run(a_str, eps, Tc, w, N, prec=256, sectors=('even', 'odd'), kind='zeta', tag=None, frac=0.98,
        certify_it=True):
    flint.ctx.prec = prec
    if '/' in a_str:
        p, q = a_str.split('/')
        a = arb(int(p)) / int(q)
    else:
        a = arb(float(a_str))
    win = WindowWA(a, eps, Tc, w, gap_k=GAPK, gap_max=GAPM, kind=kind)
    info = dict(a=a_str, kind=kind, eps=eps, Tc=Tc, w=w, Tk=float(win.Tk.mid()), Tmax=win.Tmax_f, N=N,
                comb=[n for (_, _, n) in win.coefs], Mn=win.Mn, A_L=win.AL.str(12), Aprime=win.Ap.str(12),
                bprime=win.bp.str(12), eta=win.eta.str(5), err=win.err.str(5), deficit=win.deficit.str(5),
                xi=win.xi.str(5), bpp=win.bpp.str(12), sectors={})
    print("[WA %s] a=%s comb=%s A_L=%s  A'=%s (Mn=%s)  Tc=%s Tk=%s Tmax=%s  b'=%s  eta=%s err=%s deficit=%s xi=%s  b''=%s" % (
        kind, a_str, info['comb'], win.AL.str(6), win.Ap.str(6), win.Mn, Tc, win.Tk.str(6), win.Tmax_f,
        win.bp.str(6), win.eta.str(3), win.err.str(3), win.deficit.str(3), win.xi.str(3), win.bpp.str(6)), flush=True)
    assert win.bpp > 0
    noderad = arb(0)
    for (t, wq, _, r) in win.nodes():
        noderad = noderad.max(arb(r) + (win.a_ * t).rad() / win.a_ + (arb((win.a_ * t).mid()) / win.a_).rad())
    for sector in sectors:
        t0 = time.time()
        M, cmax2 = build_leading(win, sector, N)
        # smallest eigenvalue: sign test by floating LDL^T at 0, estimate by inverse iteration ('approx' solves)
        def pd(l):
            R_, j, s_ = vldlt.floating_chol(M, l, b=64, fprec=FPREC)
            return R_ is not None
        if not pd(0.0):
            info['sectors'][sector] = dict(pd=False)
            print("  %s: R'' NOT PD (a negative eigenvalue exists)  (%.0fs)" % (sector, time.time() - t0), flush=True)
            continue
        lo = inv_iter_ldl(M)
        # make sure the estimate is below lam_min (Rayleigh quotients are upper bounds): back off if needed
        k_ = 0
        while not pd(lo * frac) and k_ < 60:
            lo *= 0.5
            k_ += 1
        s = dict(pd=True, lam_min_est='%.6e' % lo)
        if SAVE_M and tag:
            with open('M_%s_%s.txt' % (tag, sector), 'w') as fh:
                for i in range(M.nrows()):
                    fh.write(' '.join('%s|%s' % (M[i,k].mid().str(70, radius=False), M[i,k].rad().str(3, radius=False)) for k in range(M.ncols())) + '\n')
        if certify_it:
            lam0 = float('%.4e' % (lo * frac * 0.999))
            vr = vldlt.verify_chol(M, lam0, b=64, fprec=FPREC)
            k2 = 0
            while not vr['ok'] and k2 < 8:
                lam0 = float('%.4e' % (lam0 * 0.5))
                vr = vldlt.verify_chol(M, lam0, b=64, fprec=FPREC)
                k2 += 1
            qerr, pert = win.quad_error_bound(cmax2)
            eta_q = (qerr + pert * noderad) * N
            try:
                import quad_opt2
                tot2, pert2, _ = quad_opt2.bound(win, N, sector)
                eta2 = tot2 + pert2 * noderad * N
                if eta2 < eta_q:
                    eta_q = eta2          # refined mode-weighted Bernstein bound (same nodes)
            except Exception as ex:
                print("  refined quadrature bound unavailable:", ex, flush=True)
            try:
                tb = win.tail_bounds_sharp(sector, N)
                s['tails'] = 'sharp'
            except Exception as ex:
                tb = win.tail_bounds(sector, N)
                s['tails'] = 'crude'
            final = (vr['lower'] - eta_q).min(win.bpp - tb['epsD']) - tb['epsB'] if vr['ok'] else None
            s.update(lam0=lam0, verified=vr['ok'], resid=vr['Efro'].str(5) if vr['ok'] else vr.get('reason'),
                     quad=eta_q.str(5), epsB=tb['epsB'].str(5), epsD=tb['epsD'].str(5),
                     final_lower=final.str(12) if final is not None else None,
                     final_positive=bool(final is not None and final > 0))
        s['seconds'] = round(time.time() - t0, 1)
        info['sectors'][sector] = s
        print("  %s: %s" % (sector, s), flush=True)
    if tag:
        json.dump(info, open('certwa_%s.json' % tag, 'w'), indent=1, default=str)
    return info


if __name__ == '__main__':
    a_str = sys.argv[1]
    eps, Tc, w, N = float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    prec = int(sys.argv[6]) if len(sys.argv) > 6 else 256
    kind = sys.argv[7] if len(sys.argv) > 7 else 'zeta'
    tag = sys.argv[8] if len(sys.argv) > 8 else None
    secs = tuple(sys.argv[9].split(',')) if len(sys.argv) > 9 else ('even', 'odd')
    run(a_str, eps, Tc, w, N, prec, sectors=secs, kind=kind, tag=tag)

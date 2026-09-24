"""Rigorous certificate:  Q(f) >= lam * ||f||^2  for all f in L^2[-a, a]  (window Weil form of zeta).

Chain (every step either exact ball arithmetic (Arb via python-flint) or a stated paper lemma):
  [P1] Q(f) = Pole(f) + (1/pi) int_0^inf Psi_a(t)|F(t)|^2 dt               (Weil explicit formula, frequency form)
  [P2] envelope: Re psi(1/4+it/2) - log pi >= log(t/2pi) - 1/t   (t >= 3/4; Binet's 2nd formula)
  [P3] Zhu one-stroke: Q(f) >= R(f) = Pole + (1/pi) int_0^{T#}(Psi_a - b*)|F|^2 + b*||f||^2, b* > 0
  [C1] leading N x N block of R in Legendre basis: composite Gauss-Legendre with dyadic nodes, Arb balls
  [C2] quadrature truncation error: Bernstein-ellipse bound per panel, sup on ellipse via Arb covers
  [C3] node-perturbation error (dyadic nodes vs exact GL roots): Cauchy derivative bound
  [C4] tail: |j_n(x)| <= x^n/(2n+1)!!, |i_n(y)| <= y^n cosh(y)/(2n+1)!!; Schur test + Gershgorin
  [C5] interval LDL^T of (leading block - lam0 I): all pivots certified > 0 for every matrix in the box
  [C6] two-block bound: lam_min(R) >= min(lam0 - eta, b* - eps_D) - eps_B
Both parity sectors; Q(f) = Q(f_even) + Q(f_odd) and Q(u+iv) = Q(u) + Q(v) give the full complex window.
"""
import math
import sys
import time
import json
import flint
from flint import arb, acb, arb_mat
import rmat
from rmat import sph_j_all, sph_i, primes_in_window, comb_mass, sector_modes


def ellipse_params(h, b):
    """Bernstein ellipse for [c-h, c+h] with semi-minor axis b: rho = b/h + sqrt(1 + (b/h)^2)."""
    r = arb(b) / arb(h)
    rho = r + (1 + r * r).sqrt()
    semimajor = arb(h) * (rho + 1 / rho) / 2
    return rho, semimajor


def psi_sup_on_ellipse(c, h, b, narcs=None, z0=None):
    """Rigorous upper bound of |(psi(1/4 + i z/2) + psi(1/4 - i z/2))/2| for z in the closed Bernstein
    ellipse around [c-h, c+h] with semi-minor axis b.  Analytic bound (no ball digamma):
      w = 1/4 -+ i z/2:  Re w >= sigma := 1/4 - b/2,  |Im w| = |Re z|/2 in [(c - A)/2, (c + A)/2]
      (A = semi-major axis), |w| <= wmax.  Shift by k >= 1 - sigma: psi(w) = psi(w+k) - sum_{j<k} 1/(w+j),
      and for Re u >= p > 0 (Binet's 2nd formula, |s^2+u^2| >= p^2):
          |psi(u) - log u + 1/(2u)| <= 1/(12 p^2),   |log u| <= log|u| + pi/2 when |u| >= 1.
      |w + j| >= max(sigma + j, min|Im w|)."""
    rho, A = ellipse_params(h, b)
    cc = arb(c)
    bb = arb(b)
    if z0 is None:
        z0 = arb(1) / 4
    sigma = z0 - bb / 2
    imw_min = ((cc - A) / 2).max(arb(0)) if float(c) - float(A.mid()) > 0 else arb(0)
    wmax = (z0 + bb / 2) + (abs(cc) + A) / 2
    k = max(1, int(math.ceil(1 - float(sigma.mid()) + 1e-9)))
    p = sigma + k
    if not (p >= 1):
        k += 1
        p = sigma + k
    bound = (wmax + k).log() + arb.pi() / 2 + 1 / (2 * p) + 1 / (12 * p * p)
    for j in range(k):
        dj = (sigma + j).max(imw_min)
        if not (dj > 0):
            raise RuntimeError("pole not excluded: c=%s b=%s j=%d" % (c, b, j))
        bound += 1 / dj
    return bound


def gl_rule(npts):
    return [arb.legendre_p_root(npts, k, weight=True) for k in range(npts)]


def make_panels(Tsharp, near_end, near_w, far_w):
    eds = []
    x = 0.0
    while x < min(near_end, Tsharp) - 1e-12:
        y = min(x + near_w, near_end, Tsharp)
        eds.append((x, y, 'near'))
        x = y
    while x < Tsharp - 1e-12:
        y = min(x + far_w, Tsharp)
        eds.append((x, y, 'far'))
        x = y
    return eds


class Window:
    def __init__(self, a, Tsharp, near=(8.0, 0.5, 48, 0.40), far=(2.0, 48, 2.0), kind='zeta'):
        self.kind = kind
        self.a = a
        self.a_ = arb(a)
        self.T = Tsharp
        self.T_ = arb(Tsharp)
        self.near = near
        self.far = far
        self.eds = make_panels(Tsharp, near[0], near[1], far[0])
        if kind == 'zeta':
            self.plist = primes_in_window(a)
            self.coefs = [(2 * arb(p).log() / arb(n).sqrt(), arb(n).log()) for (n, p) in self.plist]
            self.z0 = arb(1) / 4
            self.c0 = -arb.pi().log()
            self.q = arb(1)
        else:
            import galerkin_cos as gc
            two_a = 2 * self.a_
            nmax = int(math.floor(math.exp(2 * float(a)))) + 1
            lam = gc.lambda_dh(nmax)
            self.coefs = []
            self.plist = []
            for n in range(2, nmax + 1):
                ln = arb(n).log()
                if ln < two_a and not lam[n].is_zero():
                    self.coefs.append((2 * lam[n] / arb(n).sqrt(), ln))
                    self.plist.append((n, None))
                elif not (ln < two_a) and not (ln > two_a):
                    raise ValueError("straddle")
            self.z0 = arb(3) / 4
            self.c0 = (arb(5) / arb.pi()).log()
            self.q = arb(5)
        self.AL = sum((abs(c) for (c, _) in self.coefs), arb(0))
        # envelope: Re psi(z0 + it/2) + c0 >= log(q t/2pi) - 1/t   (zeta: t >= 3/4; D: t >= 27/16)
        self.bstar = (self.q * self.T_ / (2 * arb.pi())).log() - 1 / self.T_ - self.AL

    # --------------------------------------------------------------- Psi_a on the real line
    def psi_real(self, t):
        z = acb(self.z0, t / 2)
        v = z.digamma().real + self.c0
        for (c, ln) in self.coefs:
            v -= c * (t * ln).cos()
        return v

    def nodes(self):
        """(t_dyadic, weight_ball, panel_index, radius_of_exact_node) for the composite rule."""
        rn = gl_rule(self.near[2])
        rf = gl_rule(self.far[1])
        out = []
        for pi_, (lo, hi, kind) in enumerate(self.eds):
            rule = rn if kind == 'near' else rf
            c = (arb(lo) + arb(hi)) / 2
            h = (arb(hi) - arb(lo)) / 2
            for (r, w) in rule:
                tt = c + h * r
                out.append((arb(tt.mid()), h * w, pi_, tt.rad()))
        return out

    # --------------------------------------------------------------- [C2]+[C3] quadrature error
    def quad_error_bound(self, cmax2, narcs=64):
        """Bound eta with |E_kl| <= eta for every entry (k,l) of the leading block, where E is the
        difference between the exact integral (1/pi) int_0^{T#} (Psi_a - b*) g_k g_l dt and the
        composite rule evaluated at the dyadic nodes.  |g_k g_l| <= c_k c_l e^{2 a |Im z|} <= cmax2 e^{2ab}."""
        total = arb(0)
        pert = arb(0)
        logpi = arb.pi().log()
        per_panel = []
        for (lo, hi, kind) in self.eds:
            if kind == 'near':
                n = self.near[2]
                b = self.near[3]
            else:
                n = self.far[1]
                b = self.far[2]
            h = (arb(hi) - arb(lo)) / 2
            c = (arb(lo) + arb(hi)) / 2
            hf = (hi - lo) / 2
            rho, semimajor = ellipse_params(hf, b)
            psup = psi_sup_on_ellipse((lo + hi) / 2, hf, b, 256 if kind == 'near' else narcs, z0=self.z0)
            comb = arb(0)
            for (cc_, ln) in self.coefs:
                comb += abs(cc_) * (arb(b) * ln).cosh()
            Mpsi = psup + abs(self.c0) + comb + abs(self.bstar)
            Mf = Mpsi * cmax2 * (2 * self.a_ * arb(b)).exp() / arb.pi()
            err = h * arb(64) / 15 * Mf * rho ** (-2 * n) / (rho * rho - 1)
            total += err
            # node perturbation: sum |w_i| |f(t_i) - f(t_i*)| <= 2h * max|f'| * max rad; |f'| <= Mf / dist
            dist = arb(b).min(semimajor - h)
            per_panel.append(err)
            pert += 2 * h * Mf / dist
        return total, pert, per_panel

    # --------------------------------------------------------------- [C4] tails
    def psi_abs_max_real(self):
        """max_{t in [0,T#]} |Psi_a(t) - b*| via monotonicity of Re psi(1/4+it/2) in |t|."""
        psi0 = self.z0.digamma()
        psiT = acb(self.z0, self.T_ / 2).digamma().real
        m = abs(psi0).max(abs(psiT))
        return m + abs(self.c0) + self.AL + abs(self.bstar)

    def tail_bounds(self, sector, N, extra_terms=400):
        """eps_B (Schur-test bound of the coupling block) and eps_D (Gershgorin deviation of the
        tail block from b* I).  Leading modes: first N modes of the sector; tail: all higher modes."""
        a = self.a_
        T = self.T_
        Pm = self.psi_abs_max_real()
        modes = sector_modes(sector, N + extra_terms)
        lead = modes[:N]
        tail = modes[N:]
        pi = arb.pi()

        def c(n):
            return (2 * a * (2 * n + 1)).sqrt()

        def dfact(n):   # (2n+1)!!
            return arb(2 * n + 2).gamma() / (arb(2) ** (n + 1) * arb(n + 1).gamma())

        half = a / 2
        coshh = half.cosh()

        def jbound_int(n):   # int_0^T (a t)^n/(2n+1)!! dt
            return a ** n * T ** (n + 1) / ((n + 1) * dfact(n))

        def pbound(n):       # |p_n| <= c_n (a/2)^n cosh(a/2)/(2n+1)!!
            return c(n) * half ** n * coshh / dfact(n)

        # exact |p_m| for leading modes (no pole term for D)
        if self.kind != 'zeta':
            coshh = arb(0)
        plead = [c(m) * sph_i(m, half) * (1 if self.kind == 'zeta' else 0) for m in lead]
        sum_c_lead = sum((c(m) for m in lead), arb(0))
        sum_p_lead = sum((abs(p) for p in plead), arb(0))
        # tail sums over n in tail (finite list), plus geometric remainder beyond
        S1 = arb(0)   # sum_n c_n int_0^T (at)^n/(2n+1)!!
        S2 = arb(0)   # sum_n |p_n| bound
        last1 = None
        last2 = None
        col_max = arb(0)
        terms1 = []
        for n in tail:
            t1 = c(n) * jbound_int(n)
            t2 = pbound(n)
            S1 += t1
            S2 += t2
            terms1.append((n, t1, t2))
            col = sum_c_lead * Pm / pi * t1 + 2 * sum_p_lead * t2
            col_max = col_max.max(col)
            last1, last2 = t1, t2
        # geometric remainder: ratio of consecutive tail terms is < 1/2 by the end (checked)
        n_last = tail[-1]
        ratio = (a * T) ** 2 / ((2 * n_last + 3) * (2 * n_last + 5))
        if not (ratio * arb(101) / 100 < arb(45) / 100):
            raise RuntimeError("tail not yet geometric at n=%d" % n_last)
        S1 += last1
        S2 += last2
        # rows (fixed leading m): sum_n |B_mn| <= c_m Pm/pi S1 + 2|p_m| S2
        row_max = arb(0)
        for i, m in enumerate(lead):
            row = c(m) * Pm / pi * S1 + 2 * abs(plead[i]) * S2
            row_max = row_max.max(row)
        epsB = (row_max * col_max).sqrt()
        # tail block rows (fixed tail m, sum over tail n):
        #   |C_mn| <= Pm/pi c_m c_n a^{m+n} T^{m+n+1}/((m+n+1)(2m+1)!!(2n+1)!!)
        #          <= Pm/pi * f_m * c_n a^n T^{n+1}/((n+1)(2n+1)!!),  f_m = c_m (aT)^m/(2m+1)!!
        #   so row_m <= Pm/pi f_m S1 + 2 pbound(m) S2, and f_m, pbound(m) decrease in m on the tail
        #   (f_{m+2}/f_m <= 1.01 (aT)^2/((2m+3)(2m+5)) < 1 there; checked below).
        m0 = tail[0]
        f_m0 = c(m0) * (a * T) ** m0 / dfact(m0)
        if not ((a * T) ** 2 * arb(101) / 100 < (2 * m0 + 3) * (2 * m0 + 5)):
            raise RuntimeError("tail rows not yet decreasing at m0=%d" % m0)
        epsD = Pm / pi * f_m0 * S1 + 2 * pbound(m0) * S2
        return dict(epsB=epsB, epsD=epsD, row_max=row_max, col_max=col_max, Pm=Pm,
                    first_tail=tail[0], ratio_end=ratio)


def build_leading(win, sector, N, verbose=True):
    """Leading N x N block of R in the sector, Arb balls (composite rule at dyadic nodes)."""
    a_ = win.a_
    modes = sector_modes(sector, N)
    nmax = modes[-1]
    cn = [(2 * a_ * (2 * n + 1)).sqrt() for n in modes]
    sg = []
    for n in modes:
        k = n // 2 if sector == 'even' else (n - 1) // 2
        sg.append(-1 if k % 2 else 1)
    pi = arb.pi()
    nodes = win.nodes()
    t0 = time.time()
    G = None
    chunk = 3000
    for s in range(0, len(nodes), chunk):
        rows = []
        wrows = []
        for (t, w, _, _) in nodes[s:s + chunk]:
            # effective node t' = x/a with x = dyadic midpoint of a t (exact); |t' - t| <= rad(a t)/a
            x = arb((a_ * t).mid())
            t_eff = x / a_
            js = sph_j_all(x, nmax)
            row = [sg[i] * cn[i] * js[modes[i]] for i in range(N)]
            wt = w * (win.psi_real(t_eff) - win.bstar) / pi
            rows.append(row)
            wrows.append([wt * v for v in row])
        J = arb_mat(rows)
        WJ = arb_mat(wrows)
        part = J.transpose() * WJ
        G = part if G is None else G + part
    t1 = time.time()
    y = a_ / 2
    pv = [cn[i] * sph_i(modes[i], y) for i in range(N)]
    sp = (2 if sector == 'even' else -2) if win.kind == 'zeta' else 0
    M = arb_mat(N, N)
    for i in range(N):
        for k in range(i, N):
            v = (G[i, k] + G[k, i]) / 2 + sp * pv[i] * pv[k]
            if i == k:
                v += win.bstar
            M[i, k] = v
            M[k, i] = v
    if verbose:
        print("  leading block %s N=%d nodes=%d  (%.1fs)" % (sector, N, len(nodes), t1 - t0), flush=True)
    cmax2 = max(cn, key=lambda v: float(v.mid())) ** 2
    return M, cmax2


def interval_ldlt_pos(M, lam0, verbose=False):
    """Interval LDL^T of M - lam0 I (Python loops, Arb balls).  Returns (ok, min_pivot, pivots).
    ok == True certifies: every symmetric matrix in the ball enclosure has M - lam0 I positive definite."""
    n = M.nrows()
    A = [[M[i, j] for j in range(n)] for i in range(n)]
    for i in range(n):
        A[i][i] = A[i][i] - lam0
    piv = []
    L = [[None] * n for _ in range(n)]
    D = [None] * n
    for j in range(n):
        s = A[j][j]
        Lj = L[j]
        for k in range(j):
            s -= Lj[k] * Lj[k] * D[k]
        if not (s > 0):
            return False, s, piv
        D[j] = s
        piv.append(s)
        invd = 1 / s
        for i in range(j + 1, n):
            Li = L[i]
            v = A[i][j]
            for k in range(j):
                v -= Li[k] * Lj[k] * D[k]
            Li[j] = v * invd
        if verbose and j % 50 == 0:
            print("    pivot", j, s.str(5), flush=True)
    mp = min(piv, key=lambda v: float(v.lower()))
    return True, mp, piv


def certify(a, Tsharp, N, lam0s, prec=256, sectors=('even', 'odd'), near=(8.0, 0.5, 48, 0.40),
            far=(2.0, 48, 2.0), out=None):
    flint.ctx.prec = prec
    win = Window(a, Tsharp, near, far)
    rep = dict(a=str(a), Tsharp=Tsharp, N=N, prec=prec, primes=[n for (n, p) in win.plist],
               A_L=win.AL.str(20), bstar=win.bstar.str(20), sectors={})
    print("a=%s T#=%s  A_L=%s  b*=%s  primes=%s" % (a, Tsharp, win.AL.str(12), win.bstar.str(12),
                                                    rep['primes']), flush=True)
    assert win.bstar > 0 and win.T_ >= arb(3) / 4
    for sector, lam0 in zip(sectors, lam0s):
        t0 = time.time()
        M, cmax2 = build_leading(win, sector, N)
        qerr, pert, _ = win.quad_error_bound(cmax2)
        # node radius: |t_dyadic - t_exact| <= rad of the GL-root ball image (max over nodes)
        noderad = arb(0)
        for (t, w, _, r) in win.nodes():
            noderad = noderad.max(arb(r) + (win.a_ * t).rad() / win.a_ + (arb((win.a_ * t).mid()) / win.a_).rad())
        pert_total = pert * noderad
        eta = (qerr + pert_total) * N          # ||E||_2 <= N max|E_kl|
        tb = win.tail_bounds(sector, N)
        ok, minpiv, piv = interval_ldlt_pos(M, arb(lam0))
        lam_lead = arb(lam0) - eta
        final = lam_lead.min(win.bstar - tb['epsD']) - tb['epsB']
        srep = dict(lam0=lam0, ldlt_ok=ok, min_pivot=minpiv.str(8), quad_err_entry=qerr.str(5),
                    node_pert_entry=pert_total.str(5), eta=eta.str(5), epsB=tb['epsB'].str(5),
                    epsD=tb['epsD'].str(5), first_tail_order=tb['first_tail'],
                    final_lower=final.str(12) if ok else None,
                    final_positive=bool(ok and final > 0), seconds=time.time() - t0)
        rep['sectors'][sector] = srep
        print("  %s: LDL^T(M - %.3e I) ok=%s minpiv=%s  eta=%s  epsB=%s  epsD=%s  => lam_min(Q) >= %s" % (
            sector, lam0, ok, minpiv.str(5), eta.str(3), tb['epsB'].str(3), tb['epsD'].str(3),
            final.str(8) if ok else 'FAIL'), flush=True)
    if out:
        json.dump(rep, open(out, 'w'), indent=1)
    return rep


if __name__ == "__main__":
    # a must be EXACT (dyadic): either p/q with q a power of two, or a decimal taken as its exact double
    if '/' in sys.argv[1]:
        pq = sys.argv[1].split('/')
        a = arb(int(pq[0])) / int(pq[1])
    else:
        a = arb(float(sys.argv[1]))
    assert a.rad() == 0, "window half-width must be exact"

    T = float(sys.argv[2])
    N = int(sys.argv[3])
    lam_even = float(sys.argv[4])
    lam_odd = float(sys.argv[5])
    prec = int(sys.argv[6]) if len(sys.argv) > 6 else 256
    out = sys.argv[7] if len(sys.argv) > 7 else None
    certify(a, T, N, (lam_even, lam_odd), prec=prec, out=out)

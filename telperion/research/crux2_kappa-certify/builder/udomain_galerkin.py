"""BUILDER independent cross-check (kappa-certify lens).  conjecture1_proved = False.

Galerkin matrices of the window Weil form Q on L^2[-a, a] in the u-DOMAIN (no digamma, no Bessel functions),
Legendre basis, python-flint Arb balls for the arithmetic + composite Gauss-Legendre for the one archimedean
integral (quadrature error NOT bounded rigorously: this is a numerical falsification test, not a certificate).

For real f supported in [-a, a], g(u) = int f(v + u) f(v) dv (autocorrelation, g(0) = ||f||^2), Weil's
explicit formula (arithmetic side) reads

  Q(f) = 2 F(i/2) F(-i/2) + (-gamma - log pi) g(0) - g(0) log(1 - e^{-4a})
         + int_0^{2a} 2 (e^{-2u} g(0) - e^{-u/2} g(u)) / (1 - e^{-2u}) du
         - sum_{n < e^{2a}} 2 Lambda(n) n^{-1/2} g(log n),

(obtained from psi(z) = -gamma + int_0^inf (e^{-x} - e^{-zx})/(1 - e^{-x}) dx at z = 1/4 + it/2, x = 2u).
For Davenport-Heilbronn D: e^{-u/2} -> e^{-3u/2}, -log pi -> +log(5/pi), no pole term, Lambda -> Lambda_D.

Rayleigh-Ritz: lam_min(Q_N) >= lam*(Q) = inf Q(f)/||f||^2 for every N.  So if lam_min(Q_N) ever fell below a
certified LOWER bound, that certificate would be refuted.  Compared against the idea's certified intervals.
"""
import sys, time, json, math
import flint
from flint import arb, arb_mat

_GL = {}


def gl(n):
    if n not in _GL:
        _GL[n] = [arb.legendre_p_root(n, k, weight=True) for k in range(n)]
    return _GL[n]


def legendre_all(x, nmax):
    P = [arb(1), x]
    for n in range(1, nmax):
        P.append(((2 * n + 1) * x * P[n] - n * P[n - 1]) / (n + 1))
    return P[:nmax + 1]


def prime_powers(xmax):
    out = []
    for n in range(2, int(xmax) + 1):
        m, p = n, None
        for q in range(2, n + 1):
            if m % q == 0:
                p = q
                break
        while m % p == 0:
            m //= p
        if m == 1:
            out.append((n, p))
    return out


def lambda_dh_own(nmax):
    """Lambda_D(n) from -D'/D = sum Lambda_D(n) n^{-s}, D = sum a_n n^{-s}, a periodic mod 5 (1, k, -k, -1, 0)."""
    s5 = arb(5).sqrt()
    kap = ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)
    a = [arb(0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        a[n] = {1: arb(1), 2: kap, 3: -kap, 4: arb(-1), 0: arb(0)}[n % 5]
    L = [arb(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = a[n] * arb(n).log()
        for d in range(1, n):
            if n % d == 0 and d >= 2:
                acc -= L[d] * a[n // d]
        L[n] = acc
    return L


class UForm:
    def __init__(self, a, kind='zeta'):
        self.a = a
        self.kind = kind
        two_a = 2 * a
        xmax = float(two_a.exp().upper())
        self.comb = []
        if kind == 'zeta':
            for (n, p) in prime_powers(xmax):
                ln = arb(n).log()
                if ln < two_a:
                    self.comb.append((2 * arb(p).log() / arb(n).sqrt(), ln, n))
                elif not (ln > two_a):
                    raise ValueError('straddle')
            self.decay = arb(1) / 2
            self.c0 = -arb.const_euler() - arb.pi().log()
        else:
            LD = lambda_dh_own(int(xmax) + 1)
            for n in range(2, int(xmax) + 1):
                ln = arb(n).log()
                if ln < two_a and not LD[n].is_zero():
                    self.comb.append((2 * LD[n] / arb(n).sqrt(), ln, n))
            self.decay = arb(3) / 2
            self.c0 = -arb.const_euler() + (arb(5) / arb.pi()).log()
        self.c0 = self.c0 - (1 - (-4 * a).exp()).log()

    def phis(self, u, degs):
        """phi_d(u) = sqrt((2d+1)/(2a)) P_d(u/a) for d in degs (u inside [-a, a])."""
        P = legendre_all(u / self.a, degs[-1])
        return [(arb(2 * d + 1) / (2 * self.a)).sqrt() * P[d] for d in degs]

    def Gsym(self, u, degs, nin):
        """symmetrised autocorrelation matrix G_mn(u) = (g_mn(u) + g_nm(u))/2, g_mn(u) = int phi_m(v+u) phi_n(v) dv,
        exact (polynomial integrand) by nin-point Gauss-Legendre on [-a, a-u]."""
        a = self.a
        lo, hi = -a, a - u
        c, h = (lo + hi) / 2, (hi - lo) / 2
        rows1, rows2 = [], []
        for (r, w) in gl(nin):
            v = c + h * r
            p1 = self.phis(v + u, degs)
            p2 = self.phis(v, degs)
            rows1.append(p1)
            rows2.append([h * w * t for t in p2])
        A1 = arb_mat(rows1).transpose()      # N x nin
        A2 = arb_mat(rows2)                  # nin x N
        G = A1 * A2
        N = len(degs)
        return arb_mat([[(G[i, k] + G[k, i]) / 2 for k in range(N)] for i in range(N)])

    def matrix(self, sector, N, panels=8, mpan=None, verbose=False):
        degs = [2 * k for k in range(N)] if sector == 'even' else [2 * k + 1 for k in range(N)]
        maxdeg = degs[-1]
        nin = maxdeg + 2
        if mpan is None:
            mpan = maxdeg + 40
        a = self.a
        t0 = time.time()
        Arch = arb_mat(N, N)
        width = 2 * a / panels
        for pnl in range(panels):
            lo = width * pnl
            c, h = lo + width / 2, width / 2
            for (r, w) in gl(mpan):
                u = c + h * r
                G = self.Gsym(u, degs, nin)
                e2 = (-2 * u).exp()
                ed = (-self.decay * u).exp()
                den = 1 - e2
                fac = h * w * 2 / den
                for i in range(N):
                    for k in range(N):
                        v = -ed * G[i, k]
                        if i == k:
                            v += e2
                        Arch[i, k] += fac * v
        Prime = arb_mat(N, N)
        for (cn, ln, n) in self.comb:
            G = self.Gsym(ln, degs, nin)
            for i in range(N):
                for k in range(N):
                    Prime[i, k] += cn * G[i, k]
        Pole = arb_mat(N, N)
        if self.kind == 'zeta':
            vm, vp = [arb(0)] * N, [arb(0)] * N
            for (r, w) in gl(maxdeg + 60):
                u = a * r
                ph = self.phis(u, degs)
                em, ep = (-u / 2).exp(), (u / 2).exp()
                for i in range(N):
                    vm[i] += a * w * ph[i] * em
                    vp[i] += a * w * ph[i] * ep
            for i in range(N):
                for k in range(N):
                    Pole[i, k] = vm[i] * vp[k] + vm[k] * vp[i]
        Q = arb_mat(N, N)
        for i in range(N):
            for k in range(N):
                Q[i, k] = Pole[i, k] + Arch[i, k] - Prime[i, k] + (self.c0 if i == k else 0)
        if verbose:
            print('   built %s N=%d panels=%d m=%d nin=%d (%.1fs)' % (sector, N, panels, mpan, nin, time.time() - t0),
                  flush=True)
        return Q


def lam_min(Q, dps=None):
    import mpmath
    N = Q.nrows()
    old = mpmath.mp.dps
    mpmath.mp.dps = dps or max(60, int(flint.ctx.prec * 0.30) - 10)
    try:
        M = mpmath.matrix(N, N)
        for i in range(N):
            for k in range(N):
                M[i, k] = mpmath.mpf(Q[i, k].mid().str(mpmath.mp.dps + 5, radius=False))
        E, V = mpmath.eigsy(M)
        ev = sorted(E)
        maxrad = max(float(Q[i, k].rad()) for i in range(N) for k in range(N))
        return ev, maxrad
    finally:
        mpmath.mp.dps = old


if __name__ == '__main__':
    flint.ctx.prec = int(sys.argv[5]) if len(sys.argv) > 5 else 512
    p, q = sys.argv[1].split('/')
    a = arb(int(p)) / int(q)
    kind = sys.argv[2]
    sector = sys.argv[3]
    Ns = [int(t) for t in sys.argv[4].split(',')]
    panels = int(sys.argv[6]) if len(sys.argv) > 6 else 8
    uf = UForm(a, kind)
    print('a=%s x=e^{2a}=%s kind=%s comb=%s' % (sys.argv[1], (2 * a).exp().str(8), kind,
                                                [n for (_, _, n) in uf.comb]), flush=True)
    res = []
    for N in Ns:
        Q = uf.matrix(sector, N, panels=panels, verbose=True)
        ev, mr = lam_min(Q)
        print('  %s N=%3d  lam_min(Q_N) = %s   next = %s   max entry radius %.1e' % (
            sector, N, '%.10e' % float(ev[0]), '%.4e' % float(ev[1]), mr), flush=True)
        res.append(dict(N=N, lam_min=str(ev[0]), lam_2=str(ev[1]), maxrad=mr))
    tag = sys.argv[7] if len(sys.argv) > 7 else None
    if tag:
        json.dump(dict(a=sys.argv[1], kind=kind, sector=sector, prec=flint.ctx.prec, panels=panels, results=res),
                  open(tag, 'w'), indent=1)

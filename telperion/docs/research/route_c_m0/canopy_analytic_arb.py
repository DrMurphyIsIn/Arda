"""Certified analytic canopy bounds (P15 sections 8.3, 8.5; Lemmas 8.2, 8.5), generalised to
arbitrary (t0, y0), in Arb ball arithmetic.  See README.md section 3 for the derivation.

Region handled here: R_big = [x_left, x_{N1+1}] x [y0, 1] by the argument principle for the single
holomorphic function E(z) H_t(z)/B_t(z), E = prod_{p in P} (1 - b_p p^{-s_*}) (one fixed mollifier),
plus the tail x >= x_{N1+1} pointwise.  Edges:
  * bottom (y = y0) and top (y = 1): P15 Lemma 8.5 per N-interval [N-, N+]      -> edge_interval()
  * right edge and the tail N >= N1+1: crude triangle inequality, uniform in y  -> crude_interval()
  * left edge x = x_left: numerical boxes (canopy_mesh.py)
All returned margins are rigorous lower bounds (Arb); a positive margin certifies the piece.
"""
import math

from flint import arb, ctx

PI = arb.pi


def xN(N, t):
    return 4 * PI() * N * N - PI() * t / 4


def sigma_low(N, y, t):
    """Lower bound for Re s_* on the N-segment at height >= y (P15 (21) at x = x_N)."""
    x = xN(N, t)
    corr = (1 - 3 * y + 4 * y * (1 + y) / (x * x)).upper()
    corr_plus = corr if float(corr) > 0 else arb(0)
    return ((1 + y) / 2 + (t / 4) * (x / (4 * PI())).log() - (t / (2 * x * x)) * corr_plus).lower()


def g_up(N, y, t):
    """Upper bound for |gamma| on the N-segment at height y (P15 (20) at x = x_N)."""
    return ((arb('0.02') * y).exp() * (xN(N, t) / (4 * PI())) ** (-y / 2)).upper()


def c_gamma(N, t):
    """|gamma| n^y <= c_gamma (n/N)^{y0} for all y in [y0, 1], n <= N, x in the N-segment."""
    return ((arb('0.02')).exp() * (1 - t / (16 * arb(N) ** 2)) ** (-arb(1) / 2)).upper()


class Bn:
    """b_n = exp((t/4) log^2 n) and log n, n = 1..M (Arb), grown on demand."""

    def __init__(self, t):
        self.t = arb(t)
        self.ln = [None, arb(0)]
        self.b = [None, arb(1)]

    def upto(self, M):
        for n in range(len(self.ln), M + 1):
            l = arb(n).log()
            self.ln.append(l)
            self.b.append(((self.t / 4) * l * l).exp())


def F_sum(B, N, sigma, extra=0, N0cap=6000):
    """Upper bound for sum_{n<=N} n^extra b_n n^{-sigma} (Lemma 8.2 tail beyond N0cap)."""
    t = B.t
    NN = min(N, N0cap)
    B.upto(NN)
    s = arb(0)
    ex = arb(extra)
    for n in range(1, NN + 1):
        s += B.b[n] * ((ex - sigma) * B.ln[n]).exp()
    if N > NN:
        se = sigma - ex
        if not float((se - (t / 2) * arb(N).log()).lower()) > 0:
            return None
        lN0, lN = arb(NN).log(), arb(N).log()
        v0 = ((1 - se) * lN0 + (t / 4) * lN0 * lN0).exp()
        v1 = ((1 - se) * lN + (t / 4) * lN * lN).exp()
        s += v0.union(v1).upper() * (lN - lN0)
    return s.upper()


def err_segment(N, y, t, B, N0cap=6000, Np=None):
    """Upper bound for e_A + e_B + e_{C,0} at height y on every N'-segment with N' in [N, Np]
    (default Np = N).
    e_A + e_B <= (e^{delta1} - 1)(1 + c_gamma N'^{|kappa|}) F_{N',t}(sigma)   (P15 (82) with |gamma| n^y <= c_gamma)
    e_{C,0}  <= (x/4pi)^{-(1+y)/4} exp(-(t/16) L^2 + (3|L + i pi/2| + 3.58)/(x - 8.52)) (1 + eps~(s-) + eps~(s+)),
    eps~ from P15 (59) with a >= N, T = x/2.  The x-dependent factors are decreasing in x and are
    evaluated at x = x_N; the Dirichlet sum F runs over n <= Np with sigma = sigma(N) (an upper bound for
    every N' <= Np); N'^{|kappa|} <= Np^{|kappa(x_N)|}."""
    if Np is None:
        Np = N
    x = xN(N, t)
    L = (x / (4 * PI())).log()
    d1 = ((t * t / 16) * L * L + arb('0.626')) / (x - arb('6.66'))
    sig = sigma_low(N, y, t)
    kap = t * y / (2 * (x - 6))
    F = F_sum(B, Np, sig, 0, N0cap)
    if F is None:
        return None
    eAB = d1.expm1() * (1 + c_gamma(N, t) * arb(Np) ** kap) * F
    absLi = (L * L + PI() ** 2 / 4).sqrt()
    common = (x / (4 * PI())) ** (-(1 + y) / 4) * (-(t / 16) * L * L + (3 * absLi + arb('3.58')) / (x - arb('8.52'))).exp()
    T = x / 2
    et = arb(0)
    for sg in (1, -1):
        et += (arb('0.397') * 3 * arb(3) ** (sg * y) / (arb(N) - arb('0.865')) + arb(5) / (3 * (T - 6))) * (arb('3.49') / (T - 4)).exp()
    return (eAB + common * (1 + et)).upper()


def mollifier(t, primes):
    ds, lam = [1], [arb(1)]
    for p in primes:
        lp = arb(p).log()
        bp = ((t / 4) * lp * lp).exp()
        ds = ds + [d * p for d in ds]
        lam = lam + [-l * bp for l in lam]
    return ds, lam


def edge_interval(Nm, Np, y, t, primes, B, N0cap=6000):
    """Rigorous lower bound, valid for every N in [Nm, Np] and every x in those N-segments, of
        dist(E(z) H_t(z)/B_t(z), (-inf, 0])  on the edge Im z = y,
    via P15 Lemma 8.5 (see README section 3.2 for the interval/truncation handling).  Returns dict."""
    t = arb(t)
    y = arb(y)
    D = 1
    for p in primes:
        D *= p
    M = D * Np
    B.upto(max(Np, 2))
    ds, lam = mollifier(t, primes)
    sig = sigma_low(Nm, y, t)
    g = g_up(Nm, y, t)
    c = (1 - g) / (1 + g)
    # coefficients truncated at Nm (always present for N >= Nm), and the "maybe" part for m in (Nm, Np]
    beta = {}
    alph = {}
    vpart = {}
    for d, l in zip(ds, lam):
        for m in range(1, Np + 1):
            n = d * m
            bm = B.b[m]
            am = bm * (y * B.ln[m]).exp()
            if m <= Nm:
                beta[n] = beta.get(n, arb(0)) + l * bm
                alph[n] = alph.get(n, arb(0)) + l * am
            else:
                vpart[n] = vpart.get(n, arb(0)) + abs(l) * (bm + g * am)
    Y = arb(0)
    keys = set(beta) | set(vpart)
    for n in keys:
        if n < 2:
            continue
        b_ = beta.get(n, arb(0))
        a_ = alph.get(n, arb(0))
        term = _max_up(abs(b_ - g * a_), c * abs(b_ + g * a_)) + vpart.get(n, arb(0))
        Y += term * (-sig * arb(n).log()).exp()
    Emax = arb(1)
    for p in primes:
        lp = arb(p).log()
        Emax *= 1 + ((t / 4) * lp * lp).exp() * (-sig * lp).exp()
    x = xN(Nm, t)
    kap = t * y / (2 * (x - 6))
    Z = arb(0)
    for m in range(1, Np + 1):
        Z += B.b[m] * ((y - sig) * B.ln[m]).exp() * (kap * B.ln[m]).expm1()
    Z = g * Z
    err = err_segment(Nm, y, t, B, N0cap, Np=Np)
    margin = 1 - g - Y - Emax * (Z + err)
    return dict(Nm=Nm, Np=Np, y=float(y.mid()), sigma=float(sig.mid()), g=float(g.mid()),
                Y=float(Y.upper()), Emax=float(Emax.upper()), Z=float(Z.upper()), err=float(err),
                margin=float(margin.lower()), terms=len(keys))


def _max_up(a, b):
    """Upper bound of max(a, b) for nonnegative arb balls."""
    au, bu = a.upper(), b.upper()
    return au if float(au) >= float(bu) else bu


def crude_interval(Na, Nb, y0, t, primes, B, N0cap=6000):
    """For every N in [Na, Nb] and every y in [y0, 1] on those segments:
        |H/B - 1| <= rho := (F(sigma) - 1) + c_gamma N^{-y0} F_{y0}(sigma - |kappa|) + err,
    returned as an upper bound rho_up (valid uniformly).  The piece is certified (zero-free, and the
    right edge of R_big avoids (-inf,0] after multiplying by E) iff rho_up < 1 and
    arcsin(rho_up) + sum_p arcsin(b_p p^{-sigma}) < pi."""
    t = arb(t)
    y0 = arb(y0)
    sig = sigma_low(Na, y0, t)
    xa = xN(Na, t)
    kap = t * 1 / (2 * (xa - 6))
    # F(sigma) over N in [Na, Nb]: sums over n <= N are increasing in N, so bound with N = Nb and sigma(Na)
    F1 = F_sum(B, Nb, sig, 0, N0cap)
    F2 = F_sum(B, Nb, sig - kap, y0, N0cap)
    if F1 is None or F2 is None:
        return dict(Na=Na, Nb=Nb, rho=float('inf'), ok=False)
    cg = c_gamma(Na, t)
    err_lo = err_segment(Na, y0, t, B, N0cap, Np=Nb)
    err_hi = err_segment(Na, arb(1), t, B, N0cap, Np=Nb)
    if err_lo is None or err_hi is None:
        return dict(Na=Na, Nb=Nb, rho=float('inf'), ok=False)
    # err(y) = eAB(y) + C(y) with eAB decreasing in y and C log-convex in y, so for y in [y0, 1]:
    # err(y) <= eAB(y0) + max(C(y0), C(1)) <= err(y0) + err(1)   (conservative sum)
    err = (err_lo + err_hi).upper()
    rho = (F1 - 1) + cg * arb(Na) ** (-y0) * F2 + err
    ang = arb(0)
    for p in primes:
        lp = arb(p).log()
        ang += (((t / 4) * lp * lp).exp() * (-sig * lp).exp()).asin()
    rho_u = rho.upper()
    ok = float(rho_u) < 1 and float((rho_u.asin() + ang).upper()) < math.pi
    return dict(Na=Na, Nb=Nb, rho=float(rho_u), ok=ok, sigma=float(sig.mid()), err=float(err))


def crude_far(Nstart, y0, t, factor=2.0, Nlimit=10 ** 60, N0cap=6000, primes=(2, 3, 5, 7)):
    """Cover [Nstart, Nlimit] by geometric intervals with crude_interval, then N >= Nlimit by the
    trivial bound (README 3.3).  Returns (ok, list_of_pieces, worst_rho)."""
    B = Bn(t)
    pieces = []
    Na = Nstart
    worst = 0.0
    while Na < Nlimit:
        Nb = min(int(Na * factor) + 1, Nlimit)
        r = crude_interval(Na, Nb, y0, t, primes, B, N0cap)
        pieces.append(r)
        worst = max(worst, r['rho'])
        if not r['ok']:
            return False, pieces, worst
        Na = Nb + 1
    # N >= Nlimit: b_n <= n^{(t/4) log N} for n <= N, so sum_{2<=n<=N} b_n n^{-sigma} <= zeta(s2) - 1 with
    # s2 = sigma - (t/4) log N >= (1+y0)/2 + (t/4) log(x_N/4pi) - (t/4) log N - tiny >= (t/4) log N (x_N/4pi ~ N^2)
    # and similarly for the gamma-sum with exponent s2 - y0 - |kappa|; for N >= 1e60 and t >= 0.1 both
    # exponents exceed (0.1/4)*138 - 1 > 2.4, giving rho <= 2 (zeta(2.4)-1) + err < 0.9.
    t_ = arb(t)
    s2 = (t_ / 4) * arb(Nlimit).log() - 1
    if float(s2.lower()) < 2.4:
        return False, pieces, worst
    return True, pieces, worst


def far_bound(Nlimit, y0, t, primes):
    """Uniform bound for all N >= Nlimit and y in [y0, 1] (README 3.3):
        rho <= (zeta(q) - 1) + c_gamma (N^{-y0} + zeta(q - |kappa|) - 1) + err,
    q = (1+y0)/2 + (t/4) log(x_N/4pi) - (t/4) log N - corr >= (1+y0)/2 + (t/4) log N - 1e-9, using
    b_n <= n^{(t/4) log N} for n <= N.  Every ingredient is decreasing in N, so evaluating at Nlimit
    bounds all N >= Nlimit.  err: (e^{delta1}-1)(1 + c_gamma N^{|kappa|}) zeta(q) + e_C0-bound."""
    t = arb(t)
    y0 = arb(y0)
    N = arb(Nlimit)
    x = xN(Nlimit, t)
    sig = sigma_low(Nlimit, y0, t)
    q = (sig - (t / 4) * N.log()).lower()
    kap = t / (2 * (x - 6))
    zq = q.zeta()
    cg = c_gamma(Nlimit, t)
    L = (x / (4 * PI())).log()
    d1 = ((t * t / 16) * L * L + arb('0.626')) / (x - arb('6.66'))
    eAB = d1.expm1() * (1 + cg * N ** kap) * zq
    absLi = (L * L + PI() ** 2 / 4).sqrt()
    errC = arb(0)
    for y in (y0, arb(1)):
        common = (x / (4 * PI())) ** (-(1 + y) / 4) * (-(t / 16) * L * L + (3 * absLi + arb('3.58')) / (x - arb('8.52'))).exp()
        T = x / 2
        et = arb(0)
        for sg in (1, -1):
            et += (arb('0.397') * 3 * arb(3) ** (sg * y) / (N - arb('0.865')) + arb(5) / (3 * (T - 6))) * (arb('3.49') / (T - 4)).exp()
        errC = errC.union(common * (1 + et))
    rho = (zq - 1) + cg * (N ** (-y0) + (q - kap).zeta() - 1) + eAB + errC.upper()
    ang = arb(0)
    for p in primes:
        lp = arb(p).log()
        ang += (((t / 4) * lp * lp).exp() * (-sig * lp).exp()).asin()
    rho_u = rho.upper()
    ok = float(rho_u) < 1 and float((rho_u.asin() + ang).upper()) < math.pi
    return dict(Nlimit=Nlimit, rho=float(rho_u), q=float(q), ok=ok)


def analytic_certificate(t0, y0, primes, N_scan=(60, 700), grow=1.15, N_single=80, crude_start=None,
                         Nlimit=10 ** 40, log=print):
    """Find the smallest N_s such that every N >= N_s is covered: bottom and top edges by Lemma 8.5
    (single-N for the first N_single values after N_s, then geometric intervals) up to N1, and the crude
    bound from N1 on (geometric intervals to Nlimit, then far_bound).  Returns a certificate dict."""
    t = arb(t0)
    B = Bn(t)
    lo, hi = N_scan
    single = {}
    for N in range(lo, hi + 1):
        single[N] = edge_interval(N, N, arb(y0), t, primes, B)['margin']
    bad = [N for N in single if single[N] <= 0]
    Ns = (max(bad) + 1) if bad else lo
    log(f'  [analytic] single-N bottom-edge scan {lo}..{hi}: last failing N = {max(bad) if bad else None} -> N_s = {Ns}')
    cert = dict(t0=t0, y0=y0, primes=list(primes), N_s=Ns, bottom=[], top=[], crude=[], ok=True)
    # crude start: smallest N (on a 1.1-geometric grid) from which crude intervals succeed
    N1 = crude_start
    if N1 is None:
        N = max(Ns, 100)
        while True:
            r = crude_interval(N, int(N * 1.1) + 1, y0, t, primes, B)
            if r['ok']:
                N1 = N
                break
            N = int(N * 1.1) + 1
            if N > 10 ** 7:
                cert['ok'] = False
                return cert
    cert['N1'] = N1
    # bottom and top edges on [Ns, N1]
    for (edge_y, key) in ((arb(y0), 'bottom'), (arb(1), 'top')):
        N = Ns
        while N <= N1:
            if N - Ns < N_single:
                Np = N
            else:
                Np = min(N1, max(N, int(N * grow)))
            r = edge_interval(N, Np, edge_y, t, primes, B)
            while r['margin'] <= 0 and Np > N:
                Np = N + (Np - N) // 2
                r = edge_interval(N, Np, edge_y, t, primes, B)
            cert[key].append(r)
            if r['margin'] <= 0:
                cert['ok'] = False
                log(f'  [analytic] {key} edge FAILS at N={N}: margin {r["margin"]}')
                return cert
            N = Np + 1
    # crude from N1 to Nlimit, then far bound
    N = N1
    fac = 1.1
    while N < Nlimit:
        Nb = min(int(N * fac) + 1, Nlimit)
        r = crude_interval(N, Nb, y0, t, primes, B)
        if not r['ok'] and fac > 1.02:
            fac = max(1.02, fac / 1.5)
            continue
        cert['crude'].append(r)
        if not r['ok']:
            cert['ok'] = False
            log(f'  [analytic] crude FAILS on [{N},{Nb}] rho={r["rho"]}')
            return cert
        N = Nb + 1
        fac = min(2.0, fac * 1.15)
    fb = far_bound(Nlimit, y0, t0, primes)
    cert['far'] = fb
    cert['ok'] = cert['ok'] and fb['ok']
    cert['min_bottom_margin'] = min(r['margin'] for r in cert['bottom'])
    cert['min_top_margin'] = min(r['margin'] for r in cert['top'])
    cert['max_crude_rho'] = max(r['rho'] for r in cert['crude'])
    cert['edge_terms'] = sum(r['terms'] for r in cert['bottom'] + cert['top'])
    return cert

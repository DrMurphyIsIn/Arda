"""Lane B rigorous core: the same window Weil form as bcore.py, evaluated in mpmath.iv interval
arithmetic (ctx = mp.iv) or plain high precision (ctx = mp.mp).  Every transcendental input is either
an mpmath.iv primitive (exp, log, cos, sin, atan, sqrt, pi, euler-free) or the complex digamma /
trigamma below, whose truncation error is enclosed by an explicit bound.

Digamma (Re w > 0):   psi(w)  = log w - 1/(2w) - sum_{k=1}^{K-1} B_2k/(2k w^2k) + R,  |R| <= |B_2K|/(2K (Re w)^2K)
Trigamma (Re w > 0):  psi'(w) = 1/w + 1/(2w^2) + sum_{k=1}^{K-1} B_2k / w^(2k+1)   + R', |R'| <= |B_2K|/(Re w)^(2K+1)
  (from psi(w) = log w - 1/(2w) - int_0^inf phi(t) e^{-wt} dt, phi(t) = 1/(e^t-1) - 1/t + 1/2, and the
   classical fact that for real t > 0 the Taylor remainder of phi after k terms has the sign of, and is
   bounded by, the next term B_2(k+1) t^(2k+1)/(2k+2)!  -- partial fractions phi(t) = sum_j 2t/(t^2+4 pi^2 j^2).)
  The argument is first shifted by recurrence psi(z) = psi(z+n) - sum_{k<n} 1/(z+k) to Re w >= 24.
Tail of the beta_j = beta0 + 2j families (j >= J): enclosed by geometric bounds (see Form.__init__)."""
import mpmath as mp
from fractions import Fraction as Fr

BERN = [Fr(1, 6), Fr(-1, 30), Fr(1, 42), Fr(-1, 30), Fr(5, 66), Fr(-691, 2730), Fr(7, 6), Fr(-3617, 510),
        Fr(43867, 798), Fr(-174611, 330), Fr(854513, 138), Fr(-236364091, 2730)]   # B_2 .. B_24

class Ctx:
    def __init__(self, rigorous, dps):
        self.rig = rigorous
        self.m = mp.iv if rigorous else mp.mp
        self.m.dps = dps
        mp.mp.dps = dps
    def c(self, v):  # exact constant -> number
        if isinstance(v, Fr):
            return self.m.mpf(v.numerator) / self.m.mpf(v.denominator)
        if isinstance(v, str):
            return self.m.mpf(v)
        return self.m.mpf(v)
    def ball(self, r):  # [-r, r]
        if self.rig:
            r = mp.mpf(r)
            return self.m.mpf([-r, r])
        return self.m.mpf(0)
    def upper(self, x):
        return mp.mpf(x.b) if self.rig else mp.mpf(x)
    def lower(self, x):
        return mp.mpf(x.a) if self.rig else mp.mpf(x)

class C:
    __slots__ = ('re', 'im')
    def __init__(self, re, im):
        self.re = re; self.im = im
    def __add__(s, o):
        if isinstance(o, C): return C(s.re + o.re, s.im + o.im)
        return C(s.re + o, s.im)
    __radd__ = __add__
    def __sub__(s, o):
        if isinstance(o, C): return C(s.re - o.re, s.im - o.im)
        return C(s.re - o, s.im)
    def __rsub__(s, o):
        return C(o - s.re, -s.im)
    def __neg__(s): return C(-s.re, -s.im)
    def __mul__(s, o):
        if isinstance(o, C): return C(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
        return C(s.re * o, s.im * o)
    __rmul__ = __mul__
    def conj(s): return C(s.re, -s.im)
    def abs2(s): return s.re * s.re + s.im * s.im
    def inv(s):
        d = s.abs2(); return C(s.re / d, -s.im / d)
    def __truediv__(s, o):
        if isinstance(o, C): return s * o.inv()
        return C(s.re / o, s.im / o)
    def __rtruediv__(s, o): return s.inv() * o

def cexp(X, z):
    e = X.m.exp(z.re); return C(e * X.m.cos(z.im), e * X.m.sin(z.im))
def cexpi(X, t):  # e^{i t}, t real
    return C(X.m.cos(t), X.m.sin(t))
def clog(X, w):  # Re w > 0
    return C(X.m.log(w.abs2()) / 2, X.m.atan2(w.im, w.re))
def csin(X, z):
    ep = X.m.exp(z.im); em = X.m.exp(-z.im)
    return C(X.m.sin(z.re) * (ep + em) / 2, X.m.cos(z.re) * (ep - em) / 2)

def _shift(X, z, R0=24):
    if X.m.dps > 40: R0 = 400
    lo = X.lower(z.re)
    n = max(0, int(mp.ceil(R0 - lo)))
    return n

def cdigamma(X, z, K=12):
    n = _shift(X, z)
    acc = C(X.c(0), X.c(0))
    w = z
    for k in range(n):
        acc = acc - w.inv(); w = w + X.c(1)
    s = clog(X, w) - (w.inv() * X.c(Fr(1, 2)))
    w2 = w * w; p = w2
    for k in range(1, K):
        s = s - p.inv() * X.c(BERN[k - 1] / (2 * k)); p = p * w2
    rw = X.lower(w.re); assert rw >= 24
    r = abs(mp.mpf(BERN[K - 1].numerator) / BERN[K - 1].denominator) / (2 * K) / rw ** (2 * K) * (1 + mp.mpf(10) ** -10)
    return C(s.re + X.ball(r), s.im + X.ball(r)) + acc

def ctrigamma(X, z, K=12):
    n = _shift(X, z)
    acc = C(X.c(0), X.c(0)); w = z
    for k in range(n):
        acc = acc + (w * w).inv(); w = w + X.c(1)
    wi = w.inv(); s = wi + (wi * wi) * X.c(Fr(1, 2))
    w2 = w * w; p = w2 * w
    for k in range(1, K):
        s = s + p.inv() * X.c(BERN[k - 1]); p = p * w2
    rw = X.lower(w.re); assert rw >= 24
    r = abs(mp.mpf(BERN[K - 1].numerator) / BERN[K - 1].denominator) / rw ** (2 * K + 1) * (1 + mp.mpf(10) ** -10)
    return C(s.re + X.ball(r), s.im + X.ball(r)) + acc

# ---------------- arithmetic data (exact) ----------------
def chi_m4(n):
    r = n % 4
    return 0 if r % 2 == 0 else (1 if r == 1 else -1)
def leg5(n): return {0: 0, 1: 1, 4: 1, 2: -1, 3: -1}[n % 5]
def chi_m20(n): return chi_m4(n) * leg5(n)
def ppow(n):
    for q in range(2, n + 1):
        if n % q == 0:
            m = n
            while m % q == 0: m //= q
            return q if m == 1 else 0
    return 0

def weights(X, kind, nmax):
    """w(n) for 2 <= n <= nmax, as numbers in ctx X (log n enclosed by iv.log)."""
    out = {}
    if kind in ('zeta', 'ZK'):
        for n in range(2, nmax + 1):
            p = ppow(n)
            if p:
                mult = 1 if kind == 'zeta' else 1 + chi_m20(n)
                if mult: out[n] = X.c(mult) * X.m.log(X.c(p))
        return out
    # E: exact a(n) (rational), c(n) = sum_p r_{n,p} log p with rational r (recursion done symbolically)
    a = {}
    for n in range(1, nmax + 1):
        s = sum(chi_m20(d) + chi_m4(d) * leg5(n // d) for d in range(1, n + 1) if n % d == 0)
        a[n] = Fr(s, 2)
    assert a[1] == 1
    primes = [p for p in range(2, nmax + 1) if all(p % q for q in range(2, p))]
    def logvec(n):
        v = {}
        for p in primes:
            while n % p == 0: v[p] = v.get(p, 0) + 1; n //= p
        return v
    c = {}
    for n in range(2, nmax + 1):
        acc = {p: a[n] * e for p, e in logvec(n).items()}   # a(n) log n
        for d in range(2, n):
            if n % d == 0:
                for p, r in c[d].items():
                    acc[p] = acc.get(p, 0) - r * a[n // d]
        c[n] = {p: r for p, r in acc.items() if r != 0}
    for n in range(2, nmax + 1):
        if c[n]:
            out[n] = sum((X.c(r) * X.m.log(X.c(p)) for p, r in c[n].items()), X.c(0))
    return out, c

def families(X, kind):
    pi = X.m.pi
    if kind == 'zeta':
        return [(X.c(Fr(1, 2)), -X.m.log(pi))]
    return [(X.c(Fr(1, 2)), -X.m.log(pi)), (X.c(Fr(3, 2)), X.m.log(X.c(20) / pi))]

class Form:
    """A given exactly as log(x)/2 with x rational (ctx number)."""
    def __init__(self, X, x, kind):
        self.X = X; m = X.m
        xq = Fr(x).limit_denominator(10**6); assert xq == Fr(x)
        self.xq = xq
        self.A = m.log(X.c(xq)) / 2; self.a = 2 * self.A
        nmax = int(xq) if xq.denominator != 1 else int(xq) - 1   # n < x strictly
        self.nmax = nmax
        w = weights(X, kind, nmax)
        if kind == 'E': w, self.cE = w
        self.pr = [(n, w[n] / m.sqrt(X.c(n)), m.log(X.c(n))) for n in sorted(w)]
        self.fams = []
        for b0, c0 in families(X, kind):
            J = 30
            betas = [b0 + 2 * j for j in range(J)]
            bJ = b0 + 2 * J
            q = 1 / (1 - m.exp(-2 * self.a))
            tailI = 4 * m.exp(-bJ * self.a) / bJ * q            # |sum_{j>=J} 2[e^{-b a}/b - e^{-(b-il)a}/(b-il)]|
            tailCu = 2 * m.exp(-bJ * self.a) * (self.a / bJ + 1 / (bJ * bJ)) * q
            tailCL = 2 * m.exp(-bJ * self.a) / bJ * q            # in [0, tailCL]
            if X.rig:
                tI = X.ball(X.upper(tailI)); tC = X.ball(X.upper(tailCu)); tL = m.mpf([0, X.upper(tailCL)])
            else:
                tI = tC = tL = X.c(0)
            psih = cdigamma(X, C(b0 / 2, X.c(0))).re
            CL = c0 + psih + sum((2 * m.exp(-b * self.a) / b for b in betas), X.c(0)) + tL
            self.fams.append((b0, betas, CL, psih, tI, tC))
        self.CL = sum((f[2] for f in self.fams), X.c(0))

    def I(self, lam):
        X = self.X; m = X.m; tot = C(X.c(0), X.c(0))
        for b0, betas, CL, psih, tI, tC in self.fams:
            v = cdigamma(X, C(b0 / 2, -lam / 2)) - psih
            for b in betas:
                z = C(b, -lam)
                v = v - (2 * m.exp(-b * self.a) / b) + 2 * cexp(X, C(-z.re * self.a, -z.im * self.a)) / z
            tot = tot + v + C(tI, tI)
        return tot

    def Cu(self, k):
        X = self.X; m = X.m; tot = X.c(0)
        for b0, betas, CL, psih, tI, tC in self.fams:
            v = ctrigamma(X, C(b0 / 2, k / 2)).re / 2
            for b in betas:
                z = C(b, -k)
                e = cexp(X, C(-z.re * self.a, -z.im * self.a))
                v = v - 2 * (e * (z.inv() * self.a + (z * z).inv())).re
            tot = tot + v + tC
        return tot

def sector_freqs(X, A, N, par, basis='neumann'):
    pi = X.m.pi
    if basis == 'neumann':
        return [pi * m / A for m in range(N)] if par == 0 else [pi * (X.c(m) + X.c(Fr(1, 2))) / A for m in range(N)]
    return [pi * (X.c(m) + X.c(Fr(1, 2))) / A for m in range(N)] if par == 0 else [pi * (m + 1) / A for m in range(N)]

def build_sector(F, par, N, basis='neumann', progress=False):
    """Real symmetric sector matrices (M, G) (lists of lists of ctx numbers) on
       phi_m = cos(kap_m u) (par 0) / sin(kap_m u) (par 1), m < N."""
    X = F.X; m = X.m; A = F.A
    kap = sector_freqs(X, A, N, par, basis)
    zero_first = (basis == 'neumann' and par == 0)
    ks = kap + [-k for k in kap]           # index i -> +kap_i, N+i -> -kap_i
    K = len(ks)
    eA = [cexpi(X, k * A) for k in ks]
    Ep = [[cexpi(X, k * y) for (_, _, y) in F.pr] for k in ks]
    cs = [c for (_, c, _) in F.pr]; ys = [y for (_, _, y) in F.pr]
    Iv = [F.I(k) for k in ks]
    h = C(X.c(0), X.c(Fr(1, 2)))
    Fh = []
    for k in ks:
        z = C(k, X.c(0)) + h
        Fh.append(csin(X, z * A) * 2 / z)
    CL = F.CL
    def diag(ia):
        k = ks[ia]
        arch = 2 * A * CL + 2 * A * Iv[ia].re + F.Cu(k)
        comb = sum((cs[p] * 2 * (2 * A - ys[p]) * m.cos(k * ys[p]) for p in range(len(cs))), X.c(0))
        pole = 2 * (Fh[ia] * Fh[ia]).re
        return pole + arch - comb, 2 * A
    def off(ia, ib):
        d = ks[ia] - ks[ib]
        e = eA[ia] * eA[ib].conj()          # e^{i d A}
        gram = 2 * e.im / d
        P = e * (Iv[ib] + Iv[ia].conj())      # I(-k_a) = conj I(k_a)
        # P/(2 i d): (x+iy)/(2id) = (y - i x)/(2d) -> Re = y/(2d)
        arch = gram * CL + P.im / d
        comb = X.c(0)
        for p in range(len(cs)):
            U = e * (Ep[ib][p] + Ep[ia][p].conj())
            comb = comb + cs[p] * U.im
        comb = 2 * comb / d
        pole = 2 * (Fh[ia] * Fh[ib]).re
        return pole + arch - comb, gram
    cache = {}
    def ent(ia, ib):
        key = (min(ia, ib), max(ia, ib))
        if key not in cache:
            same = (ia == ib) or (zero_first and {ia, ib} == {0, N})
            cache[key] = diag(ia) if same else off(ia, ib)
        return cache[key]
    sgn = 1 if par == 0 else -1
    Mr = [[None] * N for _ in range(N)]; Gr = [[None] * N for _ in range(N)]
    half = X.c(Fr(1, 2))
    for i in range(N):
        if progress and i % 16 == 0: print('   row', i, flush=True)
        for j in range(i, N):
            m1, g1 = ent(i, j); m2, g2 = ent(i, N + j)
            if zero_first and (i == 0 or j == 0):
                if i == 0 and j == 0:
                    mv, gv = m1, g1
                else:
                    mv, gv = half * (m1 + m2), half * (g1 + g2)
                    # phi_0 = 1 = e_0 (not (e_0+e_-0)/2); B(e_0, cos) = (M[0,+j]+M[0,-j])/2 -- same formula
            else:
                mv, gv = half * (m1 + sgn * m2), half * (g1 + sgn * g2)
            Mr[i][j] = Mr[j][i] = mv; Gr[i][j] = Gr[j][i] = gv
    return Mr, Gr, kap

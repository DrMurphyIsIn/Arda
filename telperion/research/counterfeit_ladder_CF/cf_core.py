"""Lane A (counterfeit ladder) -- independent numerics core.  Written from scratch; shares no code with
the geometry angle's ep_*.py.

Functions (all normalized with a(1) = 1):
  zetaK(s) = zeta(s) L(s, chi_-20)                      K = Q(sqrt -5), h = 2
  G(s)     = L(s, chi_-4) L(s, chi_5)                    genus-character product
  E(s)     = (zetaK + G)/2 = (1/2) sum'_{(x,y) != 0} (x^2 + 5 y^2)^{-s}
Both have the completed form Lam(s) = 20^{s/2} Gamma_R(s) Gamma_R(s+1) F(s) = Lam(1-s),
Gamma_R(s) = pi^{-s/2} Gamma(s/2), Gamma_R(s) Gamma_R(s+1) = Gamma_C(s) = 2 (2 pi)^{-s} Gamma(s).

Weil functional for an even real test v supported in [-A, A] (x = e^{2A}), g = v * v~ :
  Q(v) = POLE + ARCH - PRIME
  POLE  = 2 (int v(u) cosh(u/2) du)^2                          (pole of F at s = 1, and s = 0 of Lam)
  ARCH  = g(0) (log 20 - 2 log pi) + (1/2pi) int |F(r)|^2 [Re psi(1/4 + i r/2) + Re psi(3/4 + i r/2)] dr
  PRIME = sum_{n < x} 2 c(n)/sqrt(n) g(log n),   -F'/F = sum c(n) n^{-s}.
Spatial form of the psi part (independent of the Lorentzian closed forms used in Lean):
  (1/2pi) int |F|^2 [psi_{1/4} + psi_{3/4}] dr = 2 g(0) E1(4A) + int_0^{2A} [2 e^{-2y} g(0)/y - g(y)/sinh(y/2)] dy
(from psi(z) = int_0^inf (e^{-t}/t - e^{-zt}/(1-e^{-t})) dt, t = 2y, and e^{-y/2}+e^{-3y/2} over 1-e^{-2y}).
"""
import mpmath as mp

# ---------------- characters and coefficients ----------------
def chi_m4(n):
    return [0, 1, 0, -1][n % 4]

def chi_5(n):
    return [0, 1, -1, -1, 1][n % 5]

def chi_m20(n):
    # Kronecker (-20/n): 1 on {1,3,7,9} mod 20, -1 on {11,13,17,19}, 0 otherwise
    r = n % 20
    if r in (1, 3, 7, 9):
        return 1
    if r in (11, 13, 17, 19):
        return -1
    return 0

def lattice_aE(n):
    """(1/2) #{(x, y) in Z^2 : x^2 + 5 y^2 = n}, by direct count."""
    if n == 0:
        return 0
    cnt = 0
    y = 0
    while 5 * y * y <= n:
        r = n - 5 * y * y
        x = int(round(r ** 0.5))
        for xx in (x - 1, x, x + 1):
            if xx >= 0 and xx * xx == r:
                mult = (1 if xx == 0 else 2) * (1 if y == 0 else 2)
                cnt += mult
        y += 1
    assert cnt % 2 == 0
    return cnt // 2

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def aK(n):
    return sum(chi_m20(d) for d in divisors(n))

def aG(n):
    return sum(chi_m4(d) * chi_5(n // d) for d in divisors(n))

def mangoldt(n):
    if n < 2:
        return mp.mpf(0)
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return mp.log(p) if m == 1 else mp.mpf(0)

def logderiv_coeffs(a, nmax):
    """c with a(n) log n = sum_{d | n} c(d) a(n/d), a(1) = 1."""
    assert a(1) == 1
    c = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = a(n) * mp.log(n)
        for d in divisors(n):
            if d < n:
                acc -= c[d] * a(n // d)
        c[n] = acc
    return c

def cK_list(nmax):
    return [mp.mpf(0)] + [mangoldt(n) * (1 + chi_m20(n)) for n in range(1, nmax + 1)]

# ---------------- the Dirichlet-cosine basis on [-A, A] ----------------
class Window:
    def __init__(self, A, ks, ss):
        self.A = mp.mpf(A)
        self.ks = [mp.mpf(k) for k in ks]
        self.ss = [mp.mpf(s) for s in ss]   # s_i = sin(k_i A), cos(k_i A) = 0

    def G(self, i, j, y):
        """symmetrized cross-correlation (G_ij(y) + G_ji(y))/2 for 0 <= y <= 2A (closed form)."""
        A = self.A
        ki, kj, si, sj = self.ks[i], self.ks[j], self.ss[i], self.ss[j]
        if i == j:
            return (2 * A - y) * mp.cos(ki * y) / 2 + mp.sin(ki * y) / (2 * ki)
        return si * sj * (ki * mp.sin(kj * y) - kj * mp.sin(ki * y)) / (ki ** 2 - kj ** 2)

    def G_quad(self, i, j, y):
        A = self.A
        f = lambda x: mp.cos(self.ks[i] * x) * mp.cos(self.ks[j] * (x - y))
        h = lambda x: mp.cos(self.ks[j] * x) * mp.cos(self.ks[i] * (x - y))
        return (mp.quad(f, [y - A, A]) + mp.quad(h, [y - A, A])) / 2

    def P(self, i):
        """int_{-A}^{A} cos(k u) cosh(u/2) du."""
        k = self.ks[i]
        return 2 * k * self.ss[i] * mp.cosh(self.A / 2) / (k ** 2 + mp.mpf(1) / 4)

    def F(self, i, z):
        """int_{-A}^{A} cos(k u) cos(z u) du, analytic in z."""
        k, A = self.ks[i], self.A
        if abs(z - k) < mp.mpf(10) ** (-mp.mp.dps // 2):
            return A + mp.sin(2 * k * A) / (2 * k)
        return mp.sin((k - z) * A) / (k - z) + mp.sin((k + z) * A) / (k + z)

def dirichlet_window(q, M, m0=0):
    """A = q pi, modes m = m0..m0+M-1, k_m = (m + 1/2)/q, s_m = (-1)^m."""
    q = mp.mpf(q)
    A = q * mp.pi
    ks = [(m + mp.mpf(1) / 2) / q for m in range(m0, m0 + M)]
    ss = [(-1) ** m for m in range(m0, m0 + M)]
    return Window(A, ks, ss)

def gl_nodes(n, a, b):
    xs, ws = [], []
    # Gauss-Legendre via mpmath
    nodes = mp.calculus.quadrature.GaussLegendre(mp.mp)
    # use mpmath's generic machinery: degree chosen so that 3*2^(deg-1) >= n
    deg = 1
    while 3 * 2 ** (deg - 1) < n:
        deg += 1
    pts = nodes.calc_nodes(deg, mp.mp.prec)
    for (x, w) in pts:
        xs.append((b - a) / 2 * x + (a + b) / 2)
        ws.append((b - a) / 2 * w)
    return xs, ws

def matrices(W, cE, cK, nodes=None):
    """Return dict of M x M matrices: gram (=g(0) entries), pole, arch_psi, arch_const, primeE, primeK."""
    M = len(W.ks)
    A = W.A
    x = mp.e ** (2 * A)
    Nmax = int(mp.floor(x))
    gram = mp.matrix(M, M)
    pole = mp.matrix(M, M)
    psi = mp.matrix(M, M)
    pE = mp.matrix(M, M)
    pK = mp.matrix(M, M)
    Ps = [W.P(i) for i in range(M)]
    if nodes is None:
        nodes = gl_nodes(max(200, int(12 * float(max(W.ks) * 2 * A))), mp.mpf(0), 2 * A)
    ys, ws = nodes
    E14A = mp.e1(4 * A)
    for i in range(M):
        for j in range(i, M):
            g0 = W.G(i, j, mp.mpf(0))
            gram[i, j] = gram[j, i] = g0
            pole[i, j] = pole[j, i] = 2 * Ps[i] * Ps[j]
            acc = 2 * g0 * E14A
            for y, w in zip(ys, ws):
                acc += w * (2 * mp.exp(-2 * y) * g0 / y - W.G(i, j, y) / mp.sinh(y / 2))
            psi[i, j] = psi[j, i] = acc
            se = mp.mpf(0)
            sk = mp.mpf(0)
            for n in range(2, Nmax + 1):
                ln = mp.log(n)
                if ln < 2 * A:
                    gv = W.G(i, j, ln)
                    se += 2 * cE[n] / mp.sqrt(n) * gv
                    sk += 2 * cK[n] / mp.sqrt(n) * gv
            pE[i, j] = pE[j, i] = se
            pK[i, j] = pK[j, i] = sk
    const = mp.log(20) - 2 * mp.log(mp.pi)
    arch = psi + const * gram
    return dict(gram=gram, pole=pole, arch=arch, psi=psi, pE=pE, pK=pK,
                QE=pole + arch - pE, QK=pole + arch - pK)

def quadval(Mx, v):
    M = len(v)
    return sum(v[i] * Mx[i, j] * v[j] for i in range(M) for j in range(M))

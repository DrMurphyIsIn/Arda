"""crux3 numerics, GENERAL frequencies: the Weil form of zeta and of Davenport-Heilbronn D on the window
[-A, A] (a = 2A = log x), on the (non-orthogonal) span of f_m(u) = e^{i kap_m u} 1_{[-A,A]}(u), kap_m arbitrary real.

  Q(f, f) = sum_{m,n} c_m conj(c_n) M[m][n] for f = sum_m c_m f_m;  Gram G[m][n] = int f_m conj f_n.
  g_{mn}(y) = int f_m(v) conj f_n(v - y) dv  (the cross-correlation; g_{mm} = autocorr f_m).

  Arch_{mn} = G_{mn} CL + sum_l alpha_l I(lam_l)      (off-diagonal),
            = 2A CL + 2A Cc(kap) + Cu(kap)             (diagonal),
     CL = c0 + psi(beta0/2) + sum_j 2 e^{-beta_j a}/beta_j,
     I(lam) = int_0^a W(u) (1 - e^{i lam u}) du
            = psi(beta0/2 - i lam/2) - psi(beta0/2) - sum_j 2 [e^{-beta_j a}/beta_j - e^{-(beta_j - i lam) a}/(beta_j - i lam)],
     Cc(k) = Re I(k),  Cu(k) = int_0^a u cos(ku) W(u) du
            = (1/2) Re psi'(beta0/2 + ik/2) - sum_j 2 Re[e^{-(beta_j - ik) a} (a/(beta_j - ik) + 1/(beta_j - ik)^2)].
     (g(u) + g(-u))/2 = sum_l alpha_l e^{i lam_l u}, 0 < u < a:
        alpha = e^{i d A}/(2 i d) at lam = kap_n and lam = -kap_m;  -e^{-i d A}/(2 i d) at lam = kap_m and lam = -kap_n
        (d = kap_m - kap_n).
  Prime_{mn} = sum_{n' < x} (w(n')/sqrt n') (g(y) + g(-y)), y = log n'.
  Pole_{mn} (zeta) = F_m(i/2) conj F_n(-i/2) + F_m(-i/2) conj F_n(i/2),  F_m(z) = 2 sin((kap_m + z) A)/(kap_m + z).
"""
import mpmath as mp
from weilmodes import weights, consts

mp.mp.dps = 40


class FWindow:
    def __init__(self, A, kind, J=None):
        self.A = mp.mpf(A)
        self.a = 2 * self.A
        self.kind = kind
        self.beta0, self.c0 = consts(kind)
        if J is None:
            J = int(mp.ceil(mp.mp.prec * mp.log(2) / (2 * self.a))) + 4
        self.betas = [self.beta0 + 2 * j for j in range(J)]
        self.psi_half = mp.digamma(self.beta0 / 2)
        a = self.a
        self.CL = self.c0 + self.psi_half + sum(2 * mp.exp(-b * a) / b for b in self.betas)
        x = mp.exp(a)
        self.nmax = int(mp.floor(x))
        if mp.mpf(self.nmax) == x:
            self.nmax -= 1
        w = weights(kind, self.nmax)
        self.primes = [(n, w[n] / mp.sqrt(n), mp.log(n)) for n in range(2, self.nmax + 1) if w[n] != 0]
        self.Icache = {}
        self.Ucache = {}

    def I(self, lam):
        key = mp.nstr(lam, 30)
        if key not in self.Icache:
            a = self.a
            b0 = self.beta0
            v = mp.digamma(mp.mpc(b0 / 2, -lam / 2)) - self.psi_half
            for b in self.betas:
                z = mp.mpc(b, -lam)
                v -= 2 * (mp.exp(-b * a) / b - mp.exp(-z * a) / z)
            self.Icache[key] = v
        return self.Icache[key]

    def Cu(self, k):
        key = mp.nstr(k, 30)
        if key not in self.Ucache:
            a = self.a
            v = mp.re(mp.polygamma(1, mp.mpc(self.beta0 / 2, k / 2))) / 2
            for b in self.betas:
                z = mp.mpc(b, -k)
                v -= 2 * mp.re(mp.exp(-z * a) * (a / z + 1 / (z * z)))
            self.Ucache[key] = v
        return self.Ucache[key]

    def gram(self, km, kn):
        d = km - kn
        if d == 0:
            return 2 * self.A
        return 2 * mp.sin(d * self.A) / d

    def gpair(self, km, kn, y):
        """g(y) + g(-y) for y > 0 (complex in general)."""
        d = km - kn
        A = self.A
        if d == 0:
            return 2 * (2 * A - y) * mp.cos(km * y)
        e1 = mp.expj(d * A)
        e2 = mp.expj(-d * A)
        return (e1 * (mp.expj(kn * y) + mp.expj(-km * y)) - e2 * (mp.expj(km * y) + mp.expj(-kn * y))) / (1j * d)

    def arch(self, km, kn):
        A = self.A
        if km == kn:
            return 2 * A * self.CL + 2 * A * mp.re(self.I(km)) + self.Cu(km)
        d = km - kn
        e1 = mp.expj(d * A) / (2j * d)
        e2 = -mp.expj(-d * A) / (2j * d)
        v = self.gram(km, kn) * self.CL
        v += e1 * (self.I(kn) + self.I(-km)) + e2 * (self.I(km) + self.I(-kn))
        return v

    def prime(self, km, kn):
        return sum(c * self.gpair(km, kn, y) for (nn, c, y) in self.primes)

    def F(self, k, z):
        return 2 * mp.sin((k + z) * self.A) / (k + z)

    def pole(self, km, kn):
        if self.kind != 'zeta':
            return mp.mpf(0)
        h = mp.mpc(0, mp.mpf(1) / 2)
        return self.F(km, h) * mp.conj(self.F(kn, -h)) + self.F(km, -h) * mp.conj(self.F(kn, h))

    def matrices(self, ks):
        """(M, G, comb) as mpmath complex matrices (Hermitian); M = pole + arch - prime, comb = prime."""
        N = len(ks)
        M = mp.matrix(N, N)
        G = mp.matrix(N, N)
        C = mp.matrix(N, N)
        P = mp.matrix(N, N)
        R = mp.matrix(N, N)
        for i in range(N):
            for j in range(N):
                km, kn = ks[i], ks[j]
                p = self.prime(km, kn)
                ar = self.arch(km, kn)
                po = self.pole(km, kn)
                M[i, j] = po + ar - p
                G[i, j] = self.gram(km, kn)
                C[i, j] = p
                P[i, j] = po
                R[i, j] = ar
        return M, G, C, P, R


def gen_eig(M, G):
    """eigenvalues of the pencil (M, G), G > 0, via numpy (complex Hermitian)."""
    import numpy as np
    import scipy.linalg as sl
    Mn = np.array([[complex(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])
    Gn = np.array([[complex(G[i, j]) for j in range(G.cols)] for i in range(G.rows)])
    Mn = (Mn + Mn.conj().T) / 2
    Gn = (Gn + Gn.conj().T) / 2
    return sl.eigh(Mn, Gn)

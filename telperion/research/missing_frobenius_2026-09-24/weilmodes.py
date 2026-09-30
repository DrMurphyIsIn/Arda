"""crux3 numerics: the Weil form of zeta and of Davenport-Heilbronn D on a window, in the COMPLEX Fourier-mode
basis e_m(u) = e^{i k_m u}/sqrt(a), k_m = 2 pi m / a, on [-a/2, a/2], a = log x.  (Tests f supported in
[-a/2, a/2]; f * f~ supported in [-a, a]; only n < x enter the prime side.)

Q(f) = Pole(f) + Arch(f) - Prime(f), Q(f) = sum_{m,n} c_m conj(c_n) M_{mn} for f = sum c_m e_m, M real symmetric.

  Arch: c0 g(0) + int_0^inf [g(0) e^{-2u}/u - W(u) (g(u)+g(-u))/2] du,   W(u) = sum_j 2 e^{-beta_j u},
        zeta: beta0 = 1/2, c0 = -log pi;  D: beta0 = 3/2, c0 = log(5/pi)   (Gamma_R(s) resp. Gamma_R(s+1), q = 5)
  Prime: sum_{n<x} (w(n)/sqrt n) (g(log n) + g(-log n)),  w = Lambda (zeta), w = c_D (Dirichlet coefficients of
        -D'/D, signed, NOT supported on prime powers)
  Pole (zeta only): ghat(i/2) + ghat(-i/2), ghat(z) = F1(z) conj F2(conj z).

Closed forms (grid property e^{i k_m a} = 1), cf. crux2 kappa-certify galerkin_cos.py:
  S(k)  = int_0^a sin(ku) W = Im psi(beta0/2 + ik/2) - sum_j 2k e^{-beta_j a}/(beta_j^2+k^2)
  Cc(k) = int_0^a (1-cos ku) W = Re psi(beta0/2+ik/2) - psi(beta0/2) - sum_j 2 e^{-beta_j a} k^2/(beta_j(beta_j^2+k^2))
  Cu(k) = int_0^a u cos(ku) W = (1/2) Re psi'(beta0/2+ik/2) - sum_j 2 e^{-beta_j a} Re[a/(beta_j-ik) + 1/(beta_j-ik)^2]
  CL    = psi(beta0/2) + c0 + sum_j 2 e^{-beta_j a}/beta_j
  M_arch[n,n] = CL + Cc(k_n) + Cu(k_n)/a ;  M_arch[m,n] = (-1)^{m-n} (S(k_m) - S(k_n)) / (2 pi (m-n))
  prime, y = log n': diag 2 (a-y) cos(k_n y)/a ; off 2 (-1)^{m-n} (sin(k_n y) - sin(k_m y)) / (2 pi (m-n))
  pole: M_pole[m,n] = 2 Re(p_m p_n), p_m = 2 (-1)^m sinh(a/4) / (sqrt(a) (1/2 - i k_m)).
"""
import mpmath as mp

mp.mp.dps = 40


def von_mangoldt(nmax):
    lam = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        m = n
        p = None
        for q in range(2, n + 1):
            if m % q == 0:
                p = q
                break
        while m % p == 0:
            m //= p
        if m == 1:
            lam[n] = mp.log(p)
    return lam


def dh_kappa():
    s5 = mp.sqrt(5)
    return (mp.sqrt(10 - 2 * s5) - 2) / (s5 - 1)


def dh_coeffs(nmax):
    k = dh_kappa()
    cval = {1: mp.mpf(1), 2: k, 3: -k, 4: mp.mpf(-1), 0: mp.mpf(0)}
    return [mp.mpf(0)] + [cval[n % 5] for n in range(1, nmax + 1)]


def lambda_dh(nmax):
    """Dirichlet coefficients of -D'/D: a(n) log n = sum_{d | n} c(d) a(n/d)."""
    a = dh_coeffs(nmax)
    lam = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = a[n] * mp.log(n)
        for d in range(2, n):
            if n % d == 0:
                acc -= lam[d] * a[n // d]
        lam[n] = acc
    return lam


def weights(kind, nmax):
    return von_mangoldt(nmax) if kind == 'zeta' else lambda_dh(nmax)


def consts(kind):
    if kind == 'zeta':
        return mp.mpf(1) / 2, -mp.log(mp.pi)
    return mp.mpf(3) / 2, mp.log(5 / mp.pi)


class Window:
    def __init__(self, a, kind, J=None):
        self.a = mp.mpf(a)
        self.kind = kind
        self.beta0, self.c0 = consts(kind)
        if J is None:
            J = int(mp.ceil(mp.mp.prec * mp.log(2) / (2 * self.a))) + 4
        self.betas = [self.beta0 + 2 * j for j in range(J)]
        self.ebl = [mp.exp(-b * self.a) for b in self.betas]
        self.psi_half = mp.digamma(self.beta0 / 2)
        self.CL = self.psi_half + self.c0 + sum(2 * e / b for b, e in zip(self.betas, self.ebl))
        self.cache = {}
        x = mp.exp(self.a)
        self.nmax = int(mp.floor(x))
        if mp.mpf(self.nmax) == x:
            self.nmax -= 1
        w = weights(kind, self.nmax)
        self.primes = [(n, w[n] / mp.sqrt(n), mp.log(n)) for n in range(2, self.nmax + 1) if w[n] != 0]
        self.sh = mp.sinh(self.a / 4)

    def k(self, m):
        return 2 * mp.pi * m / self.a

    def SCC(self, m):
        """S, Cc, Cu at k_m (m >= 0); S odd in m, Cc and Cu even."""
        am = abs(m)
        if am not in self.cache:
            k = self.k(am)
            a = self.a
            z = mp.mpc(self.beta0 / 2, k / 2)
            dg = mp.digamma(z)
            tg = mp.polygamma(1, z)
            s_geo = mp.mpf(0)
            c_geo = mp.mpf(0)
            u_geo = mp.mpf(0)
            for b, e in zip(self.betas, self.ebl):
                den = b * b + k * k
                s_geo += 2 * k * e / den
                c_geo += 2 * e * k * k / (b * den)
                w = mp.mpc(b, -k)
                u_geo += 2 * e * mp.re(a / w + 1 / (w * w))
            S = dg.imag - s_geo if am > 0 else mp.mpf(0)
            Cc = dg.real - self.psi_half - c_geo if am > 0 else mp.mpf(0)
            Cu = tg.real / 2 - u_geo
            self.cache[am] = (S, Cc, Cu)
        S, Cc, Cu = self.cache[am]
        return (S if m >= 0 else -S), Cc, Cu

    def arch(self, m, n):
        if m == n:
            S, Cc, Cu = self.SCC(n)
            return self.CL + Cc + Cu / self.a
        Sm = self.SCC(m)[0]
        Sn = self.SCC(n)[0]
        return (-1) ** ((m - n) % 2) * (Sm - Sn) / (2 * mp.pi * (m - n))

    def prime(self, m, n, weightfun=None):
        tot = mp.mpf(0)
        a = self.a
        km, kn = self.k(m), self.k(n)
        for (nn, c, y) in self.primes:
            if weightfun is not None:
                c = weightfun(nn, c)
            if m == n:
                tot += c * 2 * (a - y) * mp.cos(kn * y) / a
            else:
                tot += c * 2 * (-1) ** ((m - n) % 2) * (mp.sin(kn * y) - mp.sin(km * y)) / (2 * mp.pi * (m - n))
        return tot

    def pvec(self, m):
        return 2 * (-1) ** (m % 2) * self.sh / (mp.sqrt(self.a) * mp.mpc(mp.mpf(1) / 2, -self.k(m)))

    def pole(self, m, n):
        if self.kind != 'zeta':
            return mp.mpf(0)
        return 2 * mp.re(self.pvec(m) * self.pvec(n))

    def matrix(self, ms, parts=('pole', 'arch', 'prime')):
        N = len(ms)
        M = mp.matrix(N, N)
        for i, m in enumerate(ms):
            for j in range(i, N):
                n = ms[j]
                v = mp.mpf(0)
                if 'pole' in parts:
                    v += self.pole(m, n)
                if 'arch' in parts:
                    v += self.arch(m, n)
                if 'prime' in parts:
                    v -= self.prime(m, n)
                if 'comb' in parts:     # +prime (the comb form itself)
                    v += self.prime(m, n)
                M[i, j] = v
                M[j, i] = v
        return M


def Omega(kind, t):
    b0, c0 = consts(kind)
    return mp.re(mp.digamma(mp.mpc(b0 / 2, mp.mpf(t) / 2))) + c0


def eigs(M):
    import numpy as np
    A = np.array([[float(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])
    return np.linalg.eigvalsh(A)


def eigs_mp(M):
    E, Q = mp.eigsy(M)
    return [E[i] for i in range(len(E))], Q

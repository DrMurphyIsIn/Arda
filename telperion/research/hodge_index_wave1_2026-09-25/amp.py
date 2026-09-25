"""Amplified (convolution-power) Weil sums.
 h(u) = e^{i g0 u} [B(u-T0) + B(u+T0)],  B = m-fold box conv, support [-eps,eps], mass 1.
 supp h in [-T,T], T = T0+eps = (1/2) log x.   h_k = h^{*k}, g_k = h_k * h_k~ (supp [-k log x, k log x]).
 s_k := W(g_k) = sum_rho ghat_k(rho) = sum_rho lam_rho^k,  lam_rho = F(rho) conj F(1-conj rho),
 F(s) = int h(u) e^{(s-1/2)u} du = 2 cosh(T0 z) Bhat(z), z = s-1/2-i g0, Bhat(z)=(sinh(z eps/m)/(z eps/m))^m.
 Prime side (explicit formula):
 s_k = [pole] ghat(1)+ghat(0) + (1/2pi) int |F(1/2+it)|^{2k} A(t) dt - sum_n c(n) n^{-1/2} (g_k(log n)+g_k(-log n)).
"""
import numpy as np, mpmath as mp

def digamma(z):
    z = np.asarray(z, complex).copy(); acc = np.zeros_like(z)
    for _ in range(8):
        acc -= 1 / z; z = z + 1
    z2 = 1 / (z * z)
    ser = np.log(z) - 0.5 / z - z2 * (1/12 - z2 * (1/120 - z2 * (1/252 - z2 * (1/240 - z2 * (1/132)))))
    return acc + ser
G = '/Users/peterwmurphy/arda-frob/telperion/research/missing_frobenius_2026-09-24/'

def chi_m4(n): r = n % 4; return 0 if r % 2 == 0 else (1 if r == 1 else -1)
def leg5(n): return {0: 0, 1: 1, 4: 1, 2: -1, 3: -1}[n % 5]
KAP = float((mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1))

def coeffs(kind, N):
    """c(n) with -L'/L = sum c(n) n^-s, n=0..N"""
    n = np.arange(N + 1)
    if kind in ('zeta', 'ZK'):
        lam = np.zeros(N + 1)
        sieve = np.ones(N + 1, bool); sieve[:2] = False
        for p in range(2, int(N ** .5) + 1):
            if sieve[p]: sieve[p * p::p] = False
        for p in np.nonzero(sieve)[0]:
            q = p
            while q <= N:
                lam[q] = np.log(p); q *= p
        if kind == 'zeta': return lam
        chi = np.array([chi_m4(i) * leg5(i) for i in range(N + 1)])
        return lam * (1 + chi)
    a = np.zeros(N + 1)
    if kind == 'E':
        c20 = np.array([chi_m4(i) * leg5(i) for i in range(N + 1)]); c4 = np.array([chi_m4(i) for i in range(N + 1)])
        l5 = np.array([leg5(i) for i in range(N + 1)])
        for d in range(1, N + 1):
            m = np.arange(d, N + 1, d)
            a[m] += c20[d] + c4[d] * l5[m // d]
        a /= 2
    elif kind == 'D':
        tab = {0: 0., 1: 1., 2: KAP, 3: -KAP, 4: -1.}
        a = np.array([tab[i % 5] for i in range(N + 1)]); a[0] = 0
    assert abs(a[1] - 1) < 1e-12
    c = a * np.log(np.maximum(n, 1))
    # c(n) = a(n) log n - sum_{d|n,1<d<n} c(d) a(n/d): process d increasing
    for d in range(2, N + 1):
        if c[d] != 0:
            m = np.arange(2 * d, N + 1, d)
            c[m] -= c[d] * a[m // d]
    return c

def arch_weight(kind, t):
    if kind == 'zeta': return -np.log(np.pi) + digamma(0.25 + 0.5j * t).real
    if kind in ('ZK', 'E'): return np.log(20) - 2 * np.log(2 * np.pi) + 2 * digamma(0.5 + 1j * t).real
    if kind == 'D': return np.log(5 / np.pi) + digamma(0.75 + 0.5j * t).real
POLE = {'zeta': True, 'ZK': True, 'E': True, 'D': False}

class Test:
    def __init__(self, x, frac, m, g0):
        self.T = 0.5 * np.log(x); self.eps = frac * self.T; self.T0 = self.T - self.eps
        self.m = m; self.g0 = g0; self.x = x
    def F(self, s):
        z = np.asarray(s, complex) - 0.5 - 1j * self.g0
        w = z * self.eps / self.m
        bh = np.where(np.abs(w) < 1e-8, 1.0 + 0j, np.sinh(w) / np.where(np.abs(w) < 1e-8, 1, w)) ** self.m
        return 2 * np.cosh(self.T0 * z) * bh
    def lam(self, rho):
        rho = np.asarray(rho, complex)
        return self.F(rho) * np.conj(self.F(1 - np.conj(rho)))
    def h_grid(self, du):
        # B = m-fold conv of box on [-eps/m, eps/m] density m/(2eps): build numerically
        nb = int(round(2 * self.eps / self.m / du)); nb += (nb % 2 == 0)
        box = np.ones(nb) / (nb * du)
        B = box.copy()
        for _ in range(self.m - 1): B = np.convolve(B, box) * du
        L = len(B); halfB = (L - 1) // 2
        nT0 = int(round(self.T0 / du))
        n = 2 * nT0 + L
        h = np.zeros(n, complex)
        h[0:L] += B; h[2 * nT0:2 * nT0 + L] += B
        u = (np.arange(n) - (n - 1) / 2) * du
        return u, h * np.exp(1j * self.g0 * u)

def fftconv(a, b):
    n = len(a) + len(b) - 1; N = 1 << (n - 1).bit_length()
    return np.fft.ifft(np.fft.fft(a, N) * np.fft.fft(b, N))[:n]

def prime_side(kind, test, ks, cache={}, du=2e-3, tmax=4000., nt=400001):
    """returns dict k -> s_k via explicit formula (arith side)."""
    u0, h = test.h_grid(du)
    kmax = max(ks); N = int(np.floor(test.x ** kmax * 1.0000001)) + 2
    key = (kind, N)
    if key not in cache:
        cache.clear(); cache[key] = coeffs(kind, N)
    c = cache[key]
    ns = np.nonzero(c[:N + 1])[0]; ns = ns[ns >= 2]
    t = np.linspace(-tmax, tmax, nt); Ft = test.F(0.5 + 1j * t); A = arch_weight(kind, t)
    out = {}
    hk = np.array([1.0 / du + 0j]); # delta
    for k in range(1, kmax + 1):
        hk = fftconv(hk, h) * du if k > 1 else h.copy()
        if k not in ks: continue
        # g_k = h_k * h_k~ ; h_k~(u)=conj h_k(-u)
        gk = fftconv(hk, np.conj(hk[::-1])) * du
        L = len(gk); ug = (np.arange(L) - (L - 1) / 2) * du
        lg = np.log(ns.astype(float)); w = c[ns] / np.sqrt(ns)
        gp = np.interp(lg, ug, gk.real) + 1j * np.interp(lg, ug, gk.imag)
        gm = np.interp(-lg, ug, gk.real) + 1j * np.interp(-lg, ug, gk.imag)
        prime = np.sum(w * (gp + gm))
        arch = np.trapezoid(np.abs(Ft) ** (2 * k) * A, t) / (2 * np.pi)
        pole = 0
        if POLE[kind]:
            F1 = test.F(1.0 + 0j); F0 = test.F(0.0 + 0j)
            pole = F1 ** k * np.conj(F0) ** k + F0 ** k * np.conj(F1) ** k
        out[k] = dict(s=(pole + arch - prime), pole=pole, arch=arch, prime=prime)
    return out

def load_zeros(kind):
    if kind == 'zeta':
        import os
        f = G + '../../../../../private/tmp/none'
        zs = [(0.5, float(mp.zetazero(n).imag)) for n in range(1, 301)]
    else:
        zs = [tuple(map(float, l.split())) for l in open(G + f'zeros_{kind}.txt')]
    rhos = []
    for b, g in zs:
        rhos += [b + 1j * g, b - 1j * g]
    return np.array(rhos)

def zero_side(test, rhos, ks):
    lam = test.lam(rhos)
    return {k: np.sum(lam ** k) for k in ks}, lam

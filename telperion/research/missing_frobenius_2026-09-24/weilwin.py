"""Galerkin matrices of the window-restricted Weil quadratic form, for zeta, the
Davenport-Heilbronn function D, and the Dirichlet L-function L(s,chi) mod 5 (chi(2)=i).

Conventions (match Crux3_BAND_CERTIFICATE_2026-09-24.md):
  tests f supported in [-A, A], window x = e^{2A};  F(t) = int f(u) e^{itu} du;
  Q(f) = Pole(f) + (1/2pi) int |F|^2 Omega(t) dt - sum_{n<x} (w(n)/sqrt n)(g(log n)+g(-log n)),
  g = f * f~ (autocorrelation).
  zeta : Omega = Re psi(1/4+it/2) - log pi, w = Lambda, Pole = F(i/2)F(-i/2)+cc
  D    : Omega = Re psi(3/4+it/2) + log(5/pi), w = c_D (coeffs of -D'/D), no pole
  Lchi : same Omega as D, w(n) = Re(chi(n)) Lambda(n), no pole.
u-space form of the archimedean term (for even g):
  (1/2pi) int H(t) Re psi(a/2+1/4+it/2) dt = g(0) psi(1/4+a/2) + int_0^inf (g(0)-g(u)) W_a(u) du,
  W_0(u) = e^{u/2}/sinh u,  W_1(u) = e^{-u/2}/sinh u.
Basis: even sector cos(k pi x/A), k=0..N-1; odd sector sin(k pi x/A), k=1..N.
"""
import numpy as np
import mpmath as mp

KAPPA = float((mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1))


def dh_a(n):
    r = n % 5
    return {0: 0.0, 1: 1.0, 2: KAPPA, 3: -KAPPA, 4: -1.0}[r]


def mangoldt(n):
    if n < 2:
        return 0.0
    for p in range(2, int(n ** 0.5) + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return float(np.log(p)) if m == 1 else 0.0
    return float(np.log(n))


def dh_c(nmax):
    """coefficients c(n) of -D'/D: a(n) log n = sum_{d|n} c(d) a(n/d), a(1)=1."""
    c = [0.0] * (nmax + 1)
    for n in range(2, nmax + 1):
        s = dh_a(n) * np.log(n)
        for d in range(2, n):
            if n % d == 0:
                s -= c[d] * dh_a(n // d)
        c[n] = s  # a(1)=1
    return c


def chi5_re(n):
    # chi mod 5 with chi(2)=i: chi(1)=1, chi(2)=i, chi(4)=-1, chi(3)=-i
    return {0: 0.0, 1: 1.0, 2: 0.0, 3: 0.0, 4: -1.0}[n % 5]


def weights(kind, nmax):
    if kind == 'zeta':
        return [0.0, 0.0] + [mangoldt(n) for n in range(2, nmax + 1)]
    if kind == 'D':
        return dh_c(nmax)
    if kind == 'Lchi':
        return [0.0, 0.0] + [chi5_re(n) * mangoldt(n) for n in range(2, nmax + 1)]
    if kind == 'arch':  # archimedean + pole only (Connes-Consani S={inf} object)
        return [0.0] * (nmax + 1)
    raise ValueError(kind)


def _I(gam, c, a, b):
    """int_a^b cos(gam x + c) dx, vectorised; a may be array."""
    gam = np.asarray(gam, float)
    small = np.abs(gam) < 1e-14
    gs = np.where(small, 1.0, gam)
    val = (np.sin(gs * b + c) - np.sin(gs * a + c)) / gs
    return np.where(small, (b - a) * np.cos(c), val)


def corr(A, freqs, u, parity):
    """h_jk(u) = int phi_j(x) phi_k(x-u) dx, u >= 0 array. returns (N,N,len(u))."""
    al = freqs[:, None, None]
    be = freqs[None, :, None]
    uu = np.asarray(u, float)[None, None, :]
    a = -A + uu
    b = A
    t1 = _I(al - be, be * uu, a, b)
    t2 = _I(al + be, -be * uu, a, b)
    return 0.5 * (t1 + t2) if parity == 0 else 0.5 * (t1 - t2)


def _F(c, al, A):
    return (np.exp(c * A) * (c * np.cos(al * A) + al * np.sin(al * A)) - c) / (c * c + al * al)


def _S(c, al, A):
    return (np.exp(c * A) * (c * np.sin(al * A) - al * np.cos(al * A)) + al) / (c * c + al * al)


def basis(A, N, parity):
    k = np.arange(N) if parity == 0 else np.arange(1, N + 1)
    freqs = k * np.pi / A
    gram = np.full(N, A)
    if parity == 0:
        gram[0] = 2 * A
    return freqs, np.diag(gram)


_TAIL = {}


def w_arch(u, a):
    return np.exp((0.5 if a == 0 else -0.5) * u) / np.sinh(u)


def tail(A2, a):
    key = (round(A2, 14), a)
    if key not in _TAIL:
        e = 0.5 if a == 0 else -0.5
        _TAIL[key] = float(mp.quad(lambda u: mp.e ** (e * u) / mp.sinh(u), [A2, mp.inf]))
    return _TAIL[key]


def form_matrix(kind, A, N, parity, M=400, pole=True):
    """Galerkin matrix Q_jk and Gram matrix on the basis of the given parity."""
    freqs, G = basis(A, N, parity)
    a = 0 if kind in ('zeta', 'arch') else 1
    if a == 0:
        const = float(mp.digamma(0.25) - mp.log(mp.pi))
    else:
        const = float(mp.digamma(0.75) + mp.log(5 / mp.pi))
    xs, ws = np.polynomial.legendre.leggauss(M)
    # split [0,2A] into 4 panels for accuracy
    Q = np.zeros((N, N))
    h0 = corr(A, freqs, np.array([0.0]), parity)[:, :, 0]
    edges = np.linspace(0, 2 * A, 9)
    for lo, hi in zip(edges[:-1], edges[1:]):
        u = 0.5 * (hi - lo) * xs + 0.5 * (hi + lo)
        wq = 0.5 * (hi - lo) * ws
        h = corr(A, freqs, u, parity)
        Q += np.einsum('jku,u->jk', (h0[:, :, None] - h), wq * w_arch(u, a))
    Q += h0 * (const + tail(2 * A, a))
    # prime / comb side
    x = np.exp(2 * A)
    nmax = int(np.floor(x - 1e-12))
    wts = weights(kind, max(nmax, 2))
    for n in range(2, nmax + 1):
        if wts[n] != 0.0 and np.log(n) < 2 * A:
            hn = corr(A, freqs, np.array([np.log(n)]), parity)[:, :, 0]
            Q -= 2 * wts[n] / np.sqrt(n) * 0.5 * (hn + hn.T)
    if pole and a == 0:
        if parity == 0:
            v = _F(0.5, freqs, A) + _F(-0.5, freqs, A)
            Q += 2 * np.outer(v, v)
        else:
            v = _S(0.5, freqs, A) - _S(-0.5, freqs, A)
            Q -= 2 * np.outer(v, v)
    Q = 0.5 * (Q + Q.T)
    return Q, G, freqs


def min_eig(kind, A, N, parity, **kw):
    Q, G, f = form_matrix(kind, A, N, parity, **kw)
    d = 1 / np.sqrt(np.diag(G))
    Qn = Q * d[:, None] * d[None, :]
    ev, V = np.linalg.eigh(Qn)
    return ev, V * d[:, None], f


def Fhat(coef, freqs, A, t, parity):
    t = np.asarray(t, float)[:, None]
    al = freqs[None, :]
    if parity == 0:
        G = np.sinc((t - al) * A / np.pi) * A + np.sinc((t + al) * A / np.pi) * A
    else:  # int sin(al x) e^{itx} = i * (int sin(al x) sin(tx)) ; return the real factor
        G = np.sinc((t - al) * A / np.pi) * A - np.sinc((t + al) * A / np.pi) * A
    return G @ coef

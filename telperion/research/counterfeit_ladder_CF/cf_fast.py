"""float64 Galerkin model for the threshold study (both parity sectors).  Same formulas as cf_core
(spatial arch, closed-form cross-correlations), vectorized with numpy.  Used only for the threshold
bracket; the x = 28 separation numbers come from cf_core at 30 digits."""
import numpy as np
from math import log, pi, sqrt
import mpmath
def exp1(z): return float(mpmath.e1(z))
from cf_core import lattice_aE, aK, chi_m20, divisors

def mangoldt_f(n):
    if n < 2:
        return 0.0
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return log(p) if m == 1 else 0.0

def coeffs_f(nmax):
    cE = [0.0] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = lattice_aE(n) * log(n)
        for d in divisors(n):
            if d < n:
                acc -= cE[d] * lattice_aE(n // d)
        cE[n] = acc
    cK = [0.0] + [mangoldt_f(n) * (1 + chi_m20(n)) for n in range(1, nmax + 1)]
    return np.array(cE), np.array(cK)

def prim(par, a, b, x, y):
    """antiderivative in x of phi_a(x) phi_b(x - y), phi = cos (par 0) or sin (par 1)."""
    sgn = 1.0 if par == 0 else -1.0
    same = np.isclose(a, b)
    d = np.where(same, 1.0, a - b)
    t1 = np.where(same, x * np.cos(a * y) / 2, np.sin((a - b) * x + b * y) / (2 * d))
    t2 = np.where(same, np.sin(2 * a * x - a * y) / (4 * a), np.sin((a + b) * x - b * y) / (2 * (a + b)))
    return t1 + sgn * t2

def cross(par, a, b, A, y):
    return prim(par, a, b, A, y) - prim(par, a, b, y - A, y)

def Gsym(par, ka, kb, A, y):
    return 0.5 * (cross(par, ka, kb, A, y) + cross(par, kb, ka, A, y))

def build(x, M, par, cE, cK, nquad=None):
    A = 0.5 * log(x)
    if par == 0:
        ks = np.array([(m + 0.5) * pi / A for m in range(M)])
    else:
        ks = np.array([(m + 1.0) * pi / A for m in range(M)])
    KA = ks[:, None] * np.ones((1, M))
    KB = KA.T
    # quadrature nodes on [0, 2A]
    if nquad is None:
        nquad = int(max(200, 8 * ks.max() * 2 * A))
    t, w = np.polynomial.legendre.leggauss(nquad)
    ys = A * (t + 1)
    ws = A * w
    g0 = Gsym(par, KA, KB, A, 0.0)
    psi = 2 * g0 * exp1(4 * A)
    for y, wt in zip(ys, ws):
        psi = psi + wt * (2 * np.exp(-2 * y) * g0 / y - Gsym(par, KA, KB, A, y) / np.sinh(y / 2))
    arch = psi + (log(20) - 2 * log(pi)) * g0
    # pole: V_i(+-1/2) = int phi_i(u) e^{+-u/2} du
    tu, wu = np.polynomial.legendre.leggauss(400)
    us = A * tu
    wus = A * wu
    phi = (np.cos if par == 0 else np.sin)(np.outer(ks, us))
    Vp = phi @ (wus * np.exp(us / 2))
    Vm = phi @ (wus * np.exp(-us / 2))
    pole = np.outer(Vp, Vm) + np.outer(Vm, Vp)
    pE = np.zeros((M, M))
    pK = np.zeros((M, M))
    for n in range(2, int(x) + 1):
        ln = log(n)
        if ln < 2 * A and (cE[n] != 0 or cK[n] != 0):
            G = Gsym(par, KA, KB, A, ln)
            pE += 2 * cE[n] / sqrt(n) * G
            pK += 2 * cK[n] / sqrt(n) * G
    return dict(A=A, ks=ks, g0=g0, pole=pole, arch=arch, QE=pole + arch - pE, QK=pole + arch - pK)

def lam_min(Q, g0):
    # generalized eigenproblem Q v = lam g0 v (g0 = Gram of int v^2)
    L = np.linalg.cholesky(g0)
    Li = np.linalg.inv(L)
    S = Li @ Q @ Li.T
    S = (S + S.T) / 2
    return np.linalg.eigvalsh(S)[0]

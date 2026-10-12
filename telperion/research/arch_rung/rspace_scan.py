"""r-space parameter scan for the archimedean-rung certificate (float64).  2026-10-11.
Numerical, not kernel-checked.  conjecture1_proved = False.

Pole-free class (paperFT g (I/2) = int g e^{-u/2} = 0), tsupport g in [-L, L]:
    Q(g) = (1/2pi) int |ghat|^2 (psiR(r) - log pi) dr.
Legendre basis P_k(u/L): ghat_k(r) = 2L i^k j_k(rL), Gram diag(2L/(2k+1)).

Prints:
  (a) lambda_min of Q (exact symbol, r-quadrature) on the one-condition class -- cross-check of
      polefree_numerics.py (u-space);
  (b) the same with the symbol clipped at R (min(psiR(r), psiR(R))) and with a step lower envelope;
  (c) the D(r)^2-capped bathtub bound (intermediate rung, no matrix) and its threshold in L.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import digamma, spherical_jn
from scipy.linalg import eigh, null_space
from scipy.optimize import brentq

LOGPI = math.log(math.pi)


def psiR(r):
    return digamma(0.25 + 0.5j * np.asarray(r)).real


def ghat(L, K, r):
    """K x len(r) complex: int_{-L}^{L} P_k(u/L) e^{i r u} du = 2L i^k j_k(rL)."""
    r = np.asarray(r, float)
    out = np.empty((K, len(r)), complex)
    for k in range(K):
        out[k] = 2 * L * (1j) ** k * spherical_jn(k, r * L)
    return out


def constraint(L, K):
    x, w = leggauss(K + 40)
    from numpy.polynomial.legendre import legvander
    return (legvander(x, K - 1) * (w * np.exp(-L * x / 2))[:, None]).sum(0) * L


def form(L, K, weight, R, nodes_per_unit=12):
    """A_kl = (1/2pi) int_{-R}^{R} conj ghat_k ghat_l weight(r) dr (real part; even weight)."""
    n = int(R * nodes_per_unit) + 50
    x, w = leggauss(n)
    r, wr = R * (x + 1) / 2, R * w / 2           # [0, R], double for symmetry
    G = ghat(L, K, r)
    A = (G.conj() * (wr * weight(r))) @ G.T / (2 * math.pi) * 2
    return A.real


def lam_one(L, K, A):
    Gm = np.diag(2 * L / (2 * np.arange(K) + 1))
    Z = null_space(np.atleast_2d(constraint(L, K)))
    return eigh(Z.T @ A @ Z, Z.T @ Gm @ Z, eigvals_only=True)[0]


def exact_lam(L, K=36, R=150.0):
    """Q with the exact symbol: psiR - log pi on [-R, R], tail beyond R by the clipped value
    (psiR grows, so this is a slight UNDER-estimate of Q)."""
    sR = psiR(R) - LOGPI
    Gm = np.diag(2 * L / (2 * np.arange(K) + 1))
    A = sR * Gm - form(L, K, lambda r: sR - (psiR(r) - LOGPI), R)
    return lam_one(L, K, A)


def clipped_lam(L, R, K=36):
    sR = psiR(R) - LOGPI
    Gm = np.diag(2 * L / (2 * np.arange(K) + 1))
    A = sR * Gm - form(L, K, lambda r: sR - (psiR(r) - LOGPI), R)
    return lam_one(L, K, A)


def step_lam(L, grid, K=36):
    """Step lower envelope: v = psiR(r_j) - log pi on [r_j, r_{j+1}), psiR(R) - log pi beyond."""
    grid = np.asarray(grid, float)
    vals = psiR(grid) - LOGPI
    sR = vals[-1]

    def wfun(r):
        idx = np.searchsorted(grid, r, side="right") - 1
        idx = np.clip(idx, 0, len(grid) - 1)
        return sR - vals[idx]
    Gm = np.diag(2 * L / (2 * np.arange(K) + 1))
    A = sR * Gm
    for j in range(len(grid) - 1):
        a, b = grid[j], grid[j + 1]
        x, w = leggauss(40)
        r, wr = (b - a) * (x + 1) / 2 + a, (b - a) * w / 2
        G = ghat(L, K, r)
        A = A - ((G.conj() * wr) @ G.T).real / (2 * math.pi) * 2 * (sR - vals[j])
    return lam_one(L, K, A)


def D2(L, r):
    """D(r)^2 = min_c int_{-L}^{L} |e^{iru} - c e^{-u/2}|^2 du = 2L - |A(r)|^2 / (2 sinh L)."""
    z = 1j * r - 0.5
    A = (np.exp(z * L) - np.exp(-z * L)) / z
    return 2 * L - np.abs(A) ** 2 / (2 * math.sinh(L))


def bathtub(L, rmax=200.0, n=200000):
    """inf of (1/2pi) int mu (psiR - log pi) over 0 <= mu <= D^2, int mu = 2pi (per unit ||g||^2)."""
    r = np.linspace(0, rmax, n)
    dr = r[1] - r[0]
    d2 = D2(L, r)
    phi = psiR(r) - LOGPI
    mass = np.cumsum(2 * d2 * dr)                # both signs of r
    j = np.searchsorted(mass, 2 * math.pi)
    val = np.sum(2 * d2[:j] * phi[:j] * dr)
    val += (2 * math.pi - mass[j - 1]) * phi[j]
    return val / (2 * math.pi), r[j]


if __name__ == "__main__":
    L0 = math.log(2) / 2
    L1 = 0.3466
    print("(a) exact-symbol lambda_min, one condition:")
    for L in [0.236, 0.3, L0, L1, 0.36, 0.37, 0.375, 0.38]:
        print(f"   L={L:.5f}  K=30 {exact_lam(L, 30):+.6f}  K=40 {exact_lam(L, 40):+.6f}")
    print("(b) clipped at R (L = 0.3466):")
    for R in [10, 15, 20, 25, 30, 40, 60, 100]:
        print(f"   R={R:4d}  psiR(R)-log pi={psiR(R) - LOGPI:.4f}  lambda={clipped_lam(L1, R):+.6f}")
    print("(b') step envelope, uniform grid of width h up to R (L = 0.3466):")
    for R in [30, 40]:
        for h in [1.0, 0.5, 0.25]:
            grid = np.arange(0, R + 1e-9, h)
            print(f"   R={R} h={h}  lambda={step_lam(L1, grid):+.6f}")
    print("(c) D^2-capped bathtub bound (no matrix):")
    for L in [0.1, 0.15, 0.2, 0.22, 0.24, 0.26]:
        v, rs = bathtub(L)
        print(f"   L={L:.3f}  bound={v:+.5f}  fill radius={rs:.2f}")
    Lb = brentq(lambda L: bathtub(L, rmax=400, n=800000)[0], 0.2, 0.36)
    print(f"   bathtub threshold L* = {Lb:.5f}")

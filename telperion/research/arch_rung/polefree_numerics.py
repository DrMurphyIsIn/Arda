"""Pole-free archimedean Weil form: numerical sanity checks (float64).  2026-10-11.
Numerical, not kernel-checked.  conjecture1_proved = False.

Conventions (RHDefs.lean, WeilExplicit / E6Bridge31):
  paperFT g z = int g(u) e^{i z u} du, so paperFT g (I/2) = int g(u) e^{-u/2} du.
  Pole-free class: paperFT g (I/2) = 0 (ONE complex linear condition; it kills both pole terms,
  E6Bridge31 poles_vanish).  On it, for tsupport g in [-L, L], 2L <= log 2:
     Re weilForm (autocorr g) = Q(g) := -log(pi) ||g||^2 + (1/2pi) int |ghat(r)|^2 psiR(r) dr.
  The form has a real symmetric kernel, so for complex g = a + i b, Q(g) = Q(a) + Q(b) and the
  constraint splits; real g suffices for the numerics.

Computes, on a Legendre basis of L^2[-L, L] (u-space identity, weil_f64-style quadrature):
  (1) lambda_min of Q on {int g e^{-u/2} = 0} (the Lean statement's class) and on the
      two-condition class {int g e^{+-u/2} = 0} (previous project number 0.547), vs L;
  (2) the same for the truncated forms Q_N0(g) = H_N0 ||g||^2 - sum_{b in B_N0} <g, K_b g>,
      K_b(u) = e^{-b|u|}, B_N0 = {1/2} u {2n + 5/2 : n < N0}, H_N0 = -gamma - log pi + sum_{n<N0} 1/(n+1)
      (the E6Bridge32 phiN lower bound of psiR), which is what the Lean proof can see;
  (3) the threshold of the Jensen + Wirtinger route (intermediate rung, see blueprint section 2).
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import sys
import numpy as np
from numpy.polynomial.legendre import legvander, leggauss
from scipy.special import digamma
from scipy.linalg import eigh, null_space
from scipy.optimize import brentq

GAMMA = 0.57721566490153286
LOGPI = math.log(math.pi)


def phi(t, N):
    return legvander(t, N - 1) * np.sqrt((2 * np.arange(N) + 1) / 2)


def corr(s, N, xg, wg):
    """F(s)_{jk} = int_{s-1}^{1} phi_j(t) phi_k(t - s) dt, 0 <= s <= 2 (t-units)."""
    a, b = s - 1, 1.0
    t = (b - a) / 2 * xg + (a + b) / 2
    w = (b - a) / 2 * wg
    return (phi(t, N) * w[:, None]).T @ phi(t - s, N)


def kernel_forms(L, N, kernels, panels=24, ng=40):
    """Matrices of int int g_j(v) g_k(w) K(v - w) for even kernels K given as callables on u >= 0,
    basis g_j(u) = phi_j(u/L)/sqrt(L) (orthonormal in L^2[-L, L])."""
    xg, wg = leggauss(N + 6)
    xs, ws = leggauss(ng)
    out = [np.zeros((N, N)) for _ in kernels]
    for p in range(panels):
        a, b = 2 * p / panels, 2 * (p + 1) / panels
        for x, w in zip(xs, ws):
            s = (b - a) / 2 * x + (a + b) / 2
            ww = (b - a) / 2 * w * L        # du = L ds; the basis normalisation 1/L is absorbed in F
            F = corr(s, N, xg, wg)
            S = F + F.T
            for i, K in enumerate(kernels):
                out[i] += ww * K(L * s) * S
    return out


def true_Q(L, N, panels=32, ng=48):
    """Q on the full class, poles excluded:  Q(g) = (psi(1/4) - log pi + int_{2L}^inf K) ||g||^2
    + int_0^{2L} (f(0) - f_e(u)) K(u) du,  K(u) = 2 e^{-u/2}/(1 - e^{-2u}) (weil_arb convention)."""
    xg, wg = leggauss(N + 6)
    xs, ws = leggauss(ng)
    tail = sum(2 * math.exp(-(0.5 + 2 * k) * 2 * L) / (0.5 + 2 * k) for k in range(400))
    H = (digamma(0.25) - LOGPI + tail) * np.eye(N)
    I = np.eye(N)
    for p in range(panels):
        a, b = 2 * p / panels, 2 * (p + 1) / panels
        for x, w in zip(xs, ws):
            s = (b - a) / 2 * x + (a + b) / 2
            ww = (b - a) / 2 * w * L
            u = L * s
            F = corr(s, N, xg, wg)
            E = (F + F.T) / 2
            K = 2 * math.exp(-u / 2) / (-math.expm1(-2 * u))
            H += ww * K * (I - E)
    return (H + H.T) / 2


def constraint(L, N, sgn=-1.0):
    """c_j = int g_j(u) e^{sgn u/2} du."""
    x, w = leggauss(N + 40)
    return (phi(x, N) * (w * np.exp(sgn * L * x / 2))[:, None]).sum(0) * math.sqrt(L)


def lam_restricted(H, C):
    Z = null_space(np.atleast_2d(C))
    return eigh(Z.T @ H @ Z, eigvals_only=True)


def truncated_Q(L, N, N0):
    bs = [0.5] + [2 * n + 2.5 for n in range(N0)]
    Hc = -GAMMA - LOGPI + sum(1 / (n + 1) for n in range(N0))
    mats = kernel_forms(L, N, [lambda u, b=b: math.exp(-b * u) for b in bs])
    return Hc * np.eye(N) - sum(mats)


def sigma_N0(r, N0):
    """(r^2 + 1/4) (phi_N0(r) - log pi): the Q-trick symbol of the truncated weight."""
    bs = [0.5] + [2 * n + 2.5 for n in range(N0)]
    Hc = -GAMMA - LOGPI + sum(1 / (n + 1) for n in range(N0))
    w = sum(2 * b / (b * b + r * r) for b in bs)
    return (r * r + 0.25) * (Hc - w)


def jensen_threshold(N0):
    """Largest L with sigma_N0 >= 0 and nondecreasing on r >= pi/(2L)."""
    r0 = brentq(lambda r: sigma_N0(r, N0), 1.0, 60.0)
    return math.pi / (2 * r0), r0


if __name__ == "__main__":
    L0 = math.log(2) / 2
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    print("== (1) true pole-free form: lambda_min / ||g||^2 (Legendre N=%d)" % N)
    for L in [0.1, 0.2, 0.236, 0.25, 0.3, L0, 0.36, 0.4, 0.45, 0.5]:
        H = true_Q(L, N)
        c1 = constraint(L, N, -1.0)
        c2 = constraint(L, N, +1.0)
        full = eigh(H, eigvals_only=True)[0]
        one = lam_restricted(H, c1)[0]
        two = lam_restricted(H, np.vstack([c1, c2]))[0]
        print(f"L={L:.5f}  no-condition(arch only, no poles)={full:+.5f}  one condition={one:+.6f}  both={two:+.6f}")
    print("== (2) truncated forms Q_N0 at L = (log 2)/2 and L = 0.3466, one condition")
    for L in [L0, 0.3466]:
        c1 = constraint(L, N, -1.0)
        for N0 in [0, 1, 2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 40]:
            H = truncated_Q(L, N, N0)
            print(f"L={L:.5f} N0={N0:3d}  lambda_min={lam_restricted(H, c1)[0]:+.6f}")
    print("== (3) Jensen + Wirtinger threshold (intermediate rung)")
    for N0 in [5, 10, 20, 40, 80, 1000]:
        Lj, r0 = jensen_threshold(N0)
        print(f"N0={N0}: sigma_N0 zero at r={r0:.4f}, L* = pi/(2 r0) = {Lj:.5f}")

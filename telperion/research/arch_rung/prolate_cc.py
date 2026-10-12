"""Reproduction of the numerical core of Connes-Consani arXiv:2006.13771 (float64 + mpmath checks).
2026-10-11.  Numerical, NOT certified, NOT kernel-checked.  conjecture1_proved = False.

Objects (CC section numbers):
  * even prolates PS_{2n,0}(c, x), c = 2 pi, as eigenvectors of W = -d/dx (1-x^2) d/dx + c^2 x^2
    in the normalised even Legendre basis (tridiagonal);  (66)
  * lambda(n): int_{-1}^{1} PS(x) e^{2 pi i x w} dx = lambda(n) PS(w);  (68)
  * xi_n = PS / ||PS||, ||.||^2 = int_0^1 |.|^2 (inner product (16) on L^2(R)_ev);
  * eps(rho), rho >= 1:  sum lambda^2/(1-lambda^2) rho^{1/2} int_{1/rho}^1 xi(x) xi(rho x) dx   (Lemma 5.4 proof)
  * eps'(1+) = sum lambda^2/(1-lambda^2) xi_n(1)^2  (Lemma 5.4; CC: 22.9965)
  * (Q eps)(rho) = sum lambda^2/(1-lambda^2) C_n(rho)   (99)
  * chi(x) = (Q eps)(e^{|x|}) / (2 eps'(1+)),  K_I f(x) = int_I chi(y - x) f(y) dy  on I = [-a/2, a/2]  (104)
Checks against CC: sum lambda(n)^2 = 2(Si(4pi)/(4pi) + 1) = 2.237484835 (Rem 4.6), sum lambda^2 xi(1)^2 = 2,
eps'(1+) = 22.9965, lambda_max(K_I) = 1.05158, lambda_2 = 0.686494 at a = log 2 (127).
Then: the window a* where lambda_max(K_I) = 1 (Sonin route with only ghat(i/2) = 0), and the
Schur / L1 window where 2 int_0^{a} |chi| <= 1 (crude, Cor 3.8 analogue for eps).
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import numpy as np
from numpy.polynomial import legendre as Lg
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh
from scipy.special import sici
from scipy.optimize import brentq

C = 2 * math.pi
NLEG = 80          # even Legendre degrees 0, 2, ..., 2*(NLEG-1)
NPRO = 14          # even prolates kept


def prolates():
    """Return list of (lambda_n, coefficient vector in standard Legendre P_k (all degrees))."""
    ks = 2 * np.arange(NLEG)
    A = np.zeros((NLEG, NLEG))
    for i, k in enumerate(ks):
        # <P_k, x^2 P_k>/<P_k,P_k> = (2k^2+2k-1)/((2k+3)(2k-1))
        A[i, i] = k * (k + 1) + C ** 2 * (2 * k * k + 2 * k - 1) / ((2 * k + 3) * (2 * k - 1))
        if i + 1 < NLEG:
            # normalised: <Pbar_k, x^2 Pbar_{k+2}> = (k+1)(k+2)/((2k+3) sqrt((2k+1)(2k+5)))
            v = C ** 2 * (k + 1) * (k + 2) / ((2 * k + 3) * math.sqrt((2 * k + 1) * (2 * k + 5)))
            A[i, i + 1] = A[i + 1, i] = v
    w, V = eigh(A)
    out = []
    xg, wg = leggauss(200)
    for n in range(NPRO):
        cn = np.zeros(2 * NLEG)
        cn[ks] = V[:, n] * np.sqrt((2 * ks + 1) / 2)      # normalised -> standard Legendre coefficients
        ps = Lg.legval(xg, cn)
        if Lg.legval(0.0, cn) < 0:
            cn = -cn; ps = -ps
        # lambda: int_{-1}^1 PS(x) cos(2 pi x w) dx = lambda PS(w), least squares over a few w
        ws = np.linspace(0.05, 0.9, 7)
        lhs = np.array([np.sum(wg * ps * np.cos(C * xg * om)) for om in ws])
        rhs = Lg.legval(ws, cn)
        lam = float(np.dot(lhs, rhs) / np.dot(rhs, rhs))
        nrm = math.sqrt(np.sum(wg * ps ** 2) / 2)          # int_0^1 PS^2
        out.append((lam, cn / nrm))
    return out


PRO = prolates()


def xi(n, x, der=0):
    c = PRO[n][1]
    if der:
        c = Lg.legder(c, der)
    return Lg.legval(x, c)


def checks():
    lam = np.array([p[0] for p in PRO])
    si4pi = sici(4 * math.pi)[0]
    print("lambda(n):", np.array2string(lam[:6], precision=6))
    print(f"sum lambda^2 = {np.sum(lam ** 2):.9f}   CC/Rem 4.6: 2(Si(4pi)/4pi + 1) = {2 * (si4pi / (4 * math.pi) + 1):.9f}")
    x1 = np.array([xi(n, 1.0) for n in range(NPRO)])
    print(f"sum lambda^2 xi(1)^2 = {np.sum(lam ** 2 * x1 ** 2):.6f}  (CC: 2)")
    t = lam ** 2 / (1 - lam ** 2) * x1 ** 2
    print("t(n) =", np.array2string(t[:5], precision=6), f" eps'(1+) = {t.sum():.5f}  (CC: 22.9965; t(0..4) = 11.9719, 8.77574, 2.20528, 0.0433983, 0.000125459)")
    # analytic continuation check: xi(w) vs (1/lambda) int cos(2 pi x w) xi(x) dx at w = 1.5
    xg, wg = leggauss(200)
    for n in range(3):
        direct = xi(n, 1.5)
        viaF = np.sum(wg * xi(n, xg) * np.cos(C * xg * 1.5)) / lam[n]
        print(f"   xi_{n}(1.5): Legendre series {direct:.10f}  via eigen-relation {viaF:.10f}")
    return t.sum()


def Qeps(rho):
    """(Q eps)(rho) for rho in [1, 2] via (99)."""
    lam = [p[0] for p in PRO]
    xg, wg = leggauss(120)
    a, b = 1 / rho, 1.0
    xs = (b - a) / 2 * xg + (a + b) / 2
    ws = (b - a) / 2 * wg
    tot = 0.0
    for n in range(NPRO):
        l = lam[n]
        if abs(l) < 1e-14:
            continue
        coef = l * l / (1 - l * l)
        d1x = xi(n, xs, 1)
        d1rx = xi(n, rho * xs, 1)
        I = rho ** 0.5 * np.sum(ws * xs * d1x * rho * xs * d1rx)
        Cn = I + rho ** -1.5 * xi(n, 1 / rho, 1) * xi(n, 1.0) - rho ** 1.5 * xi(n, 1.0) * xi(n, rho, 1)
        tot += coef * Cn
    return tot


def chi_table(eps1, npts=4001):
    x = np.linspace(0, math.log(2), npts)
    q = np.array([Qeps(math.exp(v)) for v in x])
    return x, q / (2 * eps1)


def kmax(a, xs, chi, N=600):
    """top eigenvalues of K_I on I = [-a/2, a/2] (Nystrom, Gauss nodes)."""
    xg, wg = leggauss(N)
    t = a / 2 * xg
    w = a / 2 * wg
    D = np.abs(t[:, None] - t[None, :])
    K = np.interp(D, xs, chi)
    S = np.sqrt(w)
    M = S[:, None] * K * S[None, :]
    ev = np.linalg.eigvalsh(M)
    return ev[::-1][:3]


if __name__ == "__main__":
    eps1 = checks()
    xs, chi = chi_table(eps1)
    print(f"chi(0) = {chi[0]:+.3e} (Q eps(1) = 0),  chi range on [0, log 2]: [{chi.min():.3f}, {chi.max():.3f}]  (CC Fig 10: about [-1, 3])")
    L2 = math.log(2)
    print("lambda_max, lambda_2, lambda_3 of K_I at |I| = log 2:", kmax(L2, xs, chi), " (CC (127): 1.05158, 0.686494, 0.0288921)")
    for a in [0.3, 0.4, 0.5, 0.55, 0.6, 0.65, L2]:
        print(f"   |I| = a = {a:.4f} (our L = a/2 = {a / 2:.4f}): lambda_max(K_I) = {kmax(a, xs, chi)[0]:.5f}")
    astar = brentq(lambda a: kmax(a, xs, chi)[0] - 1, 0.3, L2)
    print(f"a* (lambda_max(K_I) = 1) = {astar:.5f}, i.e. our half-width L* = {astar / 2:.5f}")
    # Schur / L1 window: ||K_I|| <= int_{-a}^{a} |chi| = 2 int_0^a |chi|
    cum = np.concatenate([[0], np.cumsum(np.abs(chi[1:]) * np.diff(xs))]) * 2
    aS = xs[np.searchsorted(cum, 1.0)]
    print(f"L1/Schur window: 2 int_0^a |chi| <= 1 up to a = {aS:.5f} (our L = {aS / 2:.5f})")

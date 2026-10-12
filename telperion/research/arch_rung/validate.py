"""Independent float validation of the certificate chain (cert_exact.py) on concrete test functions.
2026-10-11.  Numerical, not kernel-checked.  conjecture1_proved = False.

For each test g (the u-space minimiser of Q on the pole-free class at L1, and random smooth
pole-free g = bump * polynomial projected onto int g e^{-u/2} = 0) it checks, in float64:
  (T1) Taylor: max_{|r| <= R} |ghat(r) - P(r)| <= 2 ||g||_1 (R L)^M / M!   (S3);
  (T2) Bessel: sum_k w_k |mt_k|^2 <= ||g||^2                              (S5);
  (T3) certificate consequence: (1+eta) mt^T Z mt <= KAPPA ||g||^2 + RHO (c^T mt)^2   (S7);
  (T4) the step form: (1/2pi) int |ghat|^2 v >= margin ||g||^2, and Q(g) >= margin ||g||^2.
usage: python validate.py [config]
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import sys
import math
import numpy as np
from numpy.polynomial.legendre import leggauss, legvander
from scipy.special import digamma
from flint import fmpq
import cert_exact as CE
import polefree_numerics as PN

rng = np.random.default_rng(20261011)


def psiR(r):
    return digamma(0.25 + 0.5j * np.asarray(r)).real


def fourier(gvals, u, wu, r):
    return (np.exp(1j * np.outer(r, u)) * (gvals * wu)[None, :]).sum(1)


def run(name):
    cfg = CE.CONFIGS[name]
    B, out, KAPPA, C, D = CE.certify(name)
    L, M = float(B["L"]), B["M"]
    R = float(B["grid"][-1])
    grid = np.array([float(x) for x in B["grid"]])
    s = np.array([float(x) for x in B["s"]])
    Zs = np.array([[float(B["Zs"][i, j]) for j in range(M)] for i in range(M)])
    Z = Zs / (2 * math.pi)
    c = np.array([float(x) for x in B["c"]])
    w = np.array([float(x) for x in B["w"]])
    eta, rho, kap = float(B["eta"]), float(B["rho"]), float(KAPPA)
    margin = out["margin"]
    x, wx = leggauss(400)
    u, wu = L * x, L * wx
    P = legvander(x, M - 1)                      # P_k(u/L)
    # Taylor polynomials q_k(r) = i^k Q_k(r) from the exact data
    tests = []
    # the u-space minimiser (normalised Legendre basis phi_j(u/L)/sqrt(L), N = 30)
    N = 30
    H = PN.true_Q(L, N)
    cc = PN.constraint(L, N, -1.0)
    from scipy.linalg import null_space, eigh
    Zn = null_space(cc[None, :])
    ev, V = eigh(Zn.T @ H @ Zn)
    a = Zn @ V[:, 0]
    phi = legvander(x, N - 1) * np.sqrt((2 * np.arange(N) + 1) / 2)
    tests.append(("u-space minimiser", (phi @ a) / math.sqrt(L), ev[0]))
    for t in range(6):
        deg = rng.integers(3, 25)
        co = rng.normal(size=deg) / (1 + np.arange(deg)) ** rng.uniform(0, 2)
        gv = np.exp(-1 / np.maximum(1 - x ** 2, 1e-300)) * (legvander(x, deg - 1) @ co)
        e = np.exp(-u / 2)
        # exact projection onto the constraint with a smooth corrector b(u) = bump * e^{-u/2}
        b = np.exp(-1 / np.maximum(1 - x ** 2, 1e-300)) * e
        gv = gv - (np.sum(wu * gv * e) / np.sum(wu * b * e)) * b
        tests.append((f"random bump*poly deg {deg}", gv, None))
    rr = np.linspace(0, R, 3001)
    fact = math.factorial(M)
    for label, gv, ev0 in tests:
        nrm2 = np.sum(wu * gv ** 2)
        l1 = np.sum(wu * np.abs(gv))
        cons = np.sum(wu * gv * np.exp(-u / 2))
        mt = (P * (wu * gv)[:, None]).sum(0)
        gh = fourier(gv, u, wu, rr)
        Pr = np.zeros_like(rr, dtype=complex)
        for k in range(M):
            Qk = np.polyval([float(v) for v in B_Q(B, k)][::-1], rr)
            Pr += (1j) ** k * Qk * mt[k]
        t1 = np.abs(gh - Pr).max()
        t1b = 2 * l1 * (R * L) ** M / fact
        t2 = np.sum(w * mt ** 2)
        lhs3 = (1 + eta) * mt @ Z @ mt
        rhs3 = kap * nrm2 + rho * (c @ mt) ** 2
        # step form and Q (r-space, to r = 400, exact psiR beyond R)
        r2 = np.linspace(0, 400, 40001)
        g2 = np.abs(fourier(gv, u, wu, r2)) ** 2
        idx = np.clip(np.searchsorted(grid, r2, side="right") - 1, 0, len(grid) - 1)
        v = np.where(r2 < R, s[idx], s[-1])
        dr = r2[1] - r2[0]
        tail = (2 * math.pi * nrm2 - 2 * np.trapezoid(g2, dx=dr))
        step = (2 * np.trapezoid(g2 * v, dx=dr) + tail * s[-1]) / (2 * math.pi)
        Qv = (2 * np.trapezoid(g2 * (psiR(r2) - math.log(math.pi)), dx=dr) + tail * (psiR(400) - math.log(math.pi))) / (2 * math.pi)
        print(f"[{label}] |constraint|={abs(cons):.1e}  T1 {t1:.2e} <= {t1b:.2e}: {t1 <= t1b * 1.0001 + 1e-12}  "
              f"T2 {t2 / nrm2:.6f} <= 1: {t2 <= nrm2 * (1 + 1e-9)}  "
              f"T3 {lhs3 / nrm2:.5f} <= {rhs3 / nrm2:.5f}: {lhs3 <= rhs3}  "
              f"T4 step/||g||^2={step / nrm2:+.5f}, Q/||g||^2={Qv / nrm2:+.5f} >= margin {margin:.5f}: "
              f"{min(step, Qv) >= margin * nrm2}" + (f"  (engine lambda {ev0:.5f})" if ev0 is not None else ""))


def B_Q(B, k):
    """real Taylor polynomial Q_k coefficients (low -> high) recomputed from the build's Legendre data."""
    M, L = B["M"], B["L"]
    from flint import fmpq_mat
    P = B["P"]
    T = fmpq_mat(M, M)
    for kk in range(M):
        for j, cf in enumerate(P[kk].coeffs()):
            T[kk, j] = cf
    S = T.inv()
    co = [fmpq(0)] * M
    f = fmpq(1)
    facts = [fmpq(1)]
    for j in range(1, M):
        facts.append(facts[-1] * j)
    for j in range(k % 2, M, 2):
        sg = -1 if ((j - k) // 2) % 2 else 1
        co[j] = sg * L ** j * S[j, k] / facts[j]
    return co


if __name__ == "__main__":
    run(sys.argv[1] if len(sys.argv) > 1 else "A")

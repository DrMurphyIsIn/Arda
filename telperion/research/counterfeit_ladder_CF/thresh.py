"""E's full-window least eigenvalue lambda_min(x) (normalized by ||v||^2), both parity sectors, two
Galerkin bases per sector (Dirichlet: v(+-A) = 0; Neumann: v'(+-A) = 0), M -> large.  float64 (cf_fast
formulas, validated against cf_core at 30 digits)."""
import numpy as np, sys, time
from math import log, pi, sqrt, exp
from cf_fast import coeffs_f, Gsym, exp1

cE, cK = coeffs_f(400)

def build_modes(x, ks, par, nquad=None):
    A = 0.5 * log(x)
    ks = np.array(ks, dtype=float)
    M = len(ks)
    KA = ks[:, None] * np.ones((1, M)); KB = KA.T
    kmax = max(ks.max(), 1.0)
    if nquad is None:
        nquad = int(max(300, 6 * kmax * 2 * A))
    t, w = np.polynomial.legendre.leggauss(nquad)
    ys = A * (t + 1); ws = A * w
    g0 = Gsym(par, KA, KB, A, 0.0)
    psi = 2 * g0 * exp1(4 * A)
    for y, wt in zip(ys, ws):
        psi = psi + wt * (2 * np.exp(-2 * y) * g0 / y - Gsym(par, KA, KB, A, y) / np.sinh(y / 2))
    arch = psi + (log(20) - 2 * log(pi)) * g0
    tu, wu = np.polynomial.legendre.leggauss(max(400, int(4 * kmax * A)))
    us = A * tu; wus = A * wu
    phi = (np.cos if par == 0 else np.sin)(np.outer(ks, us))
    Vp = phi @ (wus * np.exp(us / 2)); Vm = phi @ (wus * np.exp(-us / 2))
    pole = np.outer(Vp, Vm) + np.outer(Vm, Vp)
    pE = np.zeros((M, M)); pK = np.zeros((M, M))
    for n in range(2, int(x) + 1):
        ln = log(n)
        if ln < 2 * A:
            G = Gsym(par, KA, KB, A, ln)
            pE += 2 * cE[n] / sqrt(n) * G
            pK += 2 * cK[n] / sqrt(n) * G
    return A, g0, pole + arch - pE, pole + arch - pK

def lam_min(Q, g0):
    w, U = np.linalg.eigh((g0 + g0.T) / 2)
    keep = w > 1e-12 * w.max()
    T = U[:, keep] / np.sqrt(w[keep])
    S = T.T @ Q @ T
    return np.linalg.eigvalsh((S + S.T) / 2)[0]

def basis(A, M, par, kind):
    if par == 0:
        return [(m + 0.5) * pi / A for m in range(M)] if kind == 'D' else [max(m, 1e-9) * pi / A if m else 1e-6 for m in range(M)]
    else:
        return [(m + 1.0) * pi / A for m in range(M)] if kind == 'D' else [(m + 0.5) * pi / A for m in range(M)]

if __name__ == '__main__':
    xs = [float(a) for a in sys.argv[1].split(',')]
    Ms = [int(a) for a in sys.argv[2].split(',')]
    for x in xs:
        A = 0.5 * log(x)
        for par in (0, 1):
            for kind in ('D', 'N'):
                row = []
                for M in Ms:
                    ks = basis(A, M, par, kind)
                    _, g0, QE, QK = build_modes(x, ks, par)
                    row.append((M, lam_min(QE, g0)))
                print(f"x={x:6.2f} par={'even' if par==0 else 'odd '} basis={kind}: " + "  ".join(f"M={M}:{l:+.6f}" for M, l in row), flush=True)

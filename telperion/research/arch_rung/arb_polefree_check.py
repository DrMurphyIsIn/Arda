"""Arb cross-check of the pole-free margin with the validated gate-0 engine (weil_arb.py).
2026-10-11.  Numerical (arb balls on the assembled matrix; the quadrature truncation is checked by
refinement, not enclosed).  NOT kernel-checked.  conjecture1_proved = False.

The engine assembles the full Weil form (arch + poles + primes) on the orthonormal Legendre basis
g_j(u) = phi_j(u/L)/sqrt(L).  For L <= (log 2)/2 there are no prime terms, and on the pole-free
subspace {int g e^{-u/2} = 0} the pole terms vanish (E6Bridge31 poles_vanish), so the restricted
form IS Q.  The constraint vector c_j = int g_j(u) e^{-u/2} du is computed in arb; the restriction
uses the exact basis v_j = e_j - (c_j / c_0) e_0 (j >= 1) of c^perp and the generalized
eigenproblem (V^T H V, V^T V).

usage: python arb_polefree_check.py L N prec
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import sys
import time
sys.path.insert(0, os.path.expanduser("~/arda-research/gate0/weil_ladder"))
import weil_arb as W
from flint import arb, acb, arb_mat, acb_mat, ctx


def constraint_vec(F, L, ng=80):
    A = F.A                      # N x Np monomial coefficients of phi_j(t)
    N, Np = A.nrows(), A.ncols()
    xs, ws = W._gauss(ng)
    La = arb(L)
    mom = [arb(0)] * Np          # int_{-1}^{1} t^r e^{-L t / 2} dt
    for x, w in zip(xs, ws):
        e = (-La * x / 2).exp() * w
        p = arb(1)
        for r in range(Np):
            mom[r] += e * p
            p *= x
    return [La.sqrt() * sum((A[j, r] * mom[r] for r in range(Np)), arb(0)) for j in range(N)]


def restricted_min(F, c):
    N = F.N
    V = arb_mat(N, N - 1)
    for j in range(1, N):
        V[j, j - 1] = arb(1)
        V[0, j - 1] = -c[j] / c[0]
    Hr = arb_mat(N, N)
    for i in range(N):
        for j in range(N):
            Hr[i, j] = F.H[i, j].real
    Hs = V.transpose() * Hr * V
    Gs = V.transpose() * V
    M = acb_mat(Gs.solve(Hs))
    E = M.eig(multiple=True)
    return min(E, key=lambda e: float(e.real.mid()))


if __name__ == "__main__":
    L = float(sys.argv[1]) if len(sys.argv) > 1 else 0.34657359027997264
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    prec = int(sys.argv[3]) if len(sys.argv) > 3 else 256
    W.set_prec(prec)
    t = time.time()
    F = W.WeilForm(L, N)
    assert not F.plist, "prime terms present"
    c = constraint_vec(F, L)
    lam = restricted_min(F, c)
    print(f"L={L} N={N} prec={prec}: pole-free lambda_min = {lam.real.str(10, radius=True)}"
          f"  (gram defect {F.gram_defect():.1e}, {time.time() - t:.1f}s)")

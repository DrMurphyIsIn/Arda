"""Reproducible deep-dive note: the best-convex-phi linear program (needs scipy; NOT a package dep).

Tests whether a DECOUPLED invariant `x >= phi(mu)` with CONVEX phi can close the tree recursion, via the
Jensen-reduced inductive condition
    G(j,S) = c0 - 11 log(1 + S/(j+1)) + j*phi(S/j) - phi(1/(j+1+S)) >= 0 ,
with c0 = log(621/64), over all integer j>=1 and real S in (0, j].  Maximizes the worst-case slack t over
convex phi (phi(3/23)=0, phi>=0, phi(1)<=c0).  Result: t* ~ -5.2 < 0 -> INFEASIBLE, so no single-variable
convex invariant exists.  Run: `python docs/sibling_coupling_convex_lp.py`.
"""
import math

import numpy as np
from scipy.optimize import linprog


def solve(ngrid=240, jmax=40, sgrid=60):
    c0 = math.log(621 / 64)
    G = np.array(sorted(set(list(np.linspace(0.004, 1.0, ngrid)) + [3 / 23, 1 / 3, 1.0, 1 / 9, 3 / 19])))
    N = len(G)

    def interp(mu):
        r = np.zeros(N)
        if mu <= G[0]:
            r[0] = 1.0; return r
        if mu >= G[-1]:
            r[-1] = 1.0; return r
        i = int(np.searchsorted(G, mu)) - 1
        t = (mu - G[i]) / (G[i + 1] - G[i]); r[i] = 1 - t; r[i + 1] = t; return r

    nv = N + 1  # phi_0..phi_{N-1}, then t
    A, b = [], []
    for j in range(1, jmax + 1):
        for S in np.linspace(1e-3, j, sgrid):
            a = 1 + S / (j + 1); muv = 1 / (j + 1 + S)
            row = np.zeros(nv)
            row[:N] += -j * interp(S / j)
            row[:N] += interp(muv)
            row[N] = 1.0
            A.append(row); b.append(c0 - 11 * math.log(a))
    for i in range(N - 2):                                   # convexity: slopes nondecreasing
        d1 = G[i + 1] - G[i]; d2 = G[i + 2] - G[i + 1]
        row = np.zeros(nv); row[i] += 1 / d1; row[i + 1] += -1 / d1 - 1 / d2; row[i + 2] += 1 / d2
        A.append(row); b.append(0.0)
    for i in range(N):                                        # phi >= 0
        row = np.zeros(nv); row[i] = -1.0; A.append(row); b.append(0.0)
    row = np.zeros(nv); row[:N] = interp(1.0); A.append(row); b.append(c0)   # phi(1) <= c0
    Aeq = [np.concatenate([interp(3 / 23), [0.0]])]; beq = [0.0]              # phi(3/23) = 0
    c = np.zeros(nv); c[N] = -1.0                                            # maximize t
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), A_eq=np.array(Aeq), b_eq=np.array(beq),
                  bounds=[(0, None)] * N + [(None, None)], method="highs")
    return res


if __name__ == "__main__":
    res = solve()
    t = -res.fun if res.success else None
    print("status:", res.message)
    print("max worst-case slack t* =", t)
    print("t* >= 0 -> convex invariant exists (candidate BG proof);  t* < 0 -> INFEASIBLE by |t*|")

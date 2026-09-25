"""zeta's own window form at x = 20, 24, 28: high-precision (mp, dps 80) lam_min on Neumann spans."""
import sys, mpmath as mp, icore
from fractions import Fraction as Fr
for x in (20, 24, 28):
    X = icore.Ctx(False, 80)
    F = icore.Form(X, x, 'zeta')
    res = []
    for par in (0, 1):
        row = []
        for N in (16, 32, 48):
            M, G, kap = icore.build_sector(F, par, N)
            Mm = mp.matrix(N, N)
            for i in range(N):
                for j in range(N):
                    Mm[i, j] = M[i][j] / mp.sqrt(G[i][i] * G[j][j])
            ev = mp.eigsy(Mm, eigvals_only=True)
            row.append('N=%d:%s' % (N, mp.nstr(min(ev), 5)))
        res.append('par%d ' % par + ' '.join(row))
    print('zeta x=%d  ' % x + ' | '.join(res), flush=True)

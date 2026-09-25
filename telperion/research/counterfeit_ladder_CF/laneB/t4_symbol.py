import numpy as np, mpmath as mp, sys
from bcore import *
from npdig import Omega
for x in (20, 24, 28):
    A = np.log(x) / 2
    for kind in ('ZK', 'E'):
        fm = Form(A, kind)
        AL = sum(2 * abs(c) for (_, c, y) in fm.pr)
        t = np.arange(0, 4000, 0.002)
        C = np.zeros_like(t)
        for (_, c, y) in fm.pr: C += 2 * c * np.cos(t * y)
        S = Omega(t, kind) - C
        # T' = last t where S < beta for beta in list
        out = []
        for beta in (0, 0.5, 1.0, 2.0):
            bad = np.where(S < beta)[0]
            out.append('beta=%.1f: T\'=%.2f' % (beta, t[bad[-1]] if len(bad) else 0))
        T0 = 2 * np.pi / np.sqrt(20) * np.exp(AL / 2)
        print('x=%d %s A_L=%.3f  T0(Omega=A_L)~%.0f  min S=%.3f at t=%.2f  ' % (x, kind, AL, T0, S.min(), t[S.argmin()]) + '  '.join(out), flush=True)

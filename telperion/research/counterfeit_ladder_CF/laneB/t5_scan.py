import numpy as np, mpmath as mp, sys
from bcore import *
Ns = (6, 8, 12, 16, 24, 32, 64, 256)
for x in [float(s) for s in sys.argv[1:]]:
    A = mp.log(x)/2
    for kind in ('ZK', 'E'):
        fm = Form(A, kind)
        for par in (0, 1):
            Mr, Gr = real_sector(fm, sector_basis(A, max(Ns), par, 'neumann'), par)
            row = ['%d:%+.2e' % (N, gmin(Mr[:N, :N], Gr[:N, :N])[0]) for N in Ns]
            print('x=%5.1f %-2s par%d ' % (x, kind, par) + ' '.join(row), flush=True)

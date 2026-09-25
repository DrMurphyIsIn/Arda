import numpy as np, mpmath as mp
from bcore import *
for x in (23, 24):
    A = mp.log(x)/2
    for kind in ('ZK','E'):
        f = Form(A, kind)
        M, G = real_sector(f, sector_basis(A, 16, 1), 1)
        e = gmin(M, G)
        print(x, kind, 'odd N=16 lam_min=%.7f' % e[0], flush=True)

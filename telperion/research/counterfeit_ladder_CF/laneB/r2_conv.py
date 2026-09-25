import numpy as np, mpmath as mp
from bcore import *
for x in (18, 19, 19.5, 20, 22, 24, 28):
    A = mp.log(mp.mpf(x))/2; f = Form(A, 'ZK')
    r = {}
    for N in (128, 256):
        M, G = real_sector(f, sector_basis(A, N, 0), 0); r[N] = gmin(M, G)[0]
    print('x=%s ZK even N128=%.9e N256=%.9e delta=%.3e rel=%.2e' % (x, r[128], r[256], r[128]-r[256], (r[128]-r[256])/r[256]), flush=True)

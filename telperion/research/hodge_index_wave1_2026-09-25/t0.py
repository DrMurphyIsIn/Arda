from wf import *
import sys
cz = zeta_coeffs(40)
for N in (8, 12, 16):
    print('zeta x=2 N=%d' % N, lam(2.0, N, GAM['zeta'], [(n, cz[n]) for n in range(2, 3) if cz[n]]))

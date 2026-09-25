import sys; sys.path.insert(0, '../../cf/B')
from bcore import *
import numpy as np, time
for x in [5., 10., 20.]:
    A = float(mp.log(x) / 2)
    for par in [0]:
        kap = sector_basis(A, 16, par)
        t0 = time.time()
        Mz, Gz = real_sector(Form(A, 'zeta'), kap, par)
        MK, GK = real_sector(Form(A, 'ZK'), kap, par)
        ME, GE = real_sector(Form(A, 'E'), kap, par)
        ML = MK - Mz   # L(chi_-20) form (pole cancels, arch/comb additive)
        lz, lK, lE, lL = (gmin(M, Gz)[0] for M in (Mz, MK, ME, ML))
        # E vs ZK defect: pure comb difference
        eD = gmin(ME - MK, Gz)
        print(f'x={x:5.1f} par={par} lmin: zeta={lz:+.3e} Lchi={lL:+.3e} zeta+Lchi(Weyl lb)={lz+lL:+.3e} ZK={lK:+.3e} E={lE:+.3e} | E-ZK spectrum [{eD[0]:+.3e},{eD[-1]:+.3e}]  {time.time()-t0:.0f}s', flush=True)

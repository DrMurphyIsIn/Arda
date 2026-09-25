import numpy as np, mpmath as mp, time
from bcore import *
x = 24; A = mp.log(x)/2
for kind in ('ZK','E'):
    f = Form(A, kind)
    M = 15
    ks = [np.pi*m/float(A) for m in range(-M, M+1)]
    Mc, G = f.complex_mats(ks)
    Mc = (Mc+Mc.conj().T)/2; G=(G+G.conj().T)/2
    L = np.linalg.cholesky(G); Li = np.linalg.inv(L)
    print(kind, 'exp basis M=15', np.linalg.eigvalsh(Li@Mc@Li.conj().T)[0])
    for par in (0,1):
        for bk in ('neumann','dirichlet'):
            t=time.time(); Mr, Gr = real_sector(f, sector_basis(A, 16, par, bk), par)
            print('  par',par,bk,'N=16', gmin(Mr,Gr)[:2], '%.1fs'%(time.time()-t))

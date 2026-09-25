import numpy as np, mpmath as mp, sys
exec(open('t11_schur.py').read().split("print('Y computed")[0].replace("N3 = 8192","N3 = 65536"))
N2 = 128; d = 0.43
Mr, Gr = real_sector(fm, sector_basis(A, N2, par, 'neumann'), par)
dg = np.sqrt(np.diag(Gr)); H = Mr/np.outer(dg, dg)
I = np.arange(N2)
u = np.array([(-1)**i for i in I])/np.sqrt(nrm[I]*Af)
AL = sum(2*abs(c) for (_, c, y) in fm.pr); Ymax = AL + np.pi + 0.01
for N3c in (4096, 8192, 16384, 32768, 65536):
    K = offblock(I, np.arange(N2, N3c)); KK = K@K.T
    Sc = Ymax**2*(Af/np.pi)**2/(N3c-1)
    lam = np.linalg.eigvalsh(H - (KK + 1.05*Sc*np.outer(u, u))/d)[0]
    print(N3c, 'Sc=%.3e  lam=%.4e' % (Sc, lam), flush=True)

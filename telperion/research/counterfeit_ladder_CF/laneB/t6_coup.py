import numpy as np, mpmath as mp, sys, time
from bcore import *
x = float(sys.argv[1]); par = int(sys.argv[2]); N2 = int(sys.argv[3])
A = mp.log(x)/2
fm = Form(A, 'ZK')
t = time.time()
Mr, Gr = real_sector(fm, sector_basis(A, N2, par, 'neumann'), par)
print('built %d in %.0fs' % (N2, time.time()-t))
np.save('M_ZK_x%g_p%d_N%d.npy' % (x, par, N2), Mr)
d = np.sqrt(np.diag(Gr)); Mn = Mr/np.outer(d, d)   # orthonormal basis
for N in (16, 32, 64, 128, 256):
    H = Mn[:N, :N]; e, V = np.linalg.eigh(H); v1 = V[:, 0]
    B = Mn[:N, N:]; Tb = Mn[N:, N:]
    b1 = v1 @ B
    et = np.linalg.eigvalsh(Tb)[0]
    # exact Schur on the finite N2 truncation: lam_min of full vs head
    s = b1 @ np.linalg.solve(Tb - e[0]*np.eye(len(Tb)), b1)
    print('N=%4d lam_head=%.8e  lam_full(N2)=%.8e  |b1|^2=%.3e  b1 T^-1 b1=%.3e  lam_min(tail block)=%.4f  ||B||=%.3f  |b1_n| at n=N,2N: %.2e %.2e' % (
        N, e[0], np.linalg.eigvalsh(Mn)[0], b1 @ b1, s, et, np.linalg.norm(B, 2), abs(b1[0]), abs(b1[min(N, len(b1)-1)])))

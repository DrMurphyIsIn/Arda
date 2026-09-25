import numpy as np
M = np.load('M_ZK_x20_p0_N512.npy'); A = np.log(20)/2
N2 = M.shape[0]; nrm = np.array([2*A] + [A]*(N2-1)); d = np.sqrt(nrm); Mn = M/np.outer(d, d)
np.set_printoptions(linewidth=200, precision=3)
for n in (64, 65, 128, 129, 256, 257, 400, 401):
    row = Mn[:6, n]; print('n=%d  Q(phi_i,phi_n)*n for i<6:' % n, row*n)
e, V = np.linalg.eigh(Mn[:128, :128]); v1 = V[:, 0]
u = np.array([(-1)**i for i in range(128)])/d[:128]  # edge functional phi_i(A)/|phi_i|
print('v1 edge value (normalized f(A)):', v1@u, ' |u|=', np.linalg.norm(u))
b1 = v1 @ Mn[:128, 128:]
for n in (128, 129, 200, 201, 300, 301, 500, 501):
    if n < N2: print('n=%d b1_n*n=%.4e   (v1.u)*w_n guess from row0*n: %.4e' % (n, b1[n-128]*n, Mn[0, n]*n*(v1@u)/u[0]))

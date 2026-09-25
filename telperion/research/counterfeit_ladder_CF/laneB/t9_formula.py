import numpy as np, mpmath as mp
from bcore import *
x = 20; A = mp.log(x)/2; Af = float(A)
fm = Form(A, 'ZK')
M = np.load('M_ZK_x20_p0_N512.npy'); N2 = M.shape[0]
kap = np.array([np.pi*m/Af for m in range(N2)])
J = fm.Ivals(kap).imag
S = np.zeros(N2)
for (_, c, y) in fm.pr: S += c*np.sin(kap*y)
Y = J - 2*S
P = np.array([(-1)**m*np.sinh(Af/2)/(k**2+0.25) for m, k in enumerate(kap)])
err = 0
for i in (0, 1, 5, 50, 300):
    for n in (1, 7, 64, 200, 511):
        if i == n: continue
        q = 2*P[i]*P[n] + (-1)**(i+n)*(kap[i]*Y[i] - kap[n]*Y[n])/(kap[n]**2 - kap[i]**2)
        err = max(err, abs(q - M[i, n]))
print('max |formula - matrix| over sample:', err)
# diagonal
print('Y range over n<512: [%.3f, %.3f]; J(kappa_511)=%.4f (-> -pi/2*2 = %.4f)' % (Y.min(), Y.max(), J[-1], -np.pi))

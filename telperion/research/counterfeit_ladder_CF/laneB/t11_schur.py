import numpy as np, mpmath as mp, sys, time
from bcore import *
x = float(sys.argv[1]); par = int(sys.argv[2])
A = mp.log(x)/2; Af = float(A)
fm = Form(A, 'ZK')
N3 = 8192
kap = np.array([np.pi*(m + (0.5 if par else 0))/Af for m in range(N3)])
t = time.time()
J = np.zeros(N3)
from npdig import cdigamma
# J = Im I(kappa) summed over families (float, npdig) -- matches Form.Ivals
for b0, betas, CL in fm.fams:
    b0f = float(b0)
    v = cdigamma(b0f/2 - 0.5j*kap) - cdigamma(np.array([b0f/2+0j]))[0]
    for b in betas:
        b = float(b); z = b - 1j*kap
        v = v - 2*(np.exp(-b*2*Af)/b - np.exp(-z*2*Af)/z)
    J += v.imag
chk = fm.Ivals(kap[:5]).imag
assert np.max(abs(chk - J[:5])) < 1e-10, (chk, J[:5])
S = np.zeros(N3)
for (_, c, y) in fm.pr: S += c*np.sin(kap*y)
Y = J - 2*S
s = np.sinh(Af/2) if par == 0 else np.cosh(Af/2); sig = 2 if par == 0 else -2
P = np.array([(-1)**m*s/(k**2+0.25) for m, k in enumerate(kap)])
nrm = np.full(N3, Af); 
if par == 0: nrm[0] = 2*Af
def offblock(I, Nn):  # rows I (head indices), cols Nn
    ki = kap[I][:, None]; kn = kap[Nn][None, :]
    sg = ((-1.0)**(I[:, None] + Nn[None, :]))
    Q = sig*P[I][:, None]*P[Nn][None, :] + sg*(ki*Y[I][:, None] - kn*Y[Nn][None, :])/(kn**2 - ki**2)
    return Q/np.sqrt(nrm[I][:, None]*nrm[Nn][None, :])
print('Y computed %.1fs; max|Y|=%.2f' % (time.time()-t, np.max(abs(Y))))
for N2 in (128, 256, 384):
    Mr, Gr = real_sector(fm, sector_basis(A, N2, par, 'neumann'), par)
    d = np.sqrt(np.diag(Gr)); H = Mr/np.outer(d, d)
    lam1 = np.linalg.eigvalsh(H)[0]
    I = np.arange(N2); Nn = np.arange(N2, N3)
    K = offblock(I, Nn)
    KK = K @ K.T
    out = []
    for dd in (0.5, 1, 2, 5, 10):
        out.append('d=%g:%+.3e' % (dd, np.linalg.eigvalsh(H - KK/dd)[0]))
    # 'true' tail block min within [N2, min(N3, N2+1536)) for reference
    print('N2=%d kap=%.0f lam_head=%.6e  Schur lam_min(H - K^T K/d): %s' % (N2, kap[N2], lam1, ' '.join(out)), flush=True)

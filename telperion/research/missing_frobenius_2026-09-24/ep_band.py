"""2-3 mode Dirichlet-cosine band certificates: E (Epstein x^2+5y^2) indefinite, ZK positive, window x < 36
(so every weight c_E(n), n < x, is >= 0: the counterfeit is 'effective' on the whole window)."""
import mpmath as mp, numpy as np
from fractions import Fraction as Fr
from ep_weil import Fam
from ep_core import coeffs, logderiv_weights, chi_m20
from weilmodes import von_mangoldt
mp.mp.dps = 20
def mats(A, kind, ks):
    nmax = int(mp.floor(mp.exp(2*A)))
    if kind == 'ZK':
        lam = von_mangoldt(nmax); w = [lam[n]*(1+chi_m20(n)) if n >= 1 else 0 for n in range(nmax+1)]
    else:
        aE,_,_ = coeffs(nmax); w = logderiv_weights(aE, nmax)
    f1 = Fam(A, 0.5, -mp.log(mp.pi), w=w, pole=True); f2 = Fam(A, 1.5, mp.log(20/mp.pi))
    allk = list(ks) + [-k for k in ks]
    M1,G,C,P,R = f1.matrices(allk); M2,_,_,_,_ = f2.matrices(allk)
    d = len(ks)
    def fold(X, Y=None):
        Z = np.zeros((d,d))
        for i in range(d):
            for j in range(d):
                s = sum((X[a,b] + (Y[a,b] if Y is not None else 0)) for a in (i,i+d) for b in (j,j+d))
                Z[i,j] = float(mp.re(s/4))
        return Z
    return fold(M1, M2), fold(G), fold(P)
def gmin(M, G):
    L = np.linalg.cholesky(G); Li = np.linalg.inv(L); e, W = np.linalg.eigh(Li@M@Li.T); return e[0], Li.T@W[:,0]
if __name__ == "__main__":
    res = []
    for q in sorted(set(Fr(p, d) for d in range(4, 25) for p in range(1, 2*d) if Fr(50,100) < Fr(p,d) < Fr(57,100))):
        A = mp.mpf(q.numerator)/q.denominator*mp.pi
        if mp.exp(2*A) >= 36: continue
        mc = int(15.67*float(A)/np.pi - 0.5)
        for dd in (2, 3):
            for lo in range(mc-dd, mc+2):
                ks = [mp.pi*(m+mp.mpf(1)/2)/A for m in range(lo, lo+dd)]
                MK, G, PK = mats(A, 'ZK', ks); ME, _, _ = mats(A, 'E', ks)
                eK,_ = gmin(MK, G); eKn,_ = gmin(MK-PK, G); eE, v = gmin(ME, G)
                res.append((min(eKn, -eE), str(q), float(mp.exp(2*A)), dd, lo, [float(k) for k in ks], eK, eKn, eE, v))
    res.sort(key=lambda r: -r[0])
    for r in res[:8]:
        print('sep=%.4f A=%sπ x=%.2f d=%d m0=%d k=%s  ZK=%.4f ZK(no pole)=%.4f  E=%.4f  vE=%s' % (r[0], r[1], r[2], r[3], r[4], ['%.3f'%k for k in r[5]], r[6], r[7], r[8], np.round(r[9]/np.max(abs(r[9])),3)))

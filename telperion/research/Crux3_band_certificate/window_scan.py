"""Scan windows A = q pi (q rational, denominators <= 40) for the best 2-3 mode Dirichlet-cosine band
separating zeta (Weil form PD, pole dropped) from Davenport-Heilbronn (indefinite)."""
import mpmath as mp, numpy as np, sys
from fractions import Fraction as Fr
from weilfreq import FWindow
mp.mp.dps = 20

def even_mats(W, ks):
    allk = list(ks) + [-k for k in ks]
    M, G, C, P, R = W.matrices(allk)
    d = len(ks)
    def fold(X):
        Y = np.zeros((d, d))
        for i in range(d):
            for j in range(d):
                Y[i, j] = float(mp.re((X[i, j] + X[i, j + d] + X[i + d, j] + X[i + d, j + d]) / 4))
        return Y
    return fold(M), fold(G), fold(C), fold(P), fold(R)

def gen_min(Mn, Gn):
    import scipy.linalg as sl
    return sl.eigh(Mn, Gn)

gam0 = 85.699348

if __name__ == "__main__":
    qs = sorted(set(Fr(p, den) for den in range(2, 41) for p in range(1, 2*den) if Fr(0.60) < Fr(p, den) < Fr(0.76)))
    out = []
    for q in qs:
        A = mp.mpf(q.numerator) / q.denominator * mp.pi
        Wz = FWindow(A, 'zeta'); Wd = FWindow(A, 'dh')
        mc = int(round((gam0 * 2 * float(A) / np.pi - 1) / 2))
        for d in (2, 3):
            for lo in range(mc - d, mc + 2):
                ms = list(range(lo, lo + d))
                ks = [mp.mpf(2*m+1) / (2 * mp.mpf(q.numerator) / q.denominator) for m in ms]
                Mz, G, Cz, Pz, Rz = even_mats(Wz, ks)
                Md, _, _, _, _ = even_mats(Wd, ks)
                ez, _ = gen_min(Mz - Pz, G); ed, _ = gen_min(Md, G)
                out.append((min(ez[0], -ed[0]), str(q), float(A), float(mp.exp(2*A)), d, ms, [float(k) for k in ks], ez[0], ed[0]))
    out.sort(key=lambda t: -t[0])
    for o in out[:25]:
        print('sep %.4f q=%s A=%.4f x=%.2f d=%d m=%s kap=%s zeta(no pole)=%.4f D=%.4f' % (o[0], o[1], o[2], o[3], o[4], o[5], ['%.4f' % k for k in o[6]], o[7], o[8]))

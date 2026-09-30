"""Purity horizon: how far does (Euler product locality + local purity |alpha_p|=1) carry window Weil positivity?
   Q_c = Pole + Arch - sum_n c(n)/sqrt(n) * P_n,  P_n[m,l] = int (phi_m(u+y)phi_l(u)+phi_l(u+y)phi_m(u)) du, y=log n.
   c(p^k) = log p * sum_j alpha_j^k with local Satake data at p (the output of a Castelnuovo-Severi/Eichler-Shimura argument)."""
import sys, numpy as np, mpmath as mp
sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import Form, sector_basis, real_sector, gmin, weights_mp, mangoldt, chi_m20
from functools import lru_cache
GL = np.polynomial.legendre.leggauss(200)

def phi(k, par, u):
    return np.cos(k*u) if par == 0 else np.sin(k*u)

def Pn(A, kap, par, y):
    a, b = -A, A - y
    t, w = GL; u = (b-a)/2*t + (b+a)/2; w = w*(b-a)/2
    F1 = np.array([phi(k, par, u+y) for k in kap]); F0 = np.array([phi(k, par, u) for k in kap])
    S = (F1*w) @ F0.T
    return S + S.T   # h(y)+h(-y) contribution for real g

class Setup:
    def __init__(self, x, kind, N, par, bas='neumann'):
        A = 0.5*np.log(x); self.A = A
        f = Form(mp.mpf(A), kind)
        kap = sector_basis(A, N, par, bas)
        M, G, P = real_sector(f, kap, par, parts=True)
        self.M0 = P['pole'] + P['arch']; self.Arch = P['arch']; self.G = G; self.Mfull = M
        self.nmax = f.nmax
        self.ns = list(range(2, f.nmax+1))
        self.Pm = {n: Pn(A, kap, par, np.log(n)) for n in self.ns}
        # validate: reconstruct comb from this kind's weights
        w = weights_mp(kind, f.nmax)
        C = sum(float(w[n])/np.sqrt(n)*self.Pm[n] for n in self.ns)
        self.valerr = np.max(np.abs(C - P['comb']))/max(1, np.max(np.abs(P['comb'])))
    def M(self, c):  # c: dict n->c(n)
        return self.M0 - sum(c.get(n, 0.0)/np.sqrt(n)*self.Pm[n] for n in self.ns)
    def lmin(self, c):
        return gmin(self.M(c), self.G)[0]

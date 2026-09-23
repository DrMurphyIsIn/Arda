# Independent discretization of the window Weil form (orthonormal Legendre basis on [-a, a],
# a = (1/2) log x, double precision, direct autocorrelation quadrature).  Written in the referee
# (negative-control) lane of this workflow; copied verbatim below this header for reproducibility.
# Used only as a cross-check of the mpmath cosine/sine Galerkin code in wpw.py.

import numpy as np
from numpy.polynomial import legendre as L
from scipy.special import digamma
import sys

def vonmangoldt_zeta(M):
    lam = np.zeros(M+1)
    for n in range(2, M+1):
        m = n; p = None
        for q in range(2, n+1):
            if m % q == 0:
                p = q; break
        while m % p == 0: m //= p
        if m == 1: lam[n] = np.log(p)
    return lam

KAP = (np.sqrt(10-2*np.sqrt(5))-2)/(np.sqrt(5)-1)
def lam_dh(M):
    a = np.zeros(M+1)
    for n in range(1, M+1):
        a[n] = {1:1.0, 2:KAP, 3:-KAP, 4:-1.0, 0:0.0}[n % 5]
    Ld = np.zeros(M+1)
    for n in range(2, M+1):
        s = a[n]*np.log(n)
        for d in range(2, n):
            if n % d == 0: s -= Ld[d]*a[n//d]
        Ld[n] = s
    return Ld

def build(lam2, N, kind='zeta', pole_t=1.0):
    a = 0.5*np.log(lam2)
    xg, wg = L.leggauss(N+8)
    def phis(x):
        # orthonormal Legendre on [-a,a]
        V = L.legvander(x/a, N-1)
        return V*np.sqrt((2*np.arange(N)+1)/(2*a))
    def gmat(y):
        lo, hi = y-a, a
        x = 0.5*(hi-lo)*xg + 0.5*(hi+lo); w = 0.5*(hi-lo)*wg
        A = phis(x); B = phis(x-y)
        G = (A*w[:,None]).T @ B
        return 0.5*(G+G.T)
    G0 = gmat(0.0)
    if kind == 'zeta':
        c0 = digamma(0.25)-np.log(np.pi); K = lambda y: 2*np.exp(-y/2)/(-np.expm1(-2*y))
        Lam = vonmangoldt_zeta(int(lam2)+1)
    else:
        c0 = digamma(0.75)+np.log(5/np.pi); K = lambda y: 2*np.exp(-1.5*y)/(-np.expm1(-2*y))
        Lam = lam_dh(int(lam2)+1)
    # archimedean
    yq, wq = L.leggauss(300)
    yy = a*(yq+1); ww = a*wq
    Arch = np.zeros((N,N))
    for y, w in zip(yy, ww):
        Arch += w*K(y)*(G0-gmat(y))
    from scipy.integrate import quad
    tail = quad(K, 2*a, np.inf)[0]
    Arch += tail*G0
    H = c0*G0 + Arch
    for n in range(2, len(Lam)):
        if n < lam2 and Lam[n] != 0:
            H -= 2*Lam[n]/np.sqrt(n)*gmat(np.log(n))
    P = np.zeros((N,N))
    if kind == 'zeta':
        Av = (phis(a*xg)*(a*wg*np.exp(-a*xg/2))[:,None]).sum(0)
        Bv = (phis(a*xg)*(a*wg*np.exp(a*xg/2))[:,None]).sum(0)
        P = np.outer(Av,Bv)+np.outer(Bv,Av)
    return H, P, phis, a

if __name__ == '__main__':
    for lam2 in [3,5,7]:
        H,P,phis,a = build(lam2, 24)
        ev = np.linalg.eigvalsh(H)
        evq = np.linalg.eigvalsh(H+P)
        print('zeta lam2',lam2,'H eig',ev[:3],'Q eig',evq[:2])

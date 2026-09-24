"""Numerical top eigenvalue of the compressed prime comb P_{a'} = sum_n (c_n/2)(S_n + S_n^*) on L^2(-a',a')
(piecewise-constant Galerkin, exact cell overlaps) vs the path-graph bound A' and the Fejer value."""
import numpy as np, math, sys
def pp(n):
    m=n; p=None
    for q in range(2,n+1):
        if m%q==0: p=q; break
    while m%p==0: m//=p
    return p if m==1 else None
def comb(a):
    out=[]
    for n in range(2, int(math.exp(2*a))+2):
        p=pp(n)
        if p and math.log(n) < 2*a: out.append((n, 2*math.log(p)/math.sqrt(n), math.log(n)))
    return out
def Pmat(a, ap, K):
    edges = np.linspace(-ap, ap, K+1); h = edges[1]-edges[0]
    P = np.zeros((K,K))
    for (n,c,tau) in comb(a):
        # <S_tau e_j, e_i> = (1/h) |cell_i ∩ (cell_j - tau)|
        lo_i = edges[:-1][:,None]; hi_i = edges[1:][:,None]
        lo_j = edges[:-1][None,:]-tau; hi_j = edges[1:][None,:]-tau
        ov = np.clip(np.minimum(hi_i,hi_j)-np.maximum(lo_i,lo_j), 0, None)/h
        P += (c/2)*(ov + ov.T)
    return P
if __name__ == '__main__':
  for (a, eps) in [(0.97265625, 0.34), (1.0390625, 0.34), (1.19921875, 0.34), (1.19921875, 0.0), (1.4, 0.34)]:
    ap = a + eps
    lam = np.linalg.eigvalsh(Pmat(a, ap, 1600))[-1]
    Ap = sum(c*math.cos(math.pi/(math.floor(2*ap/tau)+2)) for (n,c,tau) in comb(a))
    AL = sum(c for (n,c,tau) in comb(a))
    At = sum(c*(1-tau/(2*ap)) for (n,c,tau) in comb(a))
    print("a=%.4f a'=%.3f: A_L=%.3f  path-bound A'=%.3f  numerical lam_max(P)=%.3f  Fejer(a')=%.3f   T'=%.0f  T_num=%.0f" % (a, ap, AL, Ap, lam, At, 2*math.pi*math.exp(Ap), 2*math.pi*math.exp(lam)))

"""Cross-check the FWindow-based degree-2 matrix (ep_weil.Fam) against direct quadrature for f = cos(k u) 1_[-A,A]."""
import mpmath as mp
from ep_weil import Fam
from ep_core import coeffs, logderiv_weights
mp.mp.dps = 20
A = mp.mpf('1.2'); k = mp.pi * 3 / A
nmax = int(mp.floor(mp.exp(2*A))); aE,_,_ = coeffs(nmax); w = logderiv_weights(aE, nmax)
f1 = Fam(A, 0.5, -mp.log(mp.pi), w=w, pole=True); f2 = Fam(A, 1.5, mp.log(20/mp.pi))
ks = [k, -k]
M1,G,_,_,_ = f1.matrices(ks); M2,_,_,_,_ = f2.matrices(ks)
# f = cos(ku) = (e^{iku}+e^{-iku})/2 -> coefficient vector (1/2,1/2)
Qmodel = sum((M1[i,j]+M2[i,j])/4 for i in range(2) for j in range(2))
f = lambda u: mp.cos(k*u) if abs(u) < A else mp.mpf(0)
def g(y):
    y = abs(y)
    return mp.quad(lambda v: f(v)*f(v-y), [y-A, A]) if y < 2*A else mp.mpf(0)
def F(z): return 2*mp.quad(lambda u: f(u)*mp.cos(z*u), [0, A])
def arch_family(beta0, c0):
    g0 = g(0); W = lambda u: 2*mp.exp(-beta0*u)/(1-mp.exp(-2*u))
    return c0*g0 + mp.quad(lambda u: g0*mp.exp(-2*u)/u - W(u)*g(u), [0, A, 2*A]) + mp.quad(lambda u: g0*mp.exp(-2*u)/u, [2*A, mp.inf])
h = mp.mpc(0, .5)
Qq = F(h)**2 + F(-h)**2 + arch_family(mp.mpf(1)/2, -mp.log(mp.pi)) + arch_family(mp.mpf(3)/2, mp.log(20/mp.pi)) - sum(w[n]/mp.sqrt(n)*2*g(mp.log(n)) for n in range(2, nmax+1))
print('model', mp.nstr(Qmodel, 12), ' quadrature', mp.nstr(Qq, 12))

"""S7c numerical checks [N-here, float64/mpmath, NOT certified].

Bridge: sum_k |P^ P th(g) e_k|^2 = (1/2pi) int hsq g r * Nnorm r dr.
Kernel  M(w,u) = int g(x) e^{x/2} 1{e^x|u|>1} cos(2 pi e^x u w) dx.
Claims checked:
 (R) row identity: (F P V y)(w) = int M(w,u) y(u) du   (y even, V y(v) = int g(x) e^{-x/2} y(e^{-x} v) dx)
 (H) H_w(s) := M(w,e^s) e^{s/2};  with damping e^{-eps w e^{x+s}}:
     Hhat(r) = int H(s) e^{irs} ds = paperFT g (-r) * w^{-1/2-ir} * PhiE(r,eps,w)/2
 (P) int_R |M^eps(w,u)|^2 du = (1/4pi) int hsq g (r) |PhiE(r,eps,w)|^2 / w dr
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np, mpmath as mp
from scipy.integrate import quad

def g(x):  # complex, smooth, effectively supported in [-2.5, 2.5]
    return np.exp(-4*x*x)*(1+0.3*x)*np.exp(0.5j*x)
XS = np.linspace(-2.6, 2.6, 4001)
def cquad(f, a, b, **kw):
    re = quad(lambda t: np.real(f(t)), a, b, limit=2000, **kw)[0]
    im = quad(lambda t: np.imag(f(t)), a, b, limit=2000, **kw)[0]
    return re + 1j*im
def paperFT(r):
    return cquad(lambda u: g(u)*np.exp(1j*r*u), -2.6, 2.6)

def PhiE(r, eps, a):
    z = mp.mpf(0.5) + 1j*mp.mpf(r)
    tot = 0
    for b in (eps - 2j*mp.pi, eps + 2j*mp.pi):
        b = mp.mpc(b)
        tot += b**(-z) * mp.gammainc(z, b*a)
    return complex(tot)

# sanity: PhiE closed form vs direct quadrature
r, eps, a = 0.7, 0.5, 1.3
direct = cquad(lambda s: s**(-0.5+1j*r)*2*np.cos(2*np.pi*s)*np.exp(-eps*s), a, 80)
print("PhiE closed vs direct:", PhiE(r, eps, a), direct)
print("PhiE(-r) vs conj PhiE(r):", PhiE(-r, eps, a), np.conj(PhiE(r, eps, a)))

# (R) row identity, y(u) = exp(-u^2)
def y(u): return np.exp(-u*u)
def Vy(v):
    return np.trapz(g(XS)*np.exp(-XS/2)*y(np.exp(-XS)*v), XS)
def M(w, u, eps=0.0):
    ex = np.exp(XS)
    ind = (ex*abs(u) > 1).astype(float)
    return np.trapz(g(XS)*np.exp(XS/2)*ind*np.cos(2*np.pi*ex*u*w)*np.exp(-eps*w*ex*abs(u)), XS)
for w in (1.2, 2.0):
    vs = np.linspace(1, 12, 60001)
    vals = np.array([Vy(v) for v in vs])
    lhs = 2*np.trapz(np.cos(2*np.pi*vs*w)*vals, vs)    # even: int_{|v|>1} e^{-2pi i v w} = 2 int_1^inf cos
    us = np.linspace(-12, 12, 120001)
    rhs = np.trapz(np.array([M(w, u) for u in us])*y(us), us)
    print(f"(R) w={w}: F P V y (w) = {lhs:.10f}   int M y = {rhs:.10f}")

# (H) and (P) with damping
for (w, eps) in ((1.5, 0.5), (1.2, 0.3)):
    ss = np.linspace(-2.6, 9.0, 40001)
    def Hs(s):
        t = XS + s
        ind = (t > 0).astype(float)
        return np.trapz(g(XS)*np.exp(t/2)*ind*np.cos(2*np.pi*w*np.exp(t))*np.exp(-eps*w*np.exp(t)), XS)
    Hv = np.array([Hs(s) for s in ss])
    for r in (0.0, 1.3, -2.1):
        hhat = np.trapz(Hv*np.exp(1j*r*ss), ss)
        form = paperFT(-r) * w**(-0.5-1j*r) * PhiE(r, eps, w)/2
        print(f"(H) w={w} eps={eps} r={r}: Hhat={hhat:.9f}  formula={form:.9f}")
    lhsP = 2*np.trapz(abs(Hv)**2, ss)
    rs = np.linspace(-40, 40, 1601)
    integrand = np.array([abs(paperFT(rr))**2 * abs(PhiE(rr, eps, w))**2 / w for rr in rs])
    rhsP = np.trapz(integrand, rs)/(4*np.pi)
    print(f"(P) w={w} eps={eps}: int|M|^2 du = {lhsP:.10f}   (1/4pi) int hsq |PhiE|^2/w = {rhsP:.10f}")

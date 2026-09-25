"""Epstein zeta of Q1 = x^2+5y^2 (disc -20, h=2) vs Dedekind zeta of K=Q(sqrt-5).
E(s) := (1/2) sum' Q1(x,y)^{-s} = zeta(s) L(s,chi_-20) + L(s,chi_-4) L(s,chi_5)   (a(1)=2 in this normalization)
ZK(s) := zeta(s) L(s,chi_-20)
G(s)  := L(s,chi_-4) L(s,chi_5)   (genus-character L-function = the 'other' Euler product)
Completed: Lam(s) = (sqrt20/(2pi))^s Gamma(s) * F(s), real on the critical line (root numbers +1)."""
import mpmath as mp
mp.mp.dps = 20

def kron(D, n):
    # Kronecker symbol (D/n) for fundamental D, n>0 small
    from sympy import jacobi_symbol
    return None

def chi_tab(mod, f):
    return [f(n) for n in range(mod)]

def leg5(n):
    r = n % 5
    return {0:0,1:1,4:1,2:-1,3:-1}[r]
def chi_m4(n):
    r = n % 4
    return {0:0,2:0,1:1,3:-1}[r]
def chi_m20(n):
    # (-20/n) = chi_-4(n) * (5/n)  (since -20 = -4*5, (5/n)=leg5 for odd n by reciprocity)
    return chi_m4(n) * leg5(n)

C5 = chi_tab(5, leg5); C4 = chi_tab(4, chi_m4); C20 = chi_tab(20, chi_m20)

def L(s, tab):
    return mp.dirichlet(s, tab)

def parts(s):
    z = mp.zeta(s); l20 = L(s, C20); l4 = L(s, C4); l5 = L(s, C5)
    return z*l20, l4*l5

def gam(s):
    return (mp.sqrt(20)/(2*mp.pi))**s * mp.gamma(s)

def theta(T):
    T = mp.mpf(T)
    return T*mp.log(mp.sqrt(20)/(2*mp.pi)) + mp.im(mp.loggamma(mp.mpc(0.5, T)))

def coeffs(nmax):
    """a(n) for E (normalized a(1)=1 i.e. E/2), aK(n) for ZK."""
    aK = [0]*(nmax+1); aG = [0]*(nmax+1)
    for n in range(1, nmax+1):
        for m in range(1, n+1):
            if n % m == 0:
                aK[n] += chi_m20(m)
                aG[n] += chi_m4(m)*leg5(n//m)
    aE = [ (aK[n]+aG[n]) for n in range(nmax+1)]
    return aE, aK, aG

def logderiv_weights(a, nmax):
    """c(n): -F'/F = sum c(n) n^-s, from a(n) log n = sum_{d|n} c(d) a(n/d), a(1) normalized to 1."""
    a1 = mp.mpf(a[1])
    b = [mp.mpf(x)/a1 for x in a]
    c = [mp.mpf(0)]*(nmax+1)
    for n in range(2, nmax+1):
        acc = b[n]*mp.log(n)
        for d in range(2, n):
            if n % d == 0:
                acc -= c[d]*b[n//d]
        c[n] = acc
    return c

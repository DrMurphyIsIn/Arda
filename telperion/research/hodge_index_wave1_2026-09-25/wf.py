"""Independent Weil-form implementation (no bcore). Basis: (1-v^2)^2 P_m(v), v=u/A, parity sectors.
Q(f)=pole + (1/2pi) int |F(t)|^2 Phi(t) dt - sum c(n)/sqrt n (g(log n)+g(-log n)).
Arch via direct t-quadrature of Re digamma; primes via exact autocorrelation quadrature."""
import numpy as np, mpmath as mp
POW = 3
TFAC = 30
from numpy.polynomial import legendre as Lg

def basis_vals(v, N, par):
    degs = [2*m + par for m in range(N)]
    out = []
    for d in degs:
        c = np.zeros(d+1); c[d] = 1
        out.append((1 - v**2)**POW * Lg.legval(v, c))
    return np.array(out)  # N x len(v)

_cache = {}
def rpsi(z):
    key = (z.real.tobytes() if hasattr(z.real,'tobytes') else z.real, z.imag.tobytes())
    if key not in _cache:
        _cache[key] = np.array([float(mp.re(mp.digamma(mp.mpc(a, b)))) for a, b in zip(np.broadcast_to(z.real, z.shape), z.imag)])
    return _cache[key]

def Phi(t, gam):
    # gam: list of (shift b with Gamma_R(s+b)), plus constant logq - n*log pi
    fams, const = gam
    out = np.full_like(t, const)
    for b in fams:
        out += rpsi((0.5 + b)/2 + 0.5j*t)
    return out

GAM = {'zeta': ([0], -np.log(np.pi)),
       'ZK': ([0, 1], np.log(20) - 2*np.log(np.pi)),
       'LG': ([0, 1], np.log(20) - 2*np.log(np.pi)),
       'D': ([1], np.log(5) - np.log(np.pi))}

def build(A, N, par, gam, coeffs, pole=True, Mu=600, T=None):
    xg, wg = Lg.leggauss(Mu)
    u = A*xg; wu = A*wg
    B = basis_vals(xg, N, par)
    G = (B*wu) @ B.T
    # pole
    Pm = (B*wu) @ np.exp(-u/2); Pp = (B*wu) @ np.exp(u/2)
    Mp = np.outer(Pm, Pp) + np.outer(Pp, Pm)
    # arch: t in [0, T], integrand even in t
    if T is None: T = TFAC*(2*N+4)/A + 200
    edges = np.linspace(0, T, int(T/2)+2)
    tn, tw = Lg.leggauss(12)
    ts = ((edges[1:, None]-edges[:-1, None])/2*tn[None, :] + (edges[1:, None]+edges[:-1, None])/2).ravel()
    tws = ((edges[1:, None]-edges[:-1, None])/2*tw[None, :]).ravel()
    Mu2 = int(max(400, 0.6*T*A))
    x2, w2 = Lg.leggauss(Mu2); u2 = A*x2; wu2 = A*w2; B2 = basis_vals(x2, N, par)
    F = np.zeros((N, len(ts)))
    for i0 in range(0, len(ts), 4000):
        tt = ts[i0:i0+4000]
        trig = np.cos(np.outer(u2, tt)) if par == 0 else np.sin(np.outer(u2, tt))
        F[:, i0:i0+4000] = (B2*wu2) @ trig
    ph = Phi(ts, gam)
    Ma = 2 * (F*(tws*ph)) @ F.T / (2*np.pi)
    # primes
    Mc = np.zeros((N, N))
    for n, c in coeffs:
        y = np.log(n)
        if y >= 2*A or c == 0: continue
        # g(y)=int f_j(v) f_k(v-y) dv, v in [-A+y, A]
        a, b = -A + y, A
        vv = (b-a)/2*xg + (a+b)/2; ww = (b-a)/2*wg
        Bj = basis_vals(vv/A, N, par); Bk = basis_vals((vv-y)/A, N, par)
        g = (Bj*ww) @ Bk.T
        Mc += c/np.sqrt(n) * (g + g.T)
    M = Ma - Mc + (Mp if pole else 0)
    return M, G, dict(pole=Mp, arch=Ma, comb=Mc)

def lmin(M, G, vec=False):
    L = np.linalg.cholesky((G+G.T)/2); Li = np.linalg.inv(L)
    e, W = np.linalg.eigh(Li @ ((M+M.T)/2) @ Li.T)
    return (e, Li.T @ W) if vec else e[0]

def lam(x, N, gam, coeffs, pole=True):
    A = np.log(x)/2
    return min(lmin(*build(A, N, p, gam, coeffs, pole)[:2]) for p in (0, 1))

# ---- independent coefficients ----
def reps_E(nmax):
    """a(n) = #{(x,y): x^2+5y^2=n}/2"""
    a = np.zeros(nmax+1)
    r = int(np.sqrt(nmax))+1
    for x in range(-r, r+1):
        for y in range(-r, r+1):
            n = x*x + 5*y*y
            if 1 <= n <= nmax: a[n] += 1
    return a/2

def vonmangoldt_coeffs(a, nmax):
    """c(n) with -F'/F = sum c(n) n^-s for F = sum a(n) n^-s, a(1)=1."""
    a = [mp.mpf(v) for v in a]; c = [mp.mpf(0)]*(nmax+1)
    for n in range(2, nmax+1):
        acc = a[n]*mp.log(n)
        for d in range(2, n):
            if n % d == 0: acc -= c[d]*a[n//d]
        c[n] = acc
    return c

def zeta_coeffs(nmax):
    c = [0.0]*(nmax+1)
    for n in range(2, nmax+1):
        for p in range(2, n+1):
            if n % p == 0: break
        m = n
        while m % p == 0: m //= p
        if m == 1: c[n] = float(np.log(p))
    return c

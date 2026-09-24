"""Direct (zero-free) evaluation of the S-local Weil form on the probe g = Phi' 1_[-L/2,L/2]:
   Q_S(g) = pole + arch - 2 sum_{n <= x, n S-unit} Lambda(n) n^{-1/2} h(log n)
   pole = 2 A B (A = int g e^{u/2}, B = int g e^{-u/2});
   arch = ||g||^2 CL + int_0^L (||g||^2 - h(u)) W(u) du,  W = e^{u/2}/sinh u,
   CL = -log pi + int_0^L (e^{-2u}/u - W(u)) du + E1(2L)      (wpw.build conventions, validated)
Cross-checks the zero-side value Q(g) = sum |tau^(gamma)|^2 used in probe_fast.py."""
import sys, json
import mpmath as mp
mp.mp.dps = 40

def dPhi(u, M=10):
    u = mp.mpf(u); sgn = 1 if u >= 0 else -1; v = abs(u)
    e2 = mp.exp(2 * v); s = mp.mpf(0)
    for n in range(1, M + 1):
        A = 4 * mp.pi**2 * n**4 * mp.exp(4.5 * v) - 6 * mp.pi * n**2 * mp.exp(2.5 * v)
        dA = 18 * mp.pi**2 * n**4 * mp.exp(4.5 * v) - 15 * mp.pi * n**2 * mp.exp(2.5 * v)
        s += (dA - A * 2 * mp.pi * n * n * e2) * mp.exp(-mp.pi * n * n * e2)
    return sgn * s

def gl_nodes(a, b, n):
    xs, ws = mp.gauss_legendre_nodes(n) if hasattr(mp, 'gauss_legendre_nodes') else (None, None)
    return xs, ws

def make_grid(a, b, panels, deg):
    from mpmath.calculus.quadrature import GaussLegendre
    g = GaussLegendre(mp.mp); base = g.calc_nodes(deg, mp.mp.prec)
    h = (b - a) / panels; out = []
    for p in range(panels):
        c = a + p * h + h / 2; r = h / 2
        for (xx, ww) in base: out.append((c + r * xx, r * ww))
    return out

def evaluate(x, S_primes, panels=24, deg=6):
    x = mp.mpf(x); L = mp.log(x); a = L / 2
    V = make_grid(-a, a, 2 * panels, deg)
    gv = [(v, w, dPhi(v)) for (v, w) in V]
    nrm = sum(w * d * d for (v, w, d) in gv)
    A = sum(w * d * mp.exp(v / 2) for (v, w, d) in gv)
    B = sum(w * d * mp.exp(-v / 2) for (v, w, d) in gv)
    def h(u):
        lo, hi = u - a, a
        if lo >= hi: return mp.mpf(0)
        G = make_grid(lo, hi, panels, deg)
        return sum(w * dPhi(v) * dPhi(v - u) for (v, w) in G)
    W = lambda u: mp.exp(u / 2) / mp.sinh(u)
    U = make_grid(mp.mpf(0), L, panels, deg)
    arch_int = sum(w * (nrm - h(u)) * W(u) for (u, w) in U)
    Cfix = sum(w * (mp.exp(-2 * u) / u - W(u)) for (u, w) in U)
    CL = -mp.log(mp.pi) + Cfix + mp.e1(2 * L)
    arch = nrm * CL + arch_int
    pole = 2 * A * B
    primes = mp.mpf(0); primes_full = mp.mpf(0)
    for n in range(2, int(mp.floor(x)) + 1):
        # Lambda(n)
        m = n; p = None
        for d in range(2, n + 1):
            if m % d == 0: p = d; break
        while m % p == 0: m //= p
        if m != 1: continue
        term = 2 * mp.log(p) / mp.sqrt(n) * h(mp.log(n))
        primes_full += term
        if p in S_primes: primes += term
    return dict(x=mp.nstr(x, 8), norm2=mp.nstr(nrm, 10), pole=mp.nstr(pole, 12), arch=mp.nstr(arch, 12),
                Q_full=mp.nstr(pole + arch - primes_full, 8), Q_S=mp.nstr(pole + arch - primes, 8))

if __name__ == '__main__':
    for (x, S) in [(3.3, [2]), (3.05, [2]), (5.3, [2, 3]), (5.05, [2, 3]), (7.3, [2, 3, 5])]:
        r = evaluate(x, S); r['S'] = S
        print(json.dumps(r), flush=True)

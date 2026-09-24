"""Near-radical probe for the S-local no-go.

g = Phi' * 1_[-L/2, L/2]   (Phi = Polya kernel, Phi^ = Xi;  L = log x)
Explicit formula: g^(gamma_rho) = -tau^(gamma_rho), tau = Phi' 1_{|u|>L/2}  (since (Phi')^ = -i z Xi(z) vanishes at zeros)
=> Q(g) = sum_rho |tau^(gamma)|^2 (under RH; unconditionally |.| <= sum |tau^(g_rho)||tau^(conj g_rho)|).
S-local deficit on window x < q^2 (q = first missing prime):
   Q_S(g) = Q(g) + 2 sum_{missing n <= x} Lambda(n) n^{-1/2} h_g(log n),   h_g(a) = int g(v) g(v-a) dv < 0 for a > L/2.
"""
import json, sys
import mpmath as mp

mp.mp.dps = 40
ZEROS = [mp.mpf(z) for z in json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'zeros2000.json')))]

def Phi(u, M=12):
    u = abs(mp.mpf(u))
    e2 = mp.exp(2 * u)
    s = mp.mpf(0)
    for n in range(1, M + 1):
        s += (4 * mp.pi**2 * n**4 * mp.exp(4.5 * u) - 6 * mp.pi * n**2 * mp.exp(2.5 * u)) * mp.exp(-mp.pi * n * n * e2)
    return s

def dPhi(u, M=12):
    sgn = 1 if u >= 0 else -1
    v = abs(mp.mpf(u))
    e2 = mp.exp(2 * v)
    s = mp.mpf(0)
    for n in range(1, M + 1):
        A = 4 * mp.pi**2 * n**4 * mp.exp(4.5 * v) - 6 * mp.pi * n**2 * mp.exp(2.5 * v)
        dA = 18 * mp.pi**2 * n**4 * mp.exp(4.5 * v) - 15 * mp.pi * n**2 * mp.exp(2.5 * v)
        E = mp.exp(-mp.pi * n * n * e2)
        s += (dA - A * 2 * mp.pi * n * n * e2) * E
    return sgn * s

def tau_hat(z, L):
    # tau^(z) = 2i int_{L/2}^inf Phi'(v) sin(z v) dv
    f = lambda v: dPhi(v) * mp.sin(z * v)
    a = L / 2
    I = mp.quad(f, [a, a + 0.5, a + 1.5, a + 4])
    return 2j * I

def Q_zero_sum(L, nz=2000):
    tot = mp.mpf(0)
    for g in ZEROS[:nz]:
        t = tau_hat(g, L)
        tot += 2 * abs(t) ** 2          # zeros at +gamma and -gamma
    return tot

def h_g(a, L):
    lo, hi = a - L / 2, L / 2
    if lo >= hi:
        return mp.mpf(0)
    f = lambda v: dPhi(v) * dPhi(v - a)
    return mp.quad(f, mp.linspace(lo, hi, 9))

def norm2(L):
    return 2 * mp.quad(lambda v: dPhi(v) ** 2, mp.linspace(0, L / 2, 9))

if __name__ == '__main__':
    print('check Xi(0)=int Phi =', mp.nstr(2 * mp.quad(Phi, [0, 1, 3]), 12), ' xi(1/2)=', mp.nstr(mp.mpf(0.5) * mp.mpf(-0.25) * mp.pi ** (-0.25) * mp.gamma(0.25) * mp.zeta(0.5), 12))
    # xi(s) = s(s-1)/2 pi^{-s/2} Gamma(s/2) zeta(s) at s=1/2
    rows = []
    for q in [2, 3, 5, 7, 11, 13]:
        for dx in ['0.02', '0.05', '0.1', '0.2', '0.4']:
            x = q + mp.mpf(dx)
            L = mp.log(x)
            nz = 600 if q > 7 else 2000
            Qg = Q_zero_sum(L, nz=nz)
            hq = h_g(mp.log(q), L)
            nn = norm2(L)
            QS = Qg + 2 * mp.log(q) / mp.sqrt(q) * hq
            row = dict(q=q, x=mp.nstr(x, 6), Q_rh=mp.nstr(Qg, 5), h_logq=mp.nstr(hq, 5), deficit=mp.nstr(2 * mp.log(q) / mp.sqrt(q) * hq, 5), QS=mp.nstr(QS, 5), QS_over_norm=mp.nstr(QS / nn, 5), norm2=mp.nstr(nn, 5))
            rows.append(row)
            print(json.dumps(row), flush=True)
    json.dump(rows, open('probe_rows.json', 'w'), indent=1)

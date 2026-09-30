from t2 import *
import mpmath as mp
# (i) zeta pole+arch vs full at small x
cz = zeta_coeffs(10)
for x in (2.0, 2.5, 3.0):
    pa = lam(x, 24, GAM['zeta'], []); q = lam(x, 24, GAM['zeta'], [(n, cz[n]) for n in range(2, 11) if cz[n]])
    print('zeta x=%.1f lam(P+A)=%+.3e lam(Q)=%+.3e' % (x, pa, q), flush=True)
# (iii) tautology: t* for arbitrary affine path from base B (Q_B PD) to E
def tstar(x, base, N=32):
    A = np.log(x)/2
    secs = []
    for p in (0, 1):
        M0, G, _ = build(A, N, p, GAM['ZK'], C(base))
        M1, _, _ = build(A, N, p, GAM['ZK'], C(cE))
        secs.append((M0, M1, G))
    f = lambda t: min(lmin(M0 + t*(M1-M0), G) for M0, M1, G in secs)
    lo, hi = 0.0, 3.0
    if f(0) <= 0: return 'base not PD'
    for _ in range(40):
        m = (lo+hi)/2
        (lo, hi) = (m, hi) if f(m) > 0 else (lo, m)
    return lo
for name, base in (('zK (not a sqrt of E)', cK), ('avg=sqrt(zK LG)', [(cK[n]+cL[n])/2 for n in range(NM+1)])):
    print(name, ['x=%.2f t*=%.4f' % (x, tstar(x, base)) for x in (16, 19.5, 20.0, 22)], flush=True)
# (ii) D
kap = (mp.sqrt(10 - 2*mp.sqrt(5)) - 2)/(mp.sqrt(5) - 1)
chi = {0: 0, 1: 1, 2: 1j, 4: -1, 3: -1j}
aD = [0] + [float(mp.re((1 - 1j*kap)*chi[n % 5])) for n in range(1, 61)]
cD = vonmangoldt_coeffs(aD, 60)
CD = [(n, float(cD[n])) for n in range(2, 61) if abs(cD[n]) > 1e-25]
for x in (20, 28, 31, 34, 40, 50):
    print('D x=%d' % x, ['N=%d:%+.3e' % (N, lam(x, N, GAM['D'], CD, pole=False)) for N in (16, 32)], flush=True)

"""Certify (mpmath.iv) the sector Weil-form matrix on the span of the first N basis modes:
   lower bound: interval LDL^T of M - lam_lo G has all pivots > 0  =>  Q(f) >= lam_lo ||f||^2 on the span;
   upper bound: Rayleigh quotient of an explicit (rounded) vector v, enclosed in intervals.
usage: cert.py x kind par N basis [dps]"""
import sys, time, pickle, numpy as np, mpmath as mp
import icore
from fractions import Fraction as Fr
x = Fr(sys.argv[1]); kind = sys.argv[2]; par = int(sys.argv[3]); N = int(sys.argv[4]); basis = sys.argv[5]
dps = int(sys.argv[6]) if len(sys.argv) > 6 else 34
X = icore.Ctx(True, dps); iv = X.m
t0 = time.time()
F = icore.Form(X, x, kind)
M, G, kap = icore.build_sector(F, par, N, basis)
tb = time.time() - t0
mid = lambda v: float(mp.mpf(v.mid))
Mf = np.array([[mid(v) for v in r] for r in M]); Gf = np.array([[mid(v) for v in r] for r in G])
wid = max(float(mp.mpf(v.delta)) for r in M for v in r)
d = np.sqrt(np.diag(Gf)); Mn = Mf / np.outer(d, d); Gn = Gf / np.outer(d, d)
e, V = np.linalg.eigh((Mn + Mn.T) / 2)
lam = e[0]
pickle.dump(dict(x=str(x), kind=kind, par=par, N=N, basis=basis,
                 M=[[(str(v.a), str(v.b)) for v in r] for r in M], G=[[(str(v.a), str(v.b)) for v in r] for r in G]),
            open('mat_%s_x%s_p%d_N%d_%s.pkl' % (kind, str(x).replace('/', '_'), par, N, basis), 'wb'))
# ---- upper bound: Rayleigh quotient of the rounded eigenvector (coefficients on phi_m) ----
v = V[:, 0] / d
v = v / np.max(np.abs(v))
vq = [Fr(float(c)).limit_denominator(10**12) for c in v]
vi = [X.c(c) for c in vq]
num = iv.mpf(0); den = iv.mpf(0)
for i in range(N):
    ri = iv.mpf(0); gi = iv.mpf(0)
    for j in range(N):
        ri += M[i][j] * vi[j]; gi += G[i][j] * vi[j]
    num += vi[i] * ri; den += vi[i] * gi
rq = num / den
# ---- lower bound: interval LDL^T of M - lam_lo G ----
def ldl_ok(lo):
    lo = X.c(Fr(lo).limit_denominator(10**18)) if not isinstance(lo, Fr) else X.c(lo)
    Aij = [[M[i][j] - lo * G[i][j] for j in range(N)] for i in range(N)]
    Ld = [[None] * N for _ in range(N)]; D = [None] * N
    minpiv = None
    for k in range(N):
        s = Aij[k][k]
        for j in range(k):
            s -= Ld[k][j] * Ld[k][j] * D[j]
        if not (s.a > 0):
            return False, k, s
        D[k] = s
        if minpiv is None or s.a < minpiv: minpiv = s.a
        for i in range(k + 1, N):
            t = Aij[i][k]
            for j in range(k):
                t -= Ld[i][j] * Ld[k][j] * D[j]
            Ld[i][k] = t / s
    return True, N, minpiv
res = None
for gap in (1e-12, 1e-10, 1e-8, 1e-6):
    lo = lam - gap * max(1.0, abs(lam))
    ok, k, info = ldl_ok(Fr(lo))
    if ok:
        res = (lo, gap); break
    else:
        print('  LDL fails at lo=%.3e (pivot %d)' % (lo, k))
tt = time.time() - t0
print('CERT x=%s %s par%d N=%d %s dps=%d: float lam_min=%.12e | certified LOWER %s | certified Rayleigh UPPER %s | max entry width %.1e | build %.0fs total %.0fs' % (
    x, kind, par, N, basis, dps, lam, ('%.12e (gap %.0e)' % res) if res else 'FAILED',
    mp.nstr(mp.mpf(rq.b), 13), wid, tb, tt), flush=True)

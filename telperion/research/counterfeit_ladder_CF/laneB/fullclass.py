"""FULL-CLASS (all tests in the parity sector, not just a finite span) lower bound for the window Weil
form of kind (default ZK) at x, sector par, in mpmath.iv.  Structure (orthonormal Neumann coordinates):
   f = h + r, h in V_N2 = span{phi_0..phi_{N2-1}}, r in V_N2^perp.
   (T) Q(r) >= d ||r||^2       [frequency side: S = Omega - C >= beta on |t| >= T' (grid check), leakage]
   (K) Q(h, r) = sum_{n>=N2} r_n (K h)_n with K_in from the exact off-diagonal formula
          Q_in = sigma P_i P_n + (-1)^{i+n} (k_i Y_i - k_n Y_n)/(k_n^2 - k_i^2)
   => Q(f) - lam ||f||^2 >= h^T [H - lam I - K^T K/(d - lam)] h ;  K^T K <= exact(N2 <= n < N3) + far bound.
usage: fullclass.py x par N2 N3 Tprime beta [kind]"""
import sys, time, mpmath as mp
import icore
from icore import C, Fr
x = Fr(sys.argv[1]); par = int(sys.argv[2]); N2 = int(sys.argv[3]); N3 = int(sys.argv[4])
Tp = Fr(sys.argv[5]); beta = Fr(sys.argv[6]); kind = sys.argv[7] if len(sys.argv) > 7 else 'ZK'
X = icore.Ctx(True, 34); iv = X.m
T0 = time.time()
F = icore.Form(X, x, kind)
A = F.A; a = F.a; pi = iv.pi
def up(v): return mp.mpf(v.b)
def lo(v): return mp.mpf(v.a)
cs = [c for (_, c, _) in F.pr]; ys = [y for (_, _, y) in F.pr]
AL = sum((abs(c) for c in cs), iv.mpf(0)) * 2
DC = sum((abs(cs[p]) * ys[p] for p in range(len(cs))), iv.mpf(0)) * 2
print('x=%s %s par%d N2=%d N3=%d T\'=%s beta=%s | A_L=%s D_C=%s' % (x, kind, par, N2, N3, Tp, beta, mp.nstr(up(AL), 8), mp.nstr(up(DC), 8)), flush=True)

# ---------------- (T): frequency-side tail floor ----------------
def Omega(t):
    tot = iv.mpf(0)
    fams = icore.families(X, kind)
    for (b0, c0) in fams:
        tot += c0 + icore.cdigamma(X, C(b0 / 2, t / 2)).re
    return tot
def Cfun(t):
    return sum((cs[p] * iv.cos(t * ys[p]) for p in range(len(cs))), iv.mpf(0)) * 2
Smin = Omega(iv.mpf(0)) - AL                   # Omega increasing in t>=0, C <= A_L
bet = X.c(beta)
betaU = up(X.c(beta))
ncell = 0; nsub = 0
tcur = Fr(Tp); hq = Fr(1, 100)
while True:
    tt = X.c(tcur)
    Om = Omega(tt)
    if lo(Om) >= up(AL + bet):                 # beyond: S >= Omega(t) - A_L >= beta for all larger t
        Tend = tcur; break
    Cv = Cfun(tt)
    hh = hq
    # cell [tcur, tcur+hh]: S(t) >= Omega(tcur) - C(tcur) - hh*D_C  (Omega increasing, |C'| <= D_C)
    while not (lo(Om - Cv - X.c(hh) * DC) >= betaU):
        hh /= 2; nsub += 1
        if hh < Fr(1, 10**7):
            print('S >= beta FAILS near t=%.4f' % float(tcur)); sys.exit(1)
    tcur += hh; ncell += 1
print('  (T) S(t) >= beta on [T\', %.1f] certified (%d cells, %d halvings); Omega(Tend) >= A_L + beta; S_min >= %s   [%.0fs]' % (
    float(Tend), ncell, nsub, mp.nstr(lo(Smin), 6), time.time() - T0), flush=True)
# leakage: leak <= (4/(pi A)) sum_{n>=N2} g(k_n),  g(k) = T/(2(k^2-T^2)) - log((k+T)/(k-T))/(4k)
delta = X.c(0) if par == 0 else X.c(Fr(1, 2))
kapf = lambda n: pi * (X.c(n) + delta) / A
TT = X.c(Tp)
def g(k):
    return TT / (2 * (k * k - TT * TT)) - iv.log((k + TT) / (k - TT)) / (4 * k)
KN2 = kapf(N2); assert lo(KN2) > up(TT)
Nexp = 20000
sg = iv.mpf(0)
for n in range(N2, N2 + Nexp):
    sg += g(kapf(n))
KE = kapf(N2 + Nexp); r = TT / KE
# sum_{n >= N2+Nexp} g(k_n) <= (A/pi) int_{k_{N2+Nexp}-pi/A}^inf T^3/(3 (k^2-T^2)^2) dk <= (A/pi) T^3/(9 (1-r'^2)^2 k'^3)
KE1 = KE - pi / A; r1 = TT / KE1
sg += (A / pi) * TT ** 3 / (9 * (1 - r1 * r1) ** 2 * KE1 ** 3)
leak = 4 / (pi * A) * sg
dval = bet - (bet - Smin) * leak
if par == 1:
    # odd pole: P(r) = -2 (sum r_n P'_n / sqrt(A))^2 >= -2 ||r||^2 sum_{n>=N2} P'_n^2 / A,  P'_n = cosh(A/2)/(k_n^2+1/4)
    ch = (iv.exp(A / 2) + iv.exp(-A / 2)) / 2
    s4 = (A / pi) ** 4 / (3 * (X.c(N2) - 1 + delta) ** 3) + 1 / kapf(N2) ** 4   # >= sum_{n>=N2} 1/k_n^4
    dval = dval - 2 * ch * ch * s4 / A
print('  (T) leak <= %s ; tail floor d >= %s   [%.0fs]' % (mp.nstr(up(leak), 6), mp.nstr(lo(dval), 8), time.time() - T0), flush=True)
dlo = lo(dval); assert dlo > 0

# ---------------- head matrix (interval, orthonormal) ----------------
M, Gm, kap_head = icore.build_sector(F, par, N2, 'neumann')
Ai = [2 * A if (par == 0 and i == 0) else A for i in range(N2)]
sq = [iv.sqrt(v) for v in Ai]
H = [[M[i][j] / (sq[i] * sq[j]) for j in range(N2)] for i in range(N2)]
print('  head built [%.0fs]' % (time.time() - T0), flush=True)
# ---------------- Y_n, P_n for n < N3 ----------------
kap = [kapf(n) for n in range(N3)]
Y = []
for n in range(N3):
    k = kap[n]
    Y.append(F.I(k).im - 2 * sum((cs[p] * iv.sin(k * ys[p]) for p in range(len(cs))), iv.mpf(0)))
s_ = (iv.exp(A / 2) - iv.exp(-A / 2)) / 2 if par == 0 else (iv.exp(A / 2) + iv.exp(-A / 2)) / 2
sig = 2 if par == 0 else -2
P = [(1 if n % 2 == 0 else -1) * s_ / (kap[n] ** 2 + X.c(Fr(1, 4))) for n in range(N3)]
print('  Y_n, P_n computed [%.0fs]' % (time.time() - T0), flush=True)
def Qhat(i, n):
    sgn = 1 if (i + n) % 2 == 0 else -1
    return sig * P[i] * P[n] + sgn * (kap[i] * Y[i] - kap[n] * Y[n]) / (kap[n] ** 2 - kap[i] ** 2)
# rigorous consistency check of the formula against the closed-form head matrix (intervals must overlap)
bad = 0; worst = 0
for i in range(N2):
    for j in range(N2):
        if i == j: continue
        q = Qhat(i, j) / (sq[i] * sq[j])
        if lo(q) > up(H[i][j]) or up(q) < lo(H[i][j]): bad += 1
        worst = max(worst, abs(mp.mpf(q.mid) - mp.mpf(H[i][j].mid)))
print('  formula vs closed-form head: %d non-overlapping of %d, max |mid diff| %.1e' % (bad, N2 * (N2 - 1), float(worst)), flush=True)
assert bad == 0
# ---------------- exact coupling Gram for N2 <= n < N3 ----------------
sqA = iv.sqrt(A)
GK = [[iv.mpf(0)] * N2 for _ in range(N2)]
for n in range(N2, N3):
    col = [Qhat(i, n) / (sq[i] * sqA) for i in range(N2)]
    for i in range(N2):
        ci = col[i]; row = GK[i]
        for j in range(i, N2):
            row[j] += ci * col[j]
for i in range(N2):
    for j in range(i):
        GK[i][j] = GK[j][i]
print('  exact coupling Gram done [%.0fs]' % (time.time() - T0), flush=True)
# ---------------- far bound, n >= N3 ----------------
fams = icore.families(X, kind)
Ymax = 2 * sum((abs(c) for c in cs), iv.mpf(0))
for (b0, c0) in fams:
    # |Im psi(b0/2 - i k/2)| <= pi/2 + y/(x^2+y^2) <= pi/2 + 1/y, y = k/2 >= k_{N3}/2
    Ymax += pi / 2 + 2 / kapf(N3) + 2 * iv.exp(-b0 * a) / (b0 * (1 - iv.exp(-2 * a)))
YM = iv.mpf(up(Ymax))
d0 = delta
s2 = (A / pi) ** 2 / (X.c(N3) - 1 + d0)            # >= sum_{n>=N3} 1/k_n^2
s4 = (A / pi) ** 4 / (3 * (X.c(N3) - 1 + d0) ** 3)
s6 = (A / pi) ** 6 / (5 * (X.c(N3) - 1 + d0) ** 5)
s8 = (A / pi) ** 8 / (7 * (X.c(N3) - 1 + d0) ** 7)
q = kap[N2 - 1] / kap[N3 - 1] if False else kapf(N2) / kapf(N3)
Ptil = [P[i] / (sq[i] * sqA) for i in range(N2)]
vtil = [(1 if i % 2 == 0 else -1) * kap[i] * Y[i] / (sq[i] * sqA) for i in range(N2)]
util = [(1 if i % 2 == 0 else -1) / (sq[i] * sqA) for i in range(N2)]
Sa = 4 * s_ * s_ * s4; Sb = s4
# u-coefficient sum  sum_{n>=N3} Y_n^2/k_n^2 : explicit to N4 with |Y_n| <= YI + |2 sum_p c_p sin(k_n y_p)|, crude beyond
YI = iv.mpf(0)
for (b0, c0) in fams:
    YI += pi / 2 + 2 / kapf(N3) + 2 * iv.exp(-b0 * a) / (b0 * (1 - iv.exp(-2 * a)))
N4 = 1 << 19
Sc = iv.mpf(0)
for n in range(N3, N4):
    k = kapf(n)
    sn = 2 * sum((cs[p] * iv.sin(k * ys[p]) for p in range(len(cs))), iv.mpf(0))
    yb = YI + iv.mpf(up(abs(sn)))
    Sc += yb * yb / (k * k)
Sc += YM * YM * (A / pi) ** 2 / (X.c(N4) - 1 + d0)
E = iv.mpf(0)
for i in range(N2):
    ki = kap[i]
    E += ki ** 4 / (Ai[i] * A * (1 - q * q) ** 2) * (2 * ki * ki * Y[i] * Y[i] * s8 + 2 * YM * YM * s6)
# k_n = c_n u + (a_n P + b_n v) + e_n :  k k^T <= (1+e2)[(1+e1) c^2 uu^T + (1+1/e1) 2 (a^2 PP^T + b^2 vv^T)] + (1+1/e2) |e|^2 I
e1 = X.c(Fr(1, 20)); e2 = X.c(Fr(1, 100))
Far = [[(1 + e2) * ((1 + e1) * Sc * util[i] * util[j] + (1 + 1 / e1) * 2 * (Sa * Ptil[i] * Ptil[j] + Sb * vtil[i] * vtil[j]))
        + ((1 + 1 / e2) * E if i == j else 0) for j in range(N2)] for i in range(N2)]
print('  far bound: Ymax<=%s  sum c^2<=%s  E<=%s [%.0fs]' % (mp.nstr(up(YM), 6), mp.nstr(up(Sc), 4), mp.nstr(up(E), 4), time.time() - T0), flush=True)
# ---------------- final PSD check ----------------
def ldl_ok(lam):
    L_ = X.c(lam)
    dd = iv.mpf(dlo) - L_
    Aij = [[H[i][j] - (GK[i][j] + Far[i][j]) / dd - (L_ if i == j else 0) for j in range(N2)] for i in range(N2)]
    Ld = [[None] * N2 for _ in range(N2)]; D = [None] * N2
    for k in range(N2):
        s = Aij[k][k]
        for j in range(k): s -= Ld[k][j] * Ld[k][j] * D[j]
        if not (s.a > 0): return False
        D[k] = s
        for i in range(k + 1, N2):
            t_ = Aij[i][k]
            for j in range(k): t_ -= Ld[i][j] * Ld[k][j] * D[j]
            Ld[i][k] = t_ / s
    return True
import numpy as np
Hm = np.array([[float(mp.mpf(v.mid)) for v in r] for r in H])
Gmid = np.array([[float(mp.mpf(v.mid)) for v in r] for r in GK]); Fmid = np.array([[float(mp.mpf(v.mid)) for v in r] for r in Far])
lam_head = np.linalg.eigvalsh(Hm)[0]
est = np.linalg.eigvalsh(Hm - (Gmid + Fmid) / float(dlo))[0]
print('  float: lam_head(N2)=%.8e  Schur estimate (lam=0) %.8e' % (lam_head, est), flush=True)
best = None
if ldl_ok(Fr(0)):
    best = Fr(0); hi = Fr(max(est, 1e-12)).limit_denominator(10**12)
    for k in range(10):                      # bisection for the largest certified lam in [best, hi]
        mid_ = (best + hi) / 2
        if ldl_ok(mid_): best = mid_
        else: hi = mid_
print('FULLCLASS x=%s %s par%d: certified Q(f) >= %s ||f||^2 for ALL f in the sector (N2=%d, N3=%d, d=%.4f); head Ritz value %.8e  [%.0fs]' % (
    x, kind, par, ('%.6e' % float(best)) if best is not None else 'FAILED', N2, N3, float(dlo), lam_head, time.time() - T0), flush=True)

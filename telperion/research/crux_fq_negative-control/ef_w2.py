"""Negative control 3 (fooling lemma): W2 = zeta(s) * E_a(s),
E_a(s) = 1 + a (p1^{1/2-s} + p2^{1/2-s}) + (p1 p2)^{1/2-s},  p1=101, p2=10007, a=1+1e-4.
Exact FE (conductor p1 p2), nonnegative coefficients, NOT multiplicative at p1 p2 (a != 1).
All zeros with Im < 150 are on the line (float64 in the barrier seat); first off-line zero 0.501943+162.690i.
On the line, (p1p2)^{it/2} E_a(1/2+it) = 2cos(t(L1+L2)/2) + 2a cos(t(L2-L1)/2) (real)."""
import mpmath as mp
from efcommon import *
mp.mp.dps = 30
p1, p2 = mp.mpf(101), mp.mpf(10007)
a = 1 + mp.mpf('1e-4')
L1, L2 = mp.log(p1), mp.log(p2)
half = mp.mpf(1) / 2

def Ea(s):
    return 1 + a * (mp.power(p1, half - s) + mp.power(p2, half - s)) + mp.power(p1 * p2, half - s)

def f_line(t):
    return mp.cos(t * (L1 + L2) / 2) + a * mp.cos(t * (L2 - L1) / 2)

def logcoeffs(Imax, Jmax):
    """ell[i][j]: coefficients of log(1 + A x + B y + C x y) (x = p1^{-s}, y = p2^{-s})."""
    A, B, C = a * mp.sqrt(p1), a * mp.sqrt(p2), mp.sqrt(p1 * p2)
    D = Imax + Jmax
    # power series arithmetic on dicts
    U = {(1, 0): A, (0, 1): B, (1, 1): C}
    ell = {}
    Pk = {(0, 0): mp.mpf(1)}
    for k in range(1, 2 * D + 1):
        new = {}
        for (i, j), v in Pk.items():
            for (di, dj), u in U.items():
                ii, jj = i + di, j + dj
                if ii <= Imax and jj <= Jmax:
                    new[(ii, jj)] = new.get((ii, jj), 0) + v * u
        Pk = new
        for key, v in Pk.items():
            ell[key] = ell.get(key, 0) + (-1) ** (k + 1) * v / k
        if not Pk:
            break
    return ell

def arg_count(sl, sr, t1, t2, fn, hstep=0.002, vstep=0.002):
    pts = []
    nb = int((sr - sl) / hstep) + 1; nv = int((t2 - t1) / vstep) + 1
    for k in range(nb + 1): pts.append(mp.mpc(sl + (sr - sl) * k / nb, t1))
    for k in range(1, nv + 1): pts.append(mp.mpc(sr, t1 + (t2 - t1) * k / nv))
    for k in range(1, nb + 1): pts.append(mp.mpc(sr - (sr - sl) * k / nb, t2))
    for k in range(1, nv + 1): pts.append(mp.mpc(sl, t2 - (t2 - t1) * k / nv))
    tot = mp.mpf(0); mx = mp.mpf(0); prev = fn(pts[0])
    for z in pts[1:]:
        cur = fn(z); d = mp.arg(cur / prev); tot += d; mx = max(mx, abs(d)); prev = cur
    return tot / (2 * mp.pi), mx

def main(T=mp.mpf('162.690'), w=mp.mpf(1), N=5000):
    mp.mp.dps = 20
    lo, hi = T - 17 * w, T + 17 * w
    step = mp.mpf('0.002')
    ts = [lo + step * k for k in range(int((hi - lo) / step) + 1)]
    vals = [f_line(t) for t in ts]
    mp.mp.dps = 30
    online = []
    for k in range(len(ts) - 1):
        if vals[k] * vals[k + 1] < 0:
            t0 = mp.findroot(f_line, (ts[k], ts[k + 1]), solver='anderson')
            online.append(half + mp.j * t0)
    offl = []
    for guess in ['162.690', '164.053', '165.416']:
        z = mp.findroot(Ea, mp.mpc('0.5019', guess))
        offl += [z, 1 - mp.conj(z)]
    print("off-line zeros of E_a found:", [mp.nstr(z, 12) for z in offl[::2]], " max|E_a| =", mp.nstr(max(abs(Ea(z)) for z in offl), 3))
    oims = sorted([z.imag for z in online])
    t1 = (oims[0] + oims[1]) / 2; t2 = (oims[-2] + oims[-1]) / 2
    mp.mp.dps = 20
    nc, mx = arg_count(mp.mpf('-0.5'), mp.mpf('1.5'), t1, t2, Ea)
    mp.mp.dps = 30
    nin = len([t for t in oims if t1 < t < t2])
    noff = len([z for z in offl if t1 < z.imag < t2])
    print("E_a arg-principle count on [-0.5,1.5]x[%s,%s] = %s (max step %s); on-line sign changes %d + off-line found %d = %d"
          % (mp.nstr(t1, 8), mp.nstr(t2, 8), mp.nstr(nc, 8), mp.nstr(mx, 3), nin, noff, nin + noff))
    zz = []
    n = 1
    while True:
        z = mp.zetazero(n)
        if z.imag > hi: break
        if z.imag > lo: zz.append(z)
        n += 1
    h, hhat = make_h(T, w)
    A = lambda r: (L1 + L2) / 2 - mp.log(mp.pi) / 2 + mp.re(mp.digamma(mp.mpf(1) / 4 + mp.j * r / 2)) / 2
    Lam = vonmangoldt_list(N)
    ell = logcoeffs(4, 2)
    LamE = {}
    for (i, j), v in ell.items():
        nn = int(p1) ** i * int(p2) ** j
        LamE[nn] = v * (i * L1 + j * L2)
    print("  Lambda_{E_a}(101) = %s ; Lambda_{E_a}(10007) = %s ; Lambda_{E_a}(101*10007) = %s (zero iff a=1: ell_11 = sqrt(p1p2)(1-a^2) = %s)"
          % (mp.nstr(LamE[101], 10), mp.nstr(LamE[10007], 10), mp.nstr(LamE[101 * 10007], 10), mp.nstr(mp.sqrt(p1 * p2) * (1 - a * a), 10)))
    print("  Lambda_{E_a}(101^2) = %s (negative: positivity fails)" % mp.nstr(LamE[101 ** 2], 10))
    Z1 = zero_sum(h, zz); Z2 = zero_sum(h, online); Z3 = zero_sum(h, [z for z in offl if lo < z.imag < hi])
    pole = h(mp.j / 2) + h(-mp.j / 2)
    Ar = arch_term(h, A, T, w)
    Pz = prime_term(Lam, hhat, N)
    PE = mp.mpf(0)
    for nn, v in LamE.items():
        PE += v * mp.power(nn, -half) * hhat(mp.log(nn))
    PE = -PE / mp.pi
    rhs = pole + Ar + Pz + PE
    lhs = Z1 + Z2 + Z3
    print("W2  T=%s w=%s  zeta zeros %d, E_a on-line %d, E_a off-line (upper) %d" % (T, w, len(zz), len(online), len([z for z in offl if lo < z.imag < hi])))
    print("  zero side = %s  ; pole+arch+prime = %s ; residual %s" % (mp.nstr(lhs.real, 18), mp.nstr(rhs.real, 18), mp.nstr((lhs - rhs).real, 4)))
    # what the off-line pair contributes relative to 'pretending' it sits on the line at the same height
    fake = zero_sum(h, [half + mp.j * z.imag for z in offl if lo < z.imag < hi])
    print("  (off-line quadruples minus same heights put on the line) =", mp.nstr((Z3 - fake).real, 6))

main()

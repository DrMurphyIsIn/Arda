"""Negative control 4: Epstein zeta of Q = x^2 + 5y^2 (disc -20, class number 2).
E_Q(s) = sum' Q(m,n)^{-s} = zeta(s) L(s,chi_-20) + L(s,chi_-4) L(s,chi_5)  (a genus sum of two Euler products).
Completion Lam(s) = (sqrt20/(2pi))^s Gamma(s) E_Q(s) = Lam(1-s); simple pole at s=1.
Explicit formula (F = E_Q/2, a(1)=1): A(r) = (1/2)log 20 - log(2pi) + Re digamma(1/2 + i r), pole term m=1.
Arb-certified off-line zero (Build C): 0.93296969... + 15.66824953... i."""
import mpmath as mp
from efcommon import *
mp.mp.dps = 30
c4 = [0, 1, 0, -1]
c5 = [0, 1, -1, -1, 1]
c20 = [c4[n % 4] * c5[n % 5] for n in range(20)]

def EQ(s):
    return mp.zeta(s) * mp.dirichlet(s, c20) + mp.dirichlet(s, c4) * mp.dirichlet(s, c5)

def Lam(s):
    return mp.power(mp.sqrt(20) / (2 * mp.pi), s) * mp.gamma(s) * EQ(s)

def arg_count(sl, sr, t1, t2, fn, hstep=0.01, vstep=0.02):
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

def main(T=mp.mpf('15.66824953'), w=mp.mpf(1), N=5000):
    # sanity: identity vs brute-force lattice sum at s=3
    bf = mp.mpf(0)
    R = 60
    for m in range(-R, R + 1):
        for n in range(-R, R + 1):
            if m == 0 and n == 0: continue
            bf += mp.mpf(m * m + 5 * n * n) ** -3
    print("E_Q(3): L-function identity %s vs lattice sum (|m|,|n|<=60) %s" % (mp.nstr(EQ(3), 15), mp.nstr(bf, 15)))
    for s in [mp.mpc(0.3, 2.1), mp.mpc(0.9, 15.6)]:
        print("FE residual at", s, mp.nstr(abs(Lam(s) - Lam(1 - s)) / abs(Lam(s)), 4))
    hi = T + 17 * w
    step = mp.mpf('0.01')
    ts = [mp.mpf(1) + step * k for k in range(int((hi - 1) / step) + 1)]
    def Zr(t):
        s = mp.mpf(1) / 2 + mp.j * t
        g = mp.power(mp.sqrt(20) / (2 * mp.pi), s) * mp.gamma(s)
        return (g * EQ(s) / abs(g))
    vals = [Zr(t) for t in ts]
    print("max |Im/Re| of the Hardy-type function on grid:", mp.nstr(max(abs(v.imag) / abs(v.real) for v in vals if abs(v.real) > 1e-8), 3))
    online = []
    for k in range(len(ts) - 1):
        if vals[k].real * vals[k + 1].real < 0:
            t0 = mp.findroot(lambda t: Zr(t).real, (ts[k], ts[k + 1]), solver='anderson')
            online.append(mp.mpf(1) / 2 + mp.j * t0)
    z = mp.findroot(EQ, mp.mpc('0.93296969', '15.66824953'))
    offl = [z, 1 - mp.conj(z)]
    print("Epstein off-line zero:", mp.nstr(z, 15), " |E_Q| =", mp.nstr(abs(EQ(z)), 3))
    oims = sorted([u.imag for u in online])
    t1 = (oims[0] + oims[1]) / 2; t2 = (oims[-2] + oims[-1]) / 2
    nc, mx = arg_count(mp.mpf(-1), mp.mpf(2), t1, t2, EQ)
    nin = len([t for t in oims if t1 < t < t2])
    print("arg-principle count on [-1,2]x[%s,%s] = %s (max step %s); on-line %d + off-line 2 = %d; first on-line ordinates %s"
          % (mp.nstr(t1, 8), mp.nstr(t2, 8), mp.nstr(nc, 8), mp.nstr(mx, 3), nin, nin + 2, [mp.nstr(t, 8) for t in oims[:4]]))
    # representation numbers, independently of the L-function identity
    r = [0] * (N + 1)
    M = int(mp.sqrt(N)) + 1
    for m in range(-M, M + 1):
        for n in range(-M, M + 1):
            q = m * m + 5 * n * n
            if 0 < q <= N:
                r[q] += 1
    a = [mp.mpf(0)] + [mp.mpf(r[n]) / 2 for n in range(1, N + 1)]
    LamF = log_deriv_coeffs(a, N)
    h, hhat = make_h(T, w)
    A = lambda rr: mp.log(20) / 2 - mp.log(2 * mp.pi) + mp.re(mp.digamma(mp.mpf(1) / 2 + mp.j * rr))
    Z = zero_sum(h, online + offl)
    pole = h(mp.j / 2) + h(-mp.j / 2)
    Ar = arch_term(h, A, T, w)
    P = prime_term(LamF, hhat, N)
    print("Epstein T=%s w=%s: zero side %s ; pole+arch+prime %s ; residual %s ; off-line quad contributes %s"
          % (mp.nstr(T, 12), w, mp.nstr(Z.real, 18), mp.nstr((pole + Ar + P).real, 18), mp.nstr((Z - pole - Ar - P).real, 4), mp.nstr(zero_sum(h, offl).real, 10)))
    neg = [n for n in range(2, 300) if LamF[n] < -1e-20]
    print("  Lambda_F(n), n=2..12:", [(n, mp.nstr(LamF[n], 8)) for n in range(2, 13)])
    print("  n<300 with Lambda_F(n)<0:", neg[:30], " count", len(neg))
    def is_pp(n):
        ps = [p for p in range(2, n + 1) if n % p == 0 and all(p % q for q in range(2, int(p ** 0.5) + 1))]
        return len(ps) == 1
    comp = [n for n in range(2, 300) if abs(LamF[n]) > 1e-20 and not is_pp(n)]
    print("  non-prime-power n<300 with Lambda_F(n) != 0:", comp[:20], " count", len(comp))
    mxw = max((abs(LamF[n]) / mp.sqrt(n), n) for n in range(2, N + 1))
    print("  max |Lambda_F(n)| n^{-1/2}, n<=%d: %s at n=%d" % (N, mp.nstr(mxw[0], 6), mxw[1]))

main()

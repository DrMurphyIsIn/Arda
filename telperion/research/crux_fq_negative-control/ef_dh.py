"""Negative control 1: Davenport-Heilbronn.  Guinand-Weil formula with its OWN (signed, non-multiplicative)
prime side, verified on a Gaussian test centred at the Arb-certified off-line zero 0.8085171825 + 85.6993484854 i.

D(s) = sum c(n) n^{-s}, c periodic mod 5: (c(1),c(2),c(3),c(4),c(5)) = (1, kappa, -kappa, -1, 0),
kappa = (sqrt(10-2 sqrt5) - 2)/(sqrt5 - 1).  Completion Phi(s) = (5/pi)^{s/2} Gamma((s+1)/2) D(s) = Phi(1-s).
Explicit formula (no pole; A(r) = (1/2)log(5/pi) + (1/2) Re digamma(3/4 + i r/2)):
  SUM_rho h(gamma_rho) = (1/pi) int h A - (1/pi) SUM_n Lambda_D(n) n^{-1/2} hhat(log n).
"""
import mpmath as mp
from efcommon import *
mp.mp.dps = 30

kappa = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
chi = [0, 1, kappa, -kappa, -1]

def D(s):
    return mp.dirichlet(s, chi)

def Phi(s):
    return mp.power(5 / mp.pi, s / 2) * mp.gamma((s + 1) / 2) * D(s)

def Zreal(t):
    s = mp.mpf(1) / 2 + mp.j * t
    v = Phi(s)
    g = mp.power(5 / mp.pi, s / 2) * mp.gamma((s + 1) / 2)
    return v / abs(g)   # real up to rounding

def arg_count(sl, sr, t1, t2, fn=D, hstep=0.01, vstep=0.04):
    pts = []
    nb = int((sr - sl) / hstep) + 1
    nv = int((t2 - t1) / vstep) + 1
    for k in range(nb + 1):
        pts.append(mp.mpc(sl + (sr - sl) * k / nb, t1))
    for k in range(1, nv + 1):
        pts.append(mp.mpc(sr, t1 + (t2 - t1) * k / nv))
    for k in range(1, nb + 1):
        pts.append(mp.mpc(sr - (sr - sl) * k / nb, t2))
    for k in range(1, nv + 1):
        pts.append(mp.mpc(sl, t2 - (t2 - t1) * k / nv))
    vals = [fn(z) for z in pts]
    tot = mp.mpf(0); mx = mp.mpf(0)
    for a, b in zip(vals[:-1], vals[1:]):
        d = mp.arg(b / a)
        tot += d; mx = max(mx, abs(d))
    return tot / (2 * mp.pi), mx

def main(T=mp.mpf('85.6993484854'), w=mp.mpf('1.5'), N=2000):
    # FE check
    for s in [mp.mpc(0.3, 2.1), mp.mpc(-0.7, 11.0), mp.mpc(0.8, 85.7)]:
        print("FE residual |Phi(s)-Phi(1-s)|/|Phi(s)| at", s, "=", mp.nstr(abs(Phi(s) - Phi(1 - s)) / abs(Phi(s)), 5))
    lo, hi = T - 16 * w, T + 16 * w
    # on-line zeros by sign changes of the real Hardy-type function
    step = mp.mpf('0.02')
    ts = [lo + step * k for k in range(int((hi - lo) / step) + 1)]
    vals = []
    imax = mp.mpf(0)
    for t in ts:
        v = Zreal(t); imax = max(imax, abs(v.imag) / max(abs(v.real), mp.mpf('1e-40')) if abs(v.real) > 1e-12 else imax)
        vals.append(v.real)
    print("max |Im Z/Re Z| on grid (away from zeros):", mp.nstr(imax, 3))
    online = []
    for k in range(len(ts) - 1):
        if vals[k] == 0 or vals[k] * vals[k + 1] < 0:
            t0 = mp.findroot(lambda t: Zreal(t).real, (ts[k], ts[k + 1]), solver='anderson')
            online.append(mp.mpf(1) / 2 + mp.j * t0)
    # off-line zeros (published / Arb-certified crown zero and its FE partner)
    rs = mp.findroot(D, mp.mpc('0.8085171825', '85.6993484854'))
    offline = [rs, 1 - mp.conj(rs)]
    print("off-line zero:", mp.nstr(rs, 15), " |D| =", mp.nstr(abs(D(rs)), 3))
    # count check by argument principle on [-1,2] x [t1,t2], t1,t2 mid-gaps near the window ends
    oims = sorted([z.imag for z in online])
    t1 = (oims[0] + oims[1]) / 2; t2 = (oims[-2] + oims[-1]) / 2
    nin = len([t for t in oims if t1 < t < t2])
    nc, mx = arg_count(mp.mpf(-1), mp.mpf(2), t1, t2)
    print("argument-principle count on [-1,2]x[%s,%s] = %s (max step %s); on-line sign changes inside = %d; + off-line 2 => %d"
          % (mp.nstr(t1, 8), mp.nstr(t2, 8), mp.nstr(nc, 8), mp.nstr(mx, 3), nin, nin + 2))
    h, hhat = make_h(T, w)
    A = lambda r: mp.log(5 / mp.pi) / 2 + mp.re(mp.digamma(mp.mpf(3) / 4 + mp.j * r / 2)) / 2
    Z_on = zero_sum(h, online)
    Z_off = zero_sum(h, offline)
    Ar = arch_term(h, A, T, w)
    a = [mp.mpf(0)] + [chi[n % 5] for n in range(1, N + 1)]
    LamD = log_deriv_coeffs(a, N)
    P = prime_term(LamD, hhat, N)
    print("DH  T=%s w=%s  on-line zeros used=%d" % (mp.nstr(T, 12), w, len(online)))
    print("  zero side (on-line)       =", mp.nstr(Z_on.real, 20))
    print("  zero side (off-line quad) =", mp.nstr(Z_off.real, 20), " imag", mp.nstr(Z_off.imag, 3))
    print("  zero side total           =", mp.nstr((Z_on + Z_off).real, 20))
    print("  arch + prime              =", mp.nstr((Ar + P).real, 20), " (arch %s, prime %s)" % (mp.nstr(Ar, 14), mp.nstr(P, 14)))
    print("  residual (all zeros)      =", mp.nstr((Z_on + Z_off - Ar - P).real, 5))
    print("  residual if the off-line quadruple is dropped =", mp.nstr((Z_on - Ar - P).real, 8))
    # same formula with zeta's multiplicative prime side substituted (wrong dual) for contrast
    Lz = vonmangoldt_list(N)
    Pz = prime_term(Lz, hhat, N)
    print("  residual with zeta's Lambda in place of Lambda_D =", mp.nstr((Z_on + Z_off - Ar - Pz).real, 8))
    print("Lambda_D(n)/log-free values, n=2..12:")
    for n in range(2, 13):
        print("   n=%2d  Lambda_D=%s" % (n, mp.nstr(LamD[n], 12)))
    neg = [n for n in range(2, 200) if LamD[n] < -1e-20]
    comp = [n for n in range(2, 200) if abs(LamD[n]) > 1e-20 and len([p for p in range(2, n + 1) if n % p == 0 and all(p % q for q in range(2, p))]) > 1]
    print("  n<200 with Lambda_D(n)<0:", neg[:25], "... count", len(neg))
    print("  composite non-prime-power n<200 with Lambda_D(n)!=0:", comp[:20], "... count", len(comp))
    # growth of the dual weights
    mxw = max((abs(LamD[n]) / mp.sqrt(n), n) for n in range(2, N + 1))
    print("  max |Lambda_D(n)| n^{-1/2} over n<=%d: %s at n=%d" % (N, mp.nstr(mxw[0], 6), mxw[1]))

main()

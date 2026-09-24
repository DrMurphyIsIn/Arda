"""BUILDER: independent recomputation (mpmath, 50 digits) of the scalar constants of the x = 11.006 window-aware
reduction (A_L, A', b', eta, err = A_L(2eta+eta^2), deficit, xi, b'') for both sectors, from the formulas re-derived
in NOTES.md (builder section), to compare with the idea's Arb log headers.  Also the Zhu threshold 2 pi e^{A_L}
and the window-aware threshold 2 pi e^{A'}.  conjecture1_proved = False."""
import mpmath as mp

mp.mp.dps = 50
a = mp.mpf(307) / 256
eps, w = mp.mpf('0.34'), mp.mpf(66)
A = a + eps
pp = []
for n in range(2, 12):
    m, p = n, None
    for q in range(2, n + 1):
        if m % q == 0:
            p = q
            break
    while m % p == 0:
        m //= p
    if m == 1 and mp.log(n) < 2 * a:
        pp.append((n, p))
AL = mp.mpf(0)
Ap = mp.mpf(0)
Ms = {}
for (n, p) in pp:
    c = 2 * mp.log(p) / mp.sqrt(n)
    M = int(mp.floor(2 * A / mp.log(n))) + 1
    Ms[n] = M
    AL += c
    Ap += c * mp.cos(mp.pi / (M + 1))
print("prime powers:", [n for n, _ in pp])
print("M_n:", Ms)
print("A_L = %s   A'(a+eps) = %s" % (mp.nstr(AL, 15), mp.nstr(Ap, 15)))
print("Zhu threshold 2 pi e^{A_L} = %s ; window-aware 2 pi e^{A'} = %s" % (
    mp.nstr(2 * mp.pi * mp.exp(AL), 8), mp.nstr(2 * mp.pi * mp.exp(Ap), 8)))
eta2 = 4 * a * mp.exp(-(w * eps) ** 2 / 2) / (mp.pi ** 2 * eps ** 3 * w ** 2)
eta = mp.sqrt(eta2)
err = AL * (2 * eta + eta2)
psi0 = mp.digamma(mp.mpf(1) / 4)
c0 = -mp.log(mp.pi)
for (sector, Tc, gapk, gapm) in [('even', 1170, 8, 11.5), ('odd', 2000, 8, 11.5)]:
    Tc = mp.mpf(Tc)
    Tk = Tc + gapk * w
    Tmax = Tk + mp.mpf(gapm) * w
    bp = mp.log(Tc / (2 * mp.pi)) - 1 / Tc - Ap
    k = lambda t: (mp.erf((t + Tk) / w) - mp.erf((t - Tk) / w)) / 2
    hTc = 1 - k(Tc)
    deficit = hTc ** 2 * max(Ap + abs(bp) - (psi0 + c0), 0)
    xi = mp.erfc((Tmax - Tk) / w) * (mp.log(Tmax / 2 + 1) + mp.mpf(4) / 3 + abs(c0) + AL + abs(bp) + abs(psi0))
    bpp = bp - err - deficit - xi
    # envelope check at Tc: Re psi(1/4 + i Tc/2) - log pi >= log(Tc/2pi) - 1/Tc
    env = mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * Tc / 2)) - mp.log(mp.pi)
    print("%s: Tc=%s Tk=%s Tmax=%s  b'=%s  eta=%s  err=%s  deficit=%s  xi=%s  b''=%s" % (
        sector, Tc, Tk, Tmax, mp.nstr(bp, 12), mp.nstr(eta, 5), mp.nstr(err, 5), mp.nstr(deficit, 5),
        mp.nstr(xi, 5), mp.nstr(bpp, 12)))
    print("   envelope at Tc: Phi(Tc) = %s >= log(Tc/2pi) - 1/Tc = %s : %s" % (
        mp.nstr(env, 15), mp.nstr(mp.log(Tc / (2 * mp.pi)) - 1 / Tc, 15), env >= mp.log(Tc / (2 * mp.pi)) - 1 / Tc))
# envelope check on a grid t in [3/4, 5000] (sanity, not a proof: the proof is Binet, see NOTES)
worst = None
for t in [mp.mpf(3) / 4 + j * mp.mpf('0.37') for j in range(0, 13500)]:
    d = mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * t / 2)) - mp.log(mp.pi) - (mp.log(t / (2 * mp.pi)) - 1 / t)
    if worst is None or d < worst[0]:
        worst = (d, t)
print("envelope grid check t in [0.75, 5000]: min slack %s at t = %s (must be >= 0)" % (mp.nstr(worst[0], 6), mp.nstr(worst[1], 6)))

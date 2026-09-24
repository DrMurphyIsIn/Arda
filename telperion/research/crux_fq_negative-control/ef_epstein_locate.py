"""Localize the 2 zeros of E_Q (x^2+5y^2) in [-1,2]x[3.39,30.85] missed by the on-line sign-change scan."""
import mpmath as mp
mp.mp.dps = 20
c4 = [0, 1, 0, -1]; c5 = [0, 1, -1, -1, 1]
c20 = [c4[n % 4] * c5[n % 5] for n in range(20)]
def EQ(s):
    return mp.zeta(s) * mp.dirichlet(s, c20) + mp.dirichlet(s, c4) * mp.dirichlet(s, c5)
def arg_count(sl, sr, t1, t2, fn, hstep=0.01, vstep=0.02):
    pts = []
    nb = int((sr - sl) / hstep) + 1; nv = int((t2 - t1) / vstep) + 1
    for k in range(nb + 1): pts.append(mp.mpc(sl + (sr - sl) * k / nb, t1))
    for k in range(1, nv + 1): pts.append(mp.mpc(sr, t1 + (t2 - t1) * k / nv))
    for k in range(1, nb + 1): pts.append(mp.mpc(sr - (sr - sl) * k / nb, t2))
    for k in range(1, nv + 1): pts.append(mp.mpc(sl, t2 - (t2 - t1) * k / nv))
    tot = mp.mpf(0); prev = fn(pts[0]); mx = 0
    for z in pts[1:]:
        cur = fn(z); d = mp.arg(cur / prev); tot += d; mx = max(mx, abs(d)); prev = cur
    return float(tot / (2 * mp.pi)), float(mx)
# right half of the strip first: zeros with Re > 0.5 + eta
for (a, b) in [(3.3912036, 12.0), (12.0, 20.0), (20.0, 30.84955)]:
    print("Re in [0.52, 2],  t in [%g,%g]: count" % (a, b), arg_count(mp.mpf('0.52'), mp.mpf(2), mp.mpf(a), mp.mpf(b), EQ))

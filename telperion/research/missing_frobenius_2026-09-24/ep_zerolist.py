"""All zeros of E (and of ZK) with 0 < Im < T: on-line via sign changes of the real completed function + bisection,
off-line via |E| grid minima + findroot (sigma in (0.5, 2.1]). Writes zeros_E.txt, zeros_ZK.txt."""
import mpmath as mp, sys
from ep_core import parts, gam
mp.mp.dps = 20
T = float(sys.argv[1]) if len(sys.argv) > 1 else 100
def Zre(t, which):
    s = mp.mpc(0.5, t); zk, g = parts(s); ph = gam(s)
    v = zk + g if which == 'E' else zk
    return mp.re(ph * v) * mp.exp(mp.pi * t / 2)   # rescale (Gamma decay)
for which in ('E', 'ZK'):
    zs = []; t = mp.mpf(0.3); dt = mp.mpf(0.04); prev = Zre(t, which)
    while t < T:
        t2 = t + dt; cur = Zre(t2, which)
        if prev * cur < 0:
            r = mp.findroot(lambda u: Zre(u, which), (t, t2), solver='anderson')
            zs.append(mp.mpc(0.5, r))
        t, prev = t2, cur
    if which == 'E':
        F = lambda s: sum(parts(s))
        sg = [0.6 + 0.1 * i for i in range(16)]; ts = [0.25 * j for j in range(1, int(T / 0.25))]
        V = [[abs(F(mp.mpc(s, u))) for u in ts] for s in sg]
        off = []
        for i in range(len(sg)):
            for j in range(len(ts)):
                v = V[i][j]
                nb = [V[a][b] for a in (i-1, i, i+1) for b in (j-1, j, j+1) if 0 <= a < len(sg) and 0 <= b < len(ts) and (a, b) != (i, j)]
                if all(v <= w for w in nb):
                    try: r = mp.findroot(F, mp.mpc(sg[i], ts[j]), tol=1e-16, maxsteps=40)
                    except Exception: continue
                    if mp.re(r) > 0.5 + 1e-6 and abs(F(r)) < 1e-12 and all(abs(r - f) > 1e-6 for f in off): off.append(r)
        for r in off:
            zs.append(r); zs.append(mp.mpc(1 - mp.re(r), mp.im(r)))
    zs.sort(key=lambda z: float(mp.im(z)))
    with open('zeros_%s.txt' % which, 'w') as fh:
        for z in zs: fh.write('%s %s\n' % (mp.nstr(mp.re(z), 18), mp.nstr(mp.im(z), 18)))
    print(which, 'zeros to T:', len(zs), 'offline:', sum(1 for z in zs if abs(mp.re(z) - 0.5) > 1e-8), flush=True)

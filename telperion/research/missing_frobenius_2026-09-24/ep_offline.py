"""Locate off-line zeros of E = zeta L(-20) + L(-4)L(5) with sigma > 1/2, 0<t<T: coarse |E| grid, local minima, findroot."""
import mpmath as mp, sys
from ep_core import parts
mp.mp.dps = 15
T = float(sys.argv[1]) if len(sys.argv) > 1 else 60
E = lambda s: sum(parts(s))
ds, dt = 0.1, 0.25
sg = [0.6 + ds*i for i in range(15)]
ts = [dt*j for j in range(1, int(T/dt))]
V = [[abs(E(mp.mpc(s, t))) for t in ts] for s in sg]
found = []
for i in range(len(sg)):
    for j in range(len(ts)):
        v = V[i][j]
        nb = [V[a][b] for a in (i-1, i, i+1) for b in (j-1, j, j+1) if 0 <= a < len(sg) and 0 <= b < len(ts) and (a, b) != (i, j)]
        if all(v <= w for w in nb):
            try:
                r = mp.findroot(E, mp.mpc(sg[i], ts[j]), tol=1e-14, maxsteps=40)
            except Exception:
                continue
            if mp.re(r) > 0.5 + 1e-6 and abs(E(r)) < 1e-10 and all(abs(r - f) > 1e-6 for f in found):
                found.append(r)
found.sort(key=lambda z: float(mp.im(z)))
for r in found:
    print("rho = %.8f + %.8f i" % (float(mp.re(r)), float(mp.im(r))))
print("count", len(found))

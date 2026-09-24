"""Zero-side cross-check of the certificate instance: sum over zeros of F(gamma)^2 (zeta: 2000 zeros + tail;
D: zeros to height 200 incl. the four off-line pairs + tail) against the arithmetic-side band form."""
import mpmath as mp, numpy as np, json
from weilfreq import FWindow
from window_scan import even_mats, gen_min
mp.mp.dps = 30
q = mp.mpf(9)/14
A = q * mp.pi
ks = [mp.mpf(2*m+1)/(2*q) for m in (54, 55)]
print('A =', A, ' x =', mp.exp(2*A), ' kappas', ks)
dz = json.load(open('../zeros2000.json'))
zon = [mp.mpf(z) for z in dz]
dd = json.load(open('dh_zeros.json'))
don = [mp.mpf(z) for z in dd['online'] if mp.mpf(z) < 200]
doff = [(mp.mpf(r) - mp.mpf(1)/2, mp.mpf(i)) for (r, i) in dd['offline'] if mp.mpf(r) > 0.51 and mp.mpf(i) < 200]
def F(cs, z):
    return sum(c * (mp.sin((z + k) * A) / (z + k) + mp.sin((z - k) * A) / (z - k)) for c, k in zip(cs, ks))
for kind in ('zeta', 'dh'):
    W = FWindow(A, kind)
    M, G, C, P, R = even_mats(W, ks)
    ev, V = gen_min(M - (P if kind=='zeta' else 0), G)
    ev2, V2 = gen_min(M, G)
    print(kind, 'G=', G.tolist())
    print('  Q/||.||^2 eigs (no pole):', ev, ' with pole:', ev2)
    print('  arch part eigs', gen_min(R, G)[0], ' comb part eigs', gen_min(C, G)[0], ' pole eigs', gen_min(P, G)[0])
    v = V2[:, 0]
    cs = [mp.mpf(float(x)) for x in v]
    nrm = sum(cs[i]*cs[j]*G[i, j] for i in range(2) for j in range(2))
    Qa = sum(cs[i]*cs[j]*M[i, j] for i in range(2) for j in range(2))
    if kind == 'zeta':
        zs = sum(2 * F(cs, g)**2 for g in zon)   # +-gamma
        T = zon[-1]; dens = lambda t: mp.log(t/(2*mp.pi))/(2*mp.pi)
        off = 0
    else:
        zs = sum(2 * F(cs, g)**2 for g in don)
        off = sum(4 * mp.re(F(cs, mp.mpc(g0, b))**2) for (b, g0) in doff)
        T = mp.mpf(200); dens = lambda t: mp.log(5*t/(2*mp.pi))/(2*mp.pi)
    tail = mp.quad(lambda t: 2 * F(cs, t)**2 * dens(t), [T, 2*T, 8*T, mp.inf])
    print('  eigvec c =', [float(c) for c in cs], ' arith Q/n =', mp.nstr(Qa/nrm, 10), ' zero side (online) =', mp.nstr(zs/nrm, 8),
          ' offline quads =', mp.nstr(off/nrm, 8), ' tail =', mp.nstr(tail/nrm, 5), ' total =', mp.nstr((zs+off+tail)/nrm, 10))
    if kind == 'dh':
        for (b, g0) in doff:
            print('    offline pair gamma0=%.3f beta=%.4f contributes %s' % (g0, b, mp.nstr(4*mp.re(F(cs, mp.mpc(g0,b))**2)/nrm, 6)))

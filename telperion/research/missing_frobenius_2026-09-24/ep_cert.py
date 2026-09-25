import mpmath as mp, numpy as np, itertools
from ep_band import mats, gmin
x = 28; A = mp.log(x)/2
ks = [mp.pi*(m+mp.mpf(1)/2)/A for m in range(9)]
MK, G, PK = mats(A, 'ZK', ks); ME, _, _ = mats(A, 'E', ks)
eE, v = gmin(ME, G); nv = v@G@v
print('x=28, 9 cos modes: E-eigvec v =', np.round(v/np.max(abs(v)),3))
print('  Q_E(v)/|v|^2 = %.5f   Q_ZK(v)/|v|^2 = %.5f' % (v@ME@v/nv, v@MK@v/nv))
best = []
for r in (3, 4, 5):
    for S in itertools.combinations(range(9), r):
        S = list(S); e, w = gmin(ME[np.ix_(S,S)], G[np.ix_(S,S)])
        best.append((e, S, w))
best.sort(key=lambda t: t[0])
for e, S, w in best[:6]:
    nw = w@G[np.ix_(S,S)]@w
    print('modes m=%s (k=%s): Q_E/|v|^2=%.4f  Q_ZK/|v|^2=%.4f  v=%s' % (S, ['%.2f'%float(ks[i]) for i in S], e, w@MK[np.ix_(S,S)]@w/nw, np.round(w/np.max(abs(w)),3)))

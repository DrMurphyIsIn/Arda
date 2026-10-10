import mpmath as mp, numpy as np
from ep_band import mats, gmin
for x in (24, 28, 32, 35):
    A = mp.log(x)/2
    for K in (2, 3, 4, 6, 9, 12):
        ks = [mp.pi*(m+mp.mpf(1)/2)/A for m in range(K)]
        MK, G, PK = mats(A, 'ZK', ks); ME, _, _ = mats(A, 'E', ks)
        eK,_ = gmin(MK, G); eE, v = gmin(ME, G)
        print('x=%d K=%2d (even cos modes up to k=%.2f)  ZK=%+.5f  E=%+.5f  vE=%s' % (x, K, float(ks[-1]), eK, eE, np.round(v/np.max(abs(v)),2) if K<=4 else ''), flush=True)

import mpmath as mp, numpy as np
from ep_weil import form
for x in [20, 21, 21.5, 22, 22.5, 23, 24, 26]:
    A = mp.log(x)/2
    out = []
    for M in (int(mp.ceil(24*A/mp.pi))+2, int(mp.ceil(40*A/mp.pi))+2):
        eE, v, ks = form(A, 'E', M); eK, _, _ = form(A, 'ZK', M)
        out.append((M, eK, eE))
    print('x=%5.1f ' % x + '  '.join('M=%d ZK=%+.6f E=%+.6f' % o for o in out), flush=True)

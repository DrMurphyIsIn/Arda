import mpmath as mp
from ep_weil import form
for x in [15, 17, 18, 19, 20]:
    A = mp.log(x)/2
    s = []
    for fac in (24, 40, 60):
        M = int(mp.ceil(fac*A/mp.pi))+2
        eE, v, ks = form(A, 'E', M); s.append('M=%d E=%+.6f' % (M, eE))
    print('x=%5.1f ' % x + '  '.join(s), flush=True)

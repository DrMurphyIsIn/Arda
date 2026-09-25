"""Zero-side check of Q_E(v), Q_ZK(v) for the x=28, 9-mode certificate vector; per-zero contributions."""
import mpmath as mp, numpy as np
from ep_band import mats, gmin
mp.mp.dps = 20
x = 28; A = mp.log(x)/2
ks = [mp.pi*(m+mp.mpf(1)/2)/A for m in range(9)]
MK, G, PK = mats(A, 'ZK', ks); ME, _, _ = mats(A, 'E', ks)
eE, v = gmin(ME, G); v = v/np.max(abs(v))
print('arith: Q_E(v)=%.6f  Q_ZK(v)=%.6f  |v|^2=%.6f' % (v@ME@v, v@MK@v, v@G@v))
def F(z):  # f(u) = sum v_m cos(k_m u) on [-A,A]; F(z)=int f e^{izu}
    return sum(mp.mpf(float(c))*(mp.sin((k+z)*A)/(k+z) + mp.sin((k-z)*A)/(k-z)) for c, k in zip(v, ks))
def zs(fn, T):
    tot = 0; off = 0
    for line in open(fn):
        a, b = map(mp.mpf, line.split())
        gm = (mp.mpc(a, b) - mp.mpf(1)/2)/mp.j
        c = 2*mp.re(F(gm)*mp.conj(F(mp.conj(gm))))
        tot += c
        if abs(a - mp.mpf(1)/2) > 1e-8 and b < 20: off += c
    # tail T..Tmax on the line: density (1/pi) log(t sqrt20/(2pi)) ; |F(t)|^2 twice (t and -t)
    tail = mp.quad(lambda t: 2*abs(F(t))**2*mp.log(t*mp.sqrt(20)/(2*mp.pi))/mp.pi, [T, 200, 400, 1000, 3000, 10000])
    tail += 2*(sum(float(c)**2 for c in v)/4)*(2*A)/(mp.pi)*mp.log(10000*mp.sqrt(20)/(2*mp.pi))/10000*0  # beyond 1e4 negligible
    return tot, tail, off
for name, fn in (('E', 'zeros_E.txt'), ('ZK', 'zeros_ZK.txt')):
    tot, tail, off = zs(fn, 100)
    print('%s zero side: zeros<=100 %.5f + smoothed tail %.5f = %.5f   (contribution of the off-line quadruple at 15.67: %.5f)' % (name, float(tot), float(tail), float(tot+tail), float(off)))

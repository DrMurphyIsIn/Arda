import flint
from flint import arb
flint.ctx.prec = 256
from rmat import _sph_j_backward
import math
a = arb(307)/256
worst = []
for t in [0.1, 0.5, 1, 2, 5, 8, 10, 20, 50, 100, 200, 400, 600, 800, 1000, 1200, 1500, 1800, 2000, 2200, 2400, 2450]:
    x = arb((a*arb(t)).mid())
    xf = float(x.mid())
    ntop = max(4598, int(1.3*xf)+40)
    out = _sph_j_backward(x, 4598, ntop, 256 + int(1.0*xf) + 96)
    osc = out[:max(2, int(1.2*xf))]
    mr = max(float(v.rad()) for v in out[:1700])
    print("t=%7.1f x=%8.2f  max rad j_n (n<1700) = %.2e" % (t, xf, mr))

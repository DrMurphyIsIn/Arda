import flint, time
from flint import arb
flint.ctx.prec = 256
from rmat import sph_j_all
for x in (3.7, 250.3, 543.1, 2300.2):
    xx = arb(x)
    t = time.time()
    js = sph_j_all(xx, int(1.3*x)+10)
    dt = time.time()-t
    e0 = js[0] - xx.sin()/xx
    worst = min(v.rel_accuracy_bits() for v in js[: int(1.2*x)])
    # normalization identity sum (2n+1) j_n^2 = 1
    s = arb(0)
    for n,v in enumerate(js):
        s += (2*n+1)*v*v
    print("x=%.1f  %.2fs  j0-err %s  worst rel bits(n<1.2x) %d  sum(2n+1)j^2-1 = %s" % (x, dt, e0.str(3), worst, (s-1).str(3)))

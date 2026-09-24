import flint, time, math
from flint import arb
from rmat import _bessel_top
def run(x, wp):
    flint.ctx.prec = wp
    xx = arb(x)
    ntop = int(1.3*x)+40
    half = arb(1)/2
    pref = (arb.pi()/(2*xx)).sqrt()
    jp1 = pref*_bessel_top(xx, ntop+1+half, wp+32)
    jn = pref*_bessel_top(xx, ntop+half, wp+32)
    inv = 1/xx
    worst = 10**9; worst_n = None
    for n in range(ntop, 0, -1):
        jm1 = (2*n+1)*inv*jn - jp1
        jp1, jn = jn, jm1
        if n-1 < x:
            b = jm1.rel_accuracy_bits()
            if b < worst:
                worst = b; worst_n = n-1
    return worst, worst_n, jn.rel_accuracy_bits()
for x in (543.1, 1000.3, 2300.2):
    for extra in (0.5, 0.72, 1.0, 1.5):
        wp = 256 + int(extra*x) + 64
        t=time.time()
        w, wn, b0 = run(x, wp)
        print("x=%.1f wp=%d (extra %.2f x): worst rel bits %d at n=%s, j0 bits %d  (%.2fs)" % (x, wp, extra, w, wn, b0, time.time()-t))

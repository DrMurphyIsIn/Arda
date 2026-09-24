import flint, time
from flint import arb
for (x, n) in [(543, 700), (543, 750), (2300, 3200)]:
    for prec in (320, 640, 1280, 2560, 5120):
        flint.ctx.prec = prec
        half = arb(1)/2
        xx = arb(x) + arb(1)/7
        t = time.time()
        v = xx.bessel_j(n + half)
        dt = time.time()-t
        print("x=%d n=%d prec=%d time %.2e rel_acc %d  mag %s" % (x, n, prec, dt, v.rel_accuracy_bits(), v.mid().str(3, radius=False)))

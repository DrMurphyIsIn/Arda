import flint, time
from flint import arb
flint.ctx.prec = 320
half = arb(1)/2
for (x, n) in [(120, 200), (543, 700), (543, 300), (2300, 3200), (2300, 1000)]:
    xx = arb(x) + arb(1)/7
    t = time.time()
    for k in range(20):
        v = xx.bessel_j(n + half)
    dt = (time.time()-t)/20
    print("x=%d n=%d  bessel_j time %.2e s  rel_acc_bits %d" % (x, n, dt, v.rel_accuracy_bits()))

import flint, time
from flint import arb
flint.ctx.prec = 256
flint.ctx.threads = 4
from certify import Window, build_leading
import vldlt
a = arb(249)/256
win = Window(a, 560.0)
M, _ = build_leading(win, 'even', 450)
mr = max(float(M[i,k].rad()) for i in range(450) for k in range(450))
print("max entry radius", mr)
for lam0 in (4.40e-28, 4.48e-28):
    t = time.time()
    r = vldlt.verify(M, lam0, b=64)
    print(lam0, r['ok'], r.get('Efro').str(5) if r['ok'] else r, " %.1fs" % (time.time()-t))

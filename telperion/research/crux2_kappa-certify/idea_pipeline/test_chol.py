import flint, time
from flint import arb
flint.ctx.prec = 256
flint.ctx.threads = 4
from certify import Window, build_leading
import vldlt
win = Window(arb(249)/256, 560.0)
M, _ = build_leading(win, 'even', 450)
for (fn, lam0) in [('ldlt', 4.48e-28), ('chol', 4.48e-28), ('chol', 4.49e-28)]:
    t = time.time()
    r = vldlt.verify(M, lam0, b=64) if fn == 'ldlt' else vldlt.verify_chol(M, lam0, b=64)
    print(fn, lam0, r['ok'], r['Efro'].str(5) if r['ok'] else r.get('reason'), " %.1fs" % (time.time()-t), flush=True)

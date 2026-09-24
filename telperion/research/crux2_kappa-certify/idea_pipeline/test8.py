import flint, time
from flint import arb, arb_mat
flint.ctx.prec = 256
from certify import Window, build_leading, interval_ldlt_pos
from rmat import min_eig_inverse_iter
a = arb(249)/256
win = Window(a, 560.0)
M, cmax2 = build_leading(win, 'even', 450)
lam, v = min_eig_inverse_iter(M, iters=12, verbose=True)
# check radii of entries
mx = max(float(M[i,k].rad()) for i in range(450) for k in range(450))
print("max entry radius", mx)
for lam0 in (4.0e-28, 3e-28, 1e-28, 0.0):
    t = time.time()
    ok, mp, piv = interval_ldlt_pos(M, arb(lam0))
    print("lam0=%.2e ok=%s npiv=%d  fail/min pivot %s  (%.1fs)" % (lam0, ok, len(piv), mp.str(5), time.time()-t), flush=True)
    if not ok:
        print("   last pivots:", [p.str(4) for p in piv[-3:]])

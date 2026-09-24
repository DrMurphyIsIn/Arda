import flint, time
from flint import arb
flint.ctx.prec = 256
from certify import Window, build_leading, interval_ldlt_pos
from rmat import min_eig_inverse_iter
win = Window(arb(0.8), 200.0)
M, cmax2 = build_leading(win, 'even', 200)
lam, v = min_eig_inverse_iter(M, iters=6)
print("inverse iteration lam_min ~", lam.mid().str(8, radius=False))
for lam0 in (9e-18, 1.0e-17, 1.02e-17, 1.03e-17, 1.05e-17, 1.2e-17):
    ok, mp, piv = interval_ldlt_pos(M, arb(lam0))
    small = sorted(piv, key=lambda p: float(p.mid()))[:3]
    print("lam0=%.3e ok=%s  #pivots=%d smallest pivots: %s" % (lam0, ok, len(piv), [p.str(4) for p in small]), " fail value:", (mp.str(4) if not ok else ''))

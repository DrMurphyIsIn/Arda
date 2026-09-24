import flint, time, sys
from flint import arb, arb_mat
flint.ctx.prec = 256
flint.ctx.threads = 4
from certify import Window, build_leading
import vldlt
a = arb(int(sys.argv[1].split('/')[0]))/int(sys.argv[1].split('/')[1])
T = float(sys.argv[2]); N = int(sys.argv[3]); sector = sys.argv[4]
win = Window(a, T)
print("a=%s T#=%s b*=%s N=%d %s" % (sys.argv[1], T, win.bstar.str(6), N, sector), flush=True)
M, cmax2 = build_leading(win, sector, N)
# bisection on the floating LDL^T success to locate lam_min (works for negative too)
def ok(l):
    L, D, j, s = vldlt.floating_ldlt(M, l, b=64)
    return L is not None
lo, hi = -1e-6, 1e-10
if ok(hi):
    print("  PD even at 1e-10?!", flush=True)
for it in range(60):
    mid = (lo + hi)/2 if (hi - lo) > 1e-35 and lo < 0 < hi else None
    break
# geometric search on both signs
for l in [1e-20,1e-22,1e-24,1e-26,1e-28,1e-30,1e-32,1e-34,0.0,-1e-34,-1e-30,-1e-26,-1e-22,-1e-18,-1e-16,-1e-14,-1e-12]:
    print("   floating LDL^T(M - %.0e I) PD? %s" % (l, ok(l)), flush=True)
    if ok(l):
        break

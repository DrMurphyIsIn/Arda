import flint, time, sys
from flint import arb, arb_mat
flint.ctx.prec = 256
flint.ctx.threads = int(sys.argv[1])
from certify_wa import WindowWA
from rmat import sph_j_all, sector_modes
W = WindowWA(arb(307)/256, 0.34, 1170.0, 66.0, gap_k=8.0, gap_max=11.5)
nodes = W.nodes()
a_ = W.a_
N = 2300
modes = sector_modes('even', N)
cn = [(2 * a_ * (2 * n + 1)).sqrt() for n in modes]
lo, hi = int(sys.argv[2]), int(sys.argv[3])
rows = []; wrows = []
t0 = time.time()
for (t, wq, _, _) in nodes[lo:hi]:
    x = arb((a_ * t).mid()); te = x / a_
    js = sph_j_all(x, modes[-1])
    row = [cn[i] * js[modes[i]] for i in range(N)]
    wt = wq * W.weight(te) / arb.pi()
    rows.append(row); wrows.append([wt * v for v in row])
print("built rows %.1fs; max rad J (first 800 modes) %.2e" % (time.time()-t0, max(float(r[i].rad()) for r in rows for i in range(800))), flush=True)
t0 = time.time()
J = arb_mat(rows); WJ = arb_mat(wrows)
G = J.transpose() * WJ
print("matmul %.1fs; max rad G[0:30,0:30] %.2e ; G[13,661] rad %.2e" % (time.time()-t0, max(float(G[i,k].rad()) for i in range(30) for k in range(30)), float(G[13,661].rad())), flush=True)
s = arb(0)
for r_, wr in zip(rows, wrows):
    s += r_[13] * wr[661]
print("direct sum G[13,661] rad %.2e" % float(s.rad()))

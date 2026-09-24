import flint, time
from flint import arb, arb_mat
flint.ctx.prec = 256
flint.ctx.threads = 4
import certify_wa
from certify_wa import WindowWA
from rmat import sph_j_all, sector_modes
W = WindowWA(arb(307)/256, 0.34, 1170.0, 66.0, gap_k=8.0, gap_max=11.5)
nodes = W.nodes()
a_ = W.a_
N = 120
modes = sector_modes('even', N)
nmax = modes[-1]
cn = [(2 * a_ * (2 * n + 1)).sqrt() for n in modes]
# sample 3 node windows: low t, mid t, high t
for (lo, hi) in [(0, 400), (30000, 30400), (59000, 59400)]:
    rows = []; wrows = []
    for (t, wq, _, _) in nodes[lo:hi]:
        x = arb((a_ * t).mid()); te = x / a_
        js = sph_j_all(x, 4599)
        row = [cn[i] * js[modes[i]] for i in range(N)]
        wt = wq * W.weight(te) / arb.pi()
        rows.append(row); wrows.append([wt * v for v in row])
    mr_row = max(float(v.rad()) for r in rows for v in r)
    J = arb_mat(rows); WJ = arb_mat(wrows)
    G = J.transpose() * WJ
    mr = max(float(G[i, k].rad()) for i in range(N) for k in range(N))
    # direct sum for one entry
    s = arb(0)
    for r_, wr in zip(rows, wrows):
        s += r_[5] * wr[7]
    print("nodes %d..%d t~%.0f: max rad(J)=%.2e  max rad(G via arb_mat)=%.2e  direct-sum rad(G[5,7])=%.2e vs matmul %.2e" % (
        lo, hi, float(nodes[lo][0].mid()), mr_row, mr, float(s.rad()), float(G[5, 7].rad())), flush=True)

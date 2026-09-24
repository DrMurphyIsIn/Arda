import flint, time, sys
from flint import arb
flint.ctx.prec = 256
flint.ctx.threads = 16
from rmat import *
a = float(sys.argv[1]); T = float(sys.argv[2]); Ns = [int(v) for v in sys.argv[3].split(',')]
farw = float(sys.argv[4]) if len(sys.argv) > 4 else 2.0
print("a=%s A_L=%s T#=%s beta*=%s" % (a, comb_mass(a).str(8), T, beta_star(a, T).str(8)))
nodes, eds = composite_nodes(T, far_w=farw)
for sector in ('even', 'odd'):
    for N in Ns:
        t = time.time()
        M, b, info = build_R(a, T, N, sector, nodes=nodes)
        lam, v = min_eig_inverse_iter(M, iters=6)
        print("  %s N=%d lam_min(R) ~ %s  (%.1fs)" % (sector, N, lam.mid().str(6, radius=False), time.time()-t), flush=True)

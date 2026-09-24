import flint, time
from flint import arb
flint.ctx.prec = 256
from rmat import *
a = 0.8
print("A_L =", comb_mass(a).str(12), " beta*(150) =", beta_star(a,150).str(10), " beta*(200) =", beta_star(a,200).str(10))
# spherical bessel sanity: j_0(x) = sin x / x, j_1 = sin/x^2 - cos/x
x = arb(3.7)
js = sph_j_all(x, 40)
print("j0 check", (js[0] - x.sin()/x).str(5), " j1 check", (js[1] - (x.sin()/x**2 - x.cos()/x)).str(5))
x = arb(250)
js = sph_j_all(x, 400)
print("j0 check big", (js[0] - x.sin()/x).str(5), js[0].rad())
nodes, eds = composite_nodes(150)
print("nodes", len(nodes))
for N in (60, 100):
    t=time.time()
    M, b, info = build_R(a, 150, N, 'even', nodes=nodes)
    lam, v = min_eig_inverse_iter(M, iters=6)
    print("N=%d lam_min(R_150, even) ~ %s   (%.1fs)" % (N, lam.mid().str(6, radius=False), time.time()-t))

#!/usr/bin/env python3
"""Argument-principle zero count vs real sign changes for the transform of the lowest even
eigenvector of the Weil Gram (Legendre basis).  Usage: cvs_count.py a K dps T.
Exploration only; conjecture1_proved = False."""
import os, sys
sys.path.insert(0, os.path.expanduser("~/arda-e9-audit/telperion/research/weil_positivity"))
import cc_followup as cf, weil_form as wf, mpmath as mp
a = mp.mpf(sys.argv[1]); K = int(sys.argv[2]); mp.mp.dps = int(sys.argv[3]); T = mp.mpf(sys.argv[4])
S = cf.legendre_gram(a, K)
Bs, idx = cf.sector(S["G"], 0)
ev, Q, order = cf.eig_sym(Bs)
c = [mp.mpf(0)] * K
for r, j in enumerate(idx):
    c[j] = Q[r, order[0]]
xs, ws = wf.gl_nodes(K + 80)
nodes = [a * t for t in xs]
xi = [mp.fsum(c[j] * v for j, v in enumerate(cf.phi_vals(K, a, x))) * w * a for x, w in zip(nodes, ws)]
def xihat(z):
    return mp.fsum(f * mp.exp(1j * z * x) for f, x in zip(xi, nodes))
# real sign changes on (0, T)
n = int(T / mp.mpf("0.005"))
prev = mp.re(xihat(mp.mpf("0.001")))
nreal = 0
for i in range(1, n + 1):
    cur = mp.re(xihat(mp.mpf(i) * mp.mpf("0.005")))
    if prev * cur < 0:
        nreal += 1
    prev = cur
wind = cf.count_zeros_box(xihat, T, mp.mpf(3), 4000)
print("a", a, "K", K, "dps", mp.mp.dps, "lowest eig", mp.nstr(ev[0], 5), "next", mp.nstr(ev[1], 5),
      "| zeros in box |Re|<%s |Im|<3: %s | real sign changes in (-T,T): %d" % (T, mp.nstr(wind, 8), 2 * nreal), flush=True)

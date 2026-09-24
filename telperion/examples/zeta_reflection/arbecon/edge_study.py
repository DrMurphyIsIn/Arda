"""Empirical count of zeta evaluations needed per horizontal band edge (sigma in [-1, 2] at height T)
for a Lipschitz arg-tracking certificate: cells [s_i, s_i + d_i] with |zeta(s_i)| > M_i d_i, where
M_i = max |zeta'| on the cell (estimated by dense sampling x 1.5 safety).  sigma < 1/2 is reflected by
the functional equation in a real certificate; here we count cells on [-1, 2] directly.
Also counts a 2-D net for the ball cap (0,1) x [T, T+0.093] with the same criterion.
conjecture1_proved = False."""
import json, random, mpmath
mpmath.mp.dps = 20
bands = json.load(open("bands_h280000.json"))
edges = bands["edges"]
random.seed(1)
def zeta(s): return mpmath.zeta(s)
def dz(s): return mpmath.zeta(s, derivative=1)
def cells_1d(T, a, b, safety=1.5):
    x, n = a, 0
    while x < b:
        z = abs(zeta(mpmath.mpc(x, T)))
        # derivative max over a trial cell: sample 5 points ahead with trial step
        d = 0.5
        while True:
            M = max(abs(dz(mpmath.mpc(x + d * k / 4, T))) for k in range(5)) * safety
            if z > M * d or d < 1e-4:
                break
            d /= 2
        x += d; n += 1
    return n
def cells_cap(T, h=0.093, safety=1.5):
    # 2-D: rows in t spaced like the 1-D cells, crude: count 1-D cells on sigma in (0,1) at t = T, T+h/2, T+h
    return sum(cells_1d(T + dt, 0.0, 1.0, safety) for dt in (0.0, h / 2, h))
out = []
for lo_hi in [(1, 1e3), (1e3, 1e4), (1e4, 1e5), (1e5, 2.8e5)]:
    cand = [e for e in edges if lo_hi[0] <= e < lo_hi[1]]
    for T in random.sample(cand, 4):
        n_edge = cells_1d(T, -1.0, 2.0)
        n_cap = cells_cap(T)
        out.append((T, n_edge, n_cap))
        print("T=%.2f edge cells=%d cap cells=%d" % (T, n_edge, n_cap), flush=True)
json.dump(out, open("edge_study.json", "w"))

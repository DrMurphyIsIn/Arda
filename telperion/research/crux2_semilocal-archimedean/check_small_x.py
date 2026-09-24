"""Builder-stage check: the idea-stage zero-side probe values at SMALL x (probe_fast.py) under-resolve
the oscillatory tail transform int_b^oo Phi'(u) sin(gamma u) du (80 Gauss nodes per panel against
hundreds of oscillations once Phi' decays slowly, x < 4).  Recompute the full value Q(g_x) of the
sharp probe g_x = Phi' 1_[-L/2, L/2] from the zero side with dense quadrature and compare with the
idea-stage DIRECT (zero-free: pole + arch + primes) evaluation direct_eval_np.py.

conjecture1_proved = False.
"""
import json
import os
import numpy as np
import mpmath as mp
from verify_probe_law import dphi_scaled, gl, ZEROS
import direct_eval_np as de

HERE = os.path.dirname(os.path.abspath(__file__))


def q_zero_side_dense(x):
    L = np.log(x)
    b = L / 2
    V, W = [], []
    edges = np.concatenate([b + np.linspace(0, 0.1, 41), b + np.linspace(0.1, 2.5, 241)[1:]])
    for e0, e1 in zip(edges[:-1], edges[1:]):
        v, w = gl(e0, e1, 48)
        V.append(v)
        W.append(w)
    v = np.concatenate(V)
    w = np.concatenate(W)
    d = dphi_scaled(v)
    S = np.zeros(len(ZEROS))
    for i in range(0, len(ZEROS), 200):
        S[i:i + 200] = np.sin(np.outer(ZEROS[i:i + 200], v)) @ (w * d)
    main = float(np.sum(2 * (2 * S) ** 2))
    T = ZEROS[-1]
    db = dphi_scaled(np.array([b]))[0]
    hstep = 1e-7
    kappa = -(dphi_scaled(np.array([b + hstep]))[0] - db) / hstep / db
    tail = 2 * float(mp.quad(lambda t: (mp.log(t / (2 * mp.pi)) / (2 * mp.pi)) * 2 * db ** 2 / (kappa ** 2 + t ** 2),
                             [T, mp.inf]))
    return main + tail, tail


if __name__ == '__main__':
    rows = []
    for x, S in [(2.3, []), (2.5, []), (3.05, [2]), (3.3, [2]), (5.05, [2, 3]), (5.3, [2, 3]), (7.3, [2, 3, 5])]:
        Qz, tail = q_zero_side_dense(x)
        r = de.evaluate(x, S, npan=60, deg=40)
        rows.append(dict(x=x, S=S, Q_full_direct=float(r['Q_full']), Q_full_zero_side_dense=Qz, zero_tail_part=tail,
                         Q_S_direct=float(r['Q_S'])))
        print(json.dumps(rows[-1]), flush=True)
    json.dump(rows, open(os.path.join(HERE, 'check_small_x.json'), 'w'), indent=1)

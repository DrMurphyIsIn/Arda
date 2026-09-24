import json, sys
import numpy as np
from scipy.optimize import brentq
import direct_eval_np as de
import probe_fast as pf

# ---------- small q: direct zero-free evaluation (float64 adequate for x <= ~8)
def QS_direct(q, x):
    S = [p for p in pf.primes_upto(q) if p < q]
    r = de.evaluate(x, S, npan=30, deg=30)
    return r['Q_S'], r['Q_full']

out = {}
for q in [2, 3, 5, 7]:
    f = lambda dx: QS_direct(q, q + dx)[0]
    grid = [0.002, 0.01, 0.03, 0.06, 0.1, 0.15, 0.2, 0.3]
    vals = [(dx, f(dx)) for dx in grid]
    root = None
    for (a, fa), (b, fb) in zip(vals[:-1], vals[1:]):
        if fa > 0 and fb < 0:
            root = brentq(f, a, b, xtol=1e-4); break
    out[q] = dict(method='direct', onset_dx=root, samples=[(a, float('%.4g' % v)) for a, v in vals])
    print(q, json.dumps(out[q]), flush=True)

# ---------- large q: scaled zero-side (validated vs direct at x>=5 to ~0.3%)
def dPhi_s(u, shift, M=8):
    u = np.asarray(u, dtype=float); sgn = np.sign(u); v = np.abs(u); e2 = np.exp(2 * v)
    s = np.zeros_like(v)
    for n in range(1, M + 1):
        A = 4 * np.pi**2 * n**4 * np.exp(4.5 * v) - 6 * np.pi * n**2 * np.exp(2.5 * v)
        dA = 18 * np.pi**2 * n**4 * np.exp(4.5 * v) - 15 * np.pi * n**2 * np.exp(2.5 * v)
        with np.errstate(under='ignore', over='ignore'):
            E = np.exp(-np.pi * n * n * e2 + shift)
        s = s + (dA - A * 2 * np.pi * n * n * e2) * E
    return sgn * s

ZEROS = pf.ZEROS
def QS_scaled(q, x):
    L = np.log(x); a = L / 2; sh = np.pi * q
    v, w = pf.tail_nodes(a); d = dPhi_s(v, sh)
    S = np.sin(np.outer(ZEROS, v)) @ (w * d)
    Q = np.sum(2 * (2 * S) ** 2)
    T = ZEROS[-1]; Q += 2 * 4 * dPhi_s(np.array([a]), sh)[0] ** 2 * 0.5 * np.log(T / (2 * np.pi)) / (2 * np.pi * T)
    lo, hi = np.log(q) - a, a
    xv, wv = pf.gl(lo, hi, 400)
    hq = float(np.sum(wv * dPhi_s(xv, sh) * dPhi_s(xv - np.log(q), sh)))
    return Q + 2 * np.log(q) / np.sqrt(q) * hq, Q, hq   # all scaled by e^{2 pi q}

for q in [11, 13, 23, 47, 97, 199, 401, 797]:
    f = lambda dx: QS_scaled(q, q + dx)[0]
    grid = [0.01, 0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.6, 0.8, 1.0, 1.5]
    vals = [(dx, f(dx)) for dx in grid]
    root = None
    for (a_, fa), (b_, fb) in zip(vals[:-1], vals[1:]):
        if fa > 0 and fb < 0:
            root = brentq(f, a_, b_, xtol=1e-4); break
    pred = None
    out[q] = dict(method='zero-side scaled', onset_dx=root, logq_over_4pi=float(np.log(q) / (4 * np.pi)))
    print(q, json.dumps(out[q]), flush=True)
json.dump(out, open('onsets_all.json', 'w'), indent=1)

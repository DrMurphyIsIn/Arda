"""float64 direct (zero-free) evaluation of Q_S(g), g = Phi' 1_W  (see direct_eval.py for formulas)."""
import json, sys
import numpy as np
from scipy.special import exp1
from probe_fast import dPhi, primes_upto

def panels(a, b, npan, deg):
    x, w = np.polynomial.legendre.leggauss(deg)
    edges = np.linspace(a, b, npan + 1)
    X = np.concatenate([0.5 * (e1 - e0) * x + 0.5 * (e0 + e1) for e0, e1 in zip(edges[:-1], edges[1:])])
    Wt = np.concatenate([0.5 * (e1 - e0) * w for e0, e1 in zip(edges[:-1], edges[1:])])
    return X, Wt

def evaluate(x, S_primes, npan=40, deg=40):
    L = np.log(x); a = L / 2
    V, Wv = panels(-a, a, npan, deg); d = dPhi(V)
    nrm = np.sum(Wv * d * d)
    A = np.sum(Wv * d * np.exp(V / 2)); B = np.sum(Wv * d * np.exp(-V / 2))
    def h(u):
        lo, hi = u - a, a
        if lo >= hi: return 0.0
        X, Wx = panels(lo, hi, npan, deg)
        return float(np.sum(Wx * dPhi(X) * dPhi(X - u)))
    U, Wu = panels(0.0, L, npan, deg)
    Wf = np.exp(U / 2) / np.sinh(U)
    hU = np.array([h(u) for u in U])
    arch_int = np.sum(Wu * (nrm - hU) * Wf)
    Cfix = np.sum(Wu * (np.exp(-2 * U) / U - Wf))
    CL = -np.log(np.pi) + Cfix + exp1(2 * L)
    arch = nrm * CL + arch_int
    pole = 2 * A * B
    pr_S = 0.0; pr_full = 0.0
    for p in primes_upto(int(np.floor(x))):
        n = p
        while n <= x:
            t = 2 * np.log(p) / np.sqrt(n) * h(np.log(n))
            pr_full += t
            if p in S_primes: pr_S += t
            n *= p
    return dict(x=x, S=S_primes, norm2=nrm, pole=pole, arch=arch, Q_full=pole + arch - pr_full, Q_S=pole + arch - pr_S)

if __name__ == '__main__':
    from probe_fast import QS_probe
    for (x, S, q) in [(3.3, [2], 3), (3.05, [2], 3), (5.3, [2, 3], 5), (5.05, [2, 3], 5), (7.3, [2, 3, 5], 7), (2.5, [], 2), (2.3, [], 2)]:
        r = evaluate(x, S)
        Q, tail, deficit, QS, nn = QS_probe(q, x)
        r.update(zero_side_Q=Q, zero_side_QS=QS)
        print(json.dumps({k: (float('%.6g' % v) if isinstance(v, float) else v) for k, v in r.items()}), flush=True)

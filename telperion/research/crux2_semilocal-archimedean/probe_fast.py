"""Fast (float64, no cancellation) version of the near-radical probe computation.
Q(g) for g = Phi' 1_W is computed from the ZERO SIDE: Q(g) = sum_rho |tau^(gamma)|^2 (RH-conditional
cross-check form, first 2000 zeros + integration-by-parts tail), which has NO cancellation.
"""
import json, sys
import numpy as np

ZEROS = np.array(json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'zeros2000.json'))), dtype=float)

def dPhi(u, M=8):
    u = np.asarray(u, dtype=float)
    sgn = np.sign(u); v = np.abs(u)
    e2 = np.exp(2 * v)
    s = np.zeros_like(v)
    for n in range(1, M + 1):
        A = 4 * np.pi**2 * n**4 * np.exp(4.5 * v) - 6 * np.pi * n**2 * np.exp(2.5 * v)
        dA = 18 * np.pi**2 * n**4 * np.exp(4.5 * v) - 15 * np.pi * n**2 * np.exp(2.5 * v)
        with np.errstate(under='ignore', over='ignore'):
            E = np.exp(-np.pi * n * n * e2)
        s = s + (dA - A * 2 * np.pi * n * n * e2) * E
    return sgn * s

def gl(a, b, n):
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * x + 0.5 * (a + b), 0.5 * (b - a) * w

def tail_nodes(a):
    xs, ws = [], []
    for (lo, hi, n) in [(0, 0.02, 80), (0.02, 0.08, 80), (0.08, 0.3, 80), (0.3, 2.0, 80)]:
        x, w = gl(a + lo, a + hi, n); xs.append(x); ws.append(w)
    return np.concatenate(xs), np.concatenate(ws)

def Q_zero_sum(L):
    a = L / 2
    v, w = tail_nodes(a)
    d = dPhi(v)
    # tau^(g) = 2i int_a^inf Phi'(v) sin(g v) dv
    S = np.sin(np.outer(ZEROS, v)) @ (w * d)
    main = np.sum(2 * (2 * S) ** 2)            # |tau^|^2 = 4 S^2 ; zeros at +-gamma
    T = ZEROS[-1]
    tail = 2 * 4 * dPhi(np.array([a]))[0] ** 2 * 0.5 * np.log(T / (2 * np.pi)) / (2 * np.pi * T)
    return main, tail

def h_g(a, L):
    lo, hi = a - L / 2, L / 2
    if lo >= hi:
        return 0.0
    v, w = gl(lo, hi, 400)
    return float(np.sum(w * dPhi(v) * dPhi(v - a)))

def norm2(L):
    v, w = gl(0, L / 2, 400)
    return float(2 * np.sum(w * dPhi(v) ** 2))

def primes_upto(n):
    s = [True] * (n + 1); s[0] = s[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i): s[j] = False
    return [i for i in range(n + 1) if s[i]]

def vm(n):
    for p in primes_upto(n):
        m = n
        while m % p == 0: m //= p
        if m == 1 and n % p == 0: return np.log(p)
    return 0.0

def QS_probe(q, x):
    """S = primes < q.  deficit over all missing prime powers n in [q, x]."""
    L = np.log(x)
    main, tail = Q_zero_sum(L)
    Q = main + tail
    deficit = 0.0
    P = [p for p in primes_upto(int(x)) if p >= q]
    for n in range(q, int(np.floor(x)) + 1):
        lam = vm(n)
        if lam == 0: continue
        p = int(round(np.exp(lam)))
        if p >= q:
            deficit += 2 * lam / np.sqrt(n) * h_g(np.log(n), L)
    return Q, tail, deficit, Q + deficit, norm2(L)

if __name__ == '__main__':
    rows = []
    for q in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        onset = None
        for dx in [0.005, 0.01, 0.02, 0.03, 0.05, 0.075, 0.1, 0.15, 0.2, 0.3, 0.4, 0.6, 0.8, 1.0, 1.5]:
            x = q + dx
            Q, tail, deficit, QS, nn = QS_probe(q, x)
            if QS < 0 and onset is None:
                onset = dx
            rows.append(dict(q=q, dx=dx, Q=Q, tail=tail, deficit=deficit, QS=QS, rel=QS / nn))
        print(json.dumps(dict(q=q, probe_onset_dx=onset)), flush=True)
        for r in rows[-15:]:
            print('   dx=%-6g Q=%.3e (tail %.1e) deficit=%.3e QS=%.3e QS/||g||^2=%.3e' % (r['dx'], r['Q'], r['tail'], r['deficit'], r['QS'], r['rel']))
    json.dump(rows, open('probe_fast_rows.json', 'w'), indent=1)

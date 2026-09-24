"""RIGOROUS weighted-Schur-test bound for ||P_A|| (LEMMA A'), exact step-function evaluation.
P_A = sum_n (c_n/2)(S_{t_n} + S_{-t_n}) on L^2(-A,A), w piecewise constant on K uniform cells (h = 2A/K).
For u = e_i + theta h (theta in [0,1)) and a shift s: u + s lies in cell i + k_s + [theta >= 1 - f_s],
k_s = floor(s/h), f_s = frac(s/h)  (0 outside [0, K)).  So inside every cell the cuts sit at the same relative
positions 1 - f_s; sup over the cell of (P w)(u) = max over the sub-pieces of an exact finite sum.
Arb decides k_s, f_s and the side of each cut for each sub-piece midpoint (ambiguous -> max of both cells)."""
import math, sys
import numpy as np
import flint
from flint import arb
from pnorm import comb, Pmat

def pp_(n):
    m = n; p = None
    for q in range(2, n + 1):
        if m % q == 0:
            p = q; break
    while m % p == 0:
        m //= p
    return p

def schur_bound(a, A, K=2000, w=None):
    flint.ctx.prec = 128
    if w is None:
        P = Pmat(a, A, K)
        ev, V = np.linalg.eigh(P)
        v = np.abs(V[:, -1]); v = np.maximum(v, 1e-12 * v.max())
        lam_num = float(ev[-1])
    else:
        v = np.asarray(w); lam_num = float('nan')
    wf = [float(t) for t in v]
    A_ = arb(A); h = 2 * A_ / K
    shifts = []
    for (n, c, tau) in comb(a):
        cc = arb(2) * arb(pp_(n)).log() / arb(n).sqrt() / 2
        for sgn in (1, -1):
            s = sgn * arb(n).log()
            q = s / h
            k = int(math.floor(float(q.mid())))
            f = q - k
            if not (f > 0 and f < 1):
                raise RuntimeError("ambiguous floor for shift %s" % s)
            shifts.append((cc, k, 1 - f))            # cut at relative position theta_c = 1 - f
    thetas = sorted(set([0.0, 1.0] + [float(tc.mid()) for (_, _, tc) in shifts]))
    mids = [(thetas[j] + thetas[j + 1]) / 2 for j in range(len(thetas) - 1) if thetas[j + 1] - thetas[j] > 0]
    # for each sub-piece midpoint, decide side of every cut (arb); ambiguous -> both
    sides = []
    for th in mids:
        row = []
        for (cc, k, tc) in shifts:
            d = arb(th) - tc
            if d > 0:
                row.append((cc, (k + 1,)))
            elif d < 0:
                row.append((cc, (k,)))
            else:
                row.append((cc, (k, k + 1)))
        sides.append(row)
    lam = 0.0
    lam_arb = arb(0)
    for i in range(K):
        best = arb(0)
        for row in sides:
            tot = arb(0)
            for (cc, ks) in row:
                m = 0.0
                for kk in ks:
                    j = i + kk
                    if 0 <= j < K:
                        m = max(m, wf[j])
                if m > 0:
                    tot += cc * arb(m)
            best = best.max(tot)
        lam_arb = lam_arb.max(best / arb(wf[i]))
    return lam_arb, lam_num

if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    for (a, eps) in [(0.97265625, 0.34), (1.0390625, 0.34), (1.19921875, 0.34), (1.19921875, 0.1), (1.4, 0.34)]:
        A = a + eps
        L, lm = schur_bound(a, A, K=K)
        Ap = sum(c * math.cos(math.pi / (math.floor(2 * A / tau) + 2)) for (n, c, tau) in comb(a))
        print("SCHUR a=%.4f A=%.3f K=%d: path A'=%.3f  numerical lam_max=%.4f  Schur Lambda=%s  T_Lambda=%.0f  (T_path=%.0f)" % (
            a, A, K, Ap, lm, L.str(5), 2 * math.pi * math.exp(float(L.upper())), 2 * math.pi * math.exp(Ap)), flush=True)

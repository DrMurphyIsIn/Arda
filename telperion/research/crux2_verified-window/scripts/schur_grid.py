# Exact-integer Schur / Collatz-Wielandt certificate for the window-compressed prime comb
#   P = sum_{n <= nmax, n prime power} (Lambda(n)/sqrt n) (tau_{log n} + tau_{log n}^*)  on  L^2[-Lp, Lp].
# Uniform grid of N cells (width h = 2Lp/N), step weight w_k > 0 (integers), log n enclosed in
# [A_n q, B_n q] with q = h/H.  For v in cell k the shifted point v -/+ log n lies in a known cell range;
# the checker takes the max weight over that range.  If for every k
#     sum_n C_n (Mminus_{k,n} + Mplus_{k,n}) <= Lam * w_k        (all integers)
# with C_n / S >= Lambda(n)/sqrt n and lam = Lam/S, then A_win(Lp) <= lam (continuous Schur test).
# This file is the float/integer prototype of the Lean checker (same integer algorithm).
import math, sys
import numpy as np
from fractions import Fraction as Fr

def prime_powers(nmax):
    out = []
    for n in range(2, nmax + 1):
        m = n; p = None
        for d in range(2, n + 1):
            if m % d == 0:
                p = d; break
        k = 0
        while m % p == 0:
            m //= p; k += 1
        if m == 1:
            out.append((n, p, k))
    return out

def galerkin(Lp, N, pp):
    h = 2 * Lp / N
    x = -Lp + h * np.arange(N)
    M = np.zeros((N, N))
    for (n, p, k) in pp:
        u = math.log(n)
        if u >= 2 * Lp: continue
        c = math.log(p) / math.sqrt(n)
        D = x[None, :] - x[:, None] - u
        O = np.clip(h - np.abs(D), 0, None) / h
        M += c * (O + O.T)
    ev, vec = np.linalg.eigh(M)
    return ev[-1], np.abs(vec[:, -1])

def max_range(ws, lo, hi):
    if lo > hi: return 0
    return max(ws[lo:hi + 1])

def mminus(N, H, ws, k, A, B):
    if (k + 1) * H < A: return 0
    lo = max(k * H - B, 0) // H
    hi = min(((k + 1) * H - A) // H, N - 1)
    return max_range(ws, lo, hi)

def mplus(N, H, ws, k, A, B):
    lo = (k * H + A) // H
    if N < lo: return 0
    return max_range(ws, min(lo, N - 1), min((k * H + H + B) // H, N - 1))

def row_sums(N, H, ws, data):
    out = []
    for k in range(N):
        s = 0
        for (C, A, B) in data:
            s += C * (mminus(N, H, ws, k, A, B) + mplus(N, H, ws, k, A, B))
        out.append(s)
    return out

def float_data(Lp, N, H, pp, S):
    h = 2 * Lp / N; q = h / H
    data = []
    for (n, p, k) in pp:
        u = math.log(n)
        A = math.floor(u / q) - 2; B = math.ceil(u / q) + 2
        C = math.ceil(S * math.log(p) / math.sqrt(n) * (1 + 1e-9)) + 1
        data.append((C, A, B))
    return data

if __name__ == "__main__":
    Lp = float(sys.argv[1]); N = int(sys.argv[2]); iters = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    nmax = int(math.floor(math.exp(2 * Lp)))
    pp = [t for t in prime_powers(nmax) if math.log(t[0]) < 2 * Lp]
    lam_g, vec = galerkin(Lp, N, pp)
    H = 10 ** 7; S = 10 ** 9
    data = float_data(Lp, N, H, pp, S)
    # nonlinear power iteration on the max-operator, integer weights
    w = vec / vec.max()
    best = None
    for it in range(iters):
        ws = [max(1, int(round(1e9 * wi))) for wi in w]
        rs = row_sums(N, H, ws, data)
        ratio = max(r / (S * wk) for r, wk in zip(rs, ws))
        if best is None or ratio < best[0]:
            best = (ratio, ws)
        wn = np.array(rs, dtype=float)
        w = 0.5 * w + 0.5 * wn / wn.max()
        w = w / w.max()
    print(f"Lp={Lp} N={N} shifts={len(pp)} galerkin_lower={lam_g:.6f} grid_upper={best[0]:.6f} (iters={iters})")

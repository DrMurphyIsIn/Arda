# Twist invariance (zeta) vs its failure (Davenport-Heilbronn), Galerkin cell basis.
# P_theta = sum_n c_n (e^{i <k(n), theta>} O_n + h.c.),  O_n = cell-overlap matrix of tau_{log n} on L^2[-L, L].
# zeta: c_n = Lambda(n)/sqrt n >= 0  => |P_theta| <= P_0 entrywise => lambda_max(P_theta) <= lambda_max(P_0).
# DH:   c_n = Lambda_D(n)/sqrt n signed => no domination; the sup over twists exceeds the untwisted value.
import numpy as np, math
from scipy.linalg import eigh
from scipy.optimize import minimize

def overlap(N, L, u):
    h = 2 * L / N; x = -L + h * np.arange(N)
    D = x[None, :] - x[:, None] - u
    return np.clip(h - np.abs(D), 0, None) / h

def factor(n):
    f = {}; m = n; p = 2
    while p * p <= m:
        while m % p == 0: f[p] = f.get(p, 0) + 1; m //= p
        p += 1
    if m > 1: f[m] = f.get(m, 0) + 1
    return f

def lam_theta(mats, primes, theta):
    idx = {p: i for i, p in enumerate(primes)}
    N = mats[0][2].shape[0]
    M = np.zeros((N, N), dtype=complex)
    for (c, f, O) in mats:
        ph = np.exp(1j * sum(k * theta[idx[p]] for p, k in f.items()))
        M += c * (ph * O + np.conj(ph) * O.T)
    return eigh(M, eigvals_only=True)[-1]

def study(name, coef, L, N, trials, rng):
    ns = [n for n in range(2, int(math.exp(2 * L)) + 2) if math.log(n) < 2 * L and abs(coef(n)) > 1e-14]
    primes = sorted(set(p for n in ns for p in factor(n)))
    mats = [(coef(n) / math.sqrt(n), factor(n), overlap(N, L, math.log(n))) for n in ns]
    lam0 = lam_theta(mats, primes, np.zeros(len(primes)))
    best = lam0; bt = None
    for t in range(trials):
        th = rng.uniform(-math.pi, math.pi, len(primes))
        v = lam_theta(mats, primes, th)
        if v > best: best, bt = v, th
    if bt is not None:
        r = minimize(lambda th: -lam_theta(mats, primes, th), bt, method='Nelder-Mead',
                     options={'maxiter': 300 * len(primes), 'xatol': 1e-7, 'fatol': 1e-10})
        best = max(best, -r.fun)
    print(f"{name}: L={L} N={N} support n<{math.exp(2*L):.1f} ({len(ns)} terms, primes {primes}): untwisted lam_max={lam0:.5f}; "
          f"best over {trials} random twists (+Nelder-Mead) = {best:.5f}; excess = {best - lam0:+.5f}", flush=True)
    return lam0, best

if __name__ == "__main__":
    rng = np.random.default_rng(20260923)
    def lam_zeta(n):
        f = factor(n)
        return math.log(list(f)[0]) if len(f) == 1 else 0.0
    xi = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)
    def a(n): return [0.0, 1.0, xi, -xi, -1.0][n % 5]
    NMAX = 120; LD = [0.0] * (NMAX + 1)
    for n in range(2, NMAX + 1):
        s = a(n) * math.log(n)
        for d in range(2, n):
            if n % d == 0: s -= LD[d] * a(n // d)
        LD[n] = s
    print("Lambda_DH(2..8) =", [round(LD[n], 4) for n in range(2, 9)], " Lambda_DH(6) =", round(LD[6], 4))
    study("zeta", lam_zeta, 1.717, 160, 400, rng)
    study("zeta", lam_zeta, 2.3, 200, 150, rng)
    study("DH  ", lambda n: LD[n], 1.0, 120, 400, rng)
    study("DH  ", lambda n: LD[n], 1.717, 160, 400, rng)

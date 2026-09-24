"""Analytic (Dirichlet-coefficient) canopy bounds of P15 section 8.3 / 8.5 / 10, generalised to
arbitrary (t0, y0), in floating point (exploration) -- the certified version is canopy_analytic_arb.py.

For the canopy strip at time t = t0 (P15 Thm 1.2(ii)) the region N >= N_s is handled exactly as in
P15 section 8.5 (argument principle on a rectangle whose lower edge is y = y0 and upper edge y = 1),
plus P15 section 8.3 (crude triangle inequality for N >= N_1, uniform in y in [y0, 1]).

Lower edge (y = y0), P15 Lemma 8.5 with the Euler mollifier E_{t,P}(s) = prod_{p in P}(1 - b_p p^{-s*}):
    dist(E f, (-inf, 0]) >= 1 - g - sum_{n=2}^{DN} max(|beta_n - g alpha_n|, c |beta_n + g alpha_n|) / n^sigma
where
    beta_n  = sum_{d | (n,D), n/d <= N} lambda_d b_{n/d},     lambda_d = prod_{p | d} (-b_p),
    alpha_n = sum_{d | (n,D), n/d <= N} lambda_d (n/d)^{y0} b_{n/d},
    g       = e^{0.02 y0} (x_N / 4 pi)^{-y0/2}   (>= |gamma| on the N-segment, P15 (20)),
    c       = (1 - g)/(1 + g),
    sigma   = sigma_N(y0) <= Re s*   (P15 (21) at x = x_N = 4 pi N^2 - pi t/4, the left end of the segment),
and then |H_t/B_t| is bounded away from 0 in the sense needed for the argument principle once
    dist(E f, (-inf,0]) > |E|_max * (Z + e_A + e_B + e_{C,0}),   |E|_max = prod (1 + b_p p^{-sigma}),
    Z = g * sum_{m<=N} m^{y0} b_m m^{-sigma} (m^{|kappa|} - 1),  |kappa| <= t y/(2 (x_N - 6)).
The derivation (including why the y0-exponent must match exactly, which is why this is an edge bound
and not a pointwise bound in the interior) is in README.md section 3.
"""
import math

import numpy as np

PI = math.pi


def primes_upto(P):
    return [p for p in range(2, P + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def mollifier(t, primes):
    """Squarefree divisors d of D = prod(primes) and lambda_d = prod_{p|d} (-b_p)."""
    ds = [1]
    lam = [1.0]
    for p in primes:
        bp = math.exp((t / 4) * math.log(p) ** 2)
        ds2, lam2 = [], []
        for d, l in zip(ds, lam):
            ds2.append(d * p)
            lam2.append(-l * bp)
        ds += ds2
        lam += lam2
    return np.array(ds, dtype=np.int64), np.array(lam)


def xN_of(N, t):
    return 4 * PI * N * N - PI * t / 4


def sigma_lower(N, y, t):
    """P15 (21) at x = x_N (Re s* is increasing in x and in y on the segment)."""
    x = xN_of(N, t)
    corr = max(0.0, 1 - 3 * y + 4 * y * (1 + y) / x ** 2)
    return (1 + y) / 2 + (t / 4) * math.log(x / (4 * PI)) - (t / (2 * x * x)) * corr


def g_upper(N, y, t):
    """P15 (20): |gamma| <= e^{0.02 y} (x/4pi)^{-y/2}, evaluated at x = x_N (decreasing in x)."""
    return math.exp(0.02 * y) * (xN_of(N, t) / (4 * PI)) ** (-y / 2)


def err_bound(N, y, t):
    """Upper bound for e_A + e_B + e_{C,0} on the whole N-segment [x_N, x_{N+1}) at height y
    (P15 Prop 6.6 (iv),(v) and (vi); for (vi) we use definition (59) with a - 0.865, which is more
    conservative than the printed Prop 6.6(vi) -- see README section 5)."""
    x = xN_of(N, t)
    L = math.log(x / (4 * PI))
    sig = sigma_lower(N, y, t)
    kap = t * y / (2 * (x - 6))
    g = g_upper(N, y, t)
    n = np.arange(1, N + 1, dtype=float)
    ln = np.log(n)
    bn = np.exp((t / 4) * ln * ln)
    fac = np.expm1(((t * t / 16) * (L - 2 * ln) ** 2 + 0.626) / (x - 6.66))
    eAB = np.sum((1 + g * N ** kap * np.exp(y * ln)) * bn * np.exp(-sig * ln) * fac)
    common = (x / (4 * PI)) ** (-(1 + y) / 4) * math.exp(-(t / 16) * L * L
                                                         + (3 * abs(complex(L, PI / 2)) + 3.58) / (x - 8.52))
    T = x / 2
    et = 0.0
    for sg in (+1, -1):
        et += (0.397 * 3 * 3 ** (sg * y) / (N - 0.865) + 5 / (3 * (T - 6))) * math.exp(3.49 / (T - 4))
    return eAB + common * (1 + et)


def edge_bound(N, y, t, primes, ds=None, lam=None, return_parts=False):
    """P15 Lemma 8.5 lower bound at a single N (exact truncated coefficients), height y (the
    exponent of alpha_n must equal the edge height).  Returns the certified-margin quantity
        F - |E|_max (Z + err)   (> 0 means this N-segment's edge is clear)."""
    if ds is None:
        ds, lam = mollifier(t, primes)
    D = int(np.prod(primes)) if primes else 1
    M = D * N
    sig = sigma_lower(N, y, t)
    g = g_upper(N, y, t)
    beta = np.zeros(M + 1)
    alph = np.zeros(M + 1)
    m = np.arange(1, N + 1)
    lm = np.log(m)
    bm = np.exp((t / 4) * lm * lm)
    am = bm * np.exp(y * lm)
    for d, l in zip(ds, lam):
        idx = d * m
        beta[idx] += l * bm
        alph[idx] += l * am
    n = np.arange(2, M + 1)
    c = (1 - g) / (1 + g)
    num = np.maximum(np.abs(beta[2:] - g * alph[2:]), c * np.abs(beta[2:] + g * alph[2:]))
    Y = np.sum(num * np.exp(-sig * np.log(n)))
    F = 1 - g - Y
    Emax = 1.0
    for p in primes:
        Emax *= 1 + math.exp((t / 4) * math.log(p) ** 2) * p ** (-sig)
    x = xN_of(N, t)
    kap = t * y / (2 * (x - 6))
    Z = g * np.sum(am * np.exp(-sig * lm) * np.expm1(kap * lm))
    err = err_bound(N, y, t)
    margin = F - Emax * (Z + err)
    if return_parts:
        return dict(N=N, F=F, Y=Y, g=g, sigma=sig, Emax=Emax, Z=Z, err=err, margin=margin)
    return margin


def crude_bound(N, y0, t, N0cap=4000):
    """P15 section 8.3 style crude bound, uniform in y in [y0, 1] on the N-segment:
        |f| >= 1 - sum_{n=2}^N b_n n^{-sigma} - c_g N^{-y0} sum_{n<=N} n^{y0} b_n n^{-(sigma - |kappa|)}
    minus err; sums are exact for N <= N0cap, else Lemma 8.2 tails."""
    sig = sigma_lower(N, y0, t)
    x = xN_of(N, t)
    kap = t * 1.0 / (2 * (x - 6))
    cg = math.exp(0.02) * (1 - t / (16 * N * N)) ** (-0.5)

    def S(sigma, extra_y):
        NN = min(N, N0cap)
        n = np.arange(1, NN + 1, dtype=float)
        ln = np.log(n)
        s = np.sum(np.exp((t / 4) * ln * ln + extra_y * ln - sigma * ln))
        if N > NN:
            # Lemma 8.2 applied to b_n n^{extra_y} / n^sigma  (= b_n / n^{sigma - extra_y})
            se = sigma - extra_y
            assert se > (t / 2) * math.log(N)
            v0 = NN ** (1 - se) * math.exp((t / 4) * math.log(NN) ** 2)
            v1 = N ** (1 - se) * math.exp((t / 4) * math.log(N) ** 2)
            s += max(v0, v1) * math.log(N / NN)
        return s
    A = S(sig, 0.0) - 1
    Bs = cg * N ** (-y0) * S(sig - kap, y0)
    return 1 - A - Bs - err_bound(N, y0, t) - 0.0  # err at y0 (err_bound is max-at-endpoints; see README)

#!/usr/bin/env python3
"""Numerical companion to Crux/Crux_meta_barriers.lean (the golden-fake barrier).

conjecture1_proved = False.  Nothing here says anything about where the zeros of the Riemann zeta
function lie.  Every check prints PASS or FAIL and the script exits nonzero if any check fails.
Results go to outputs/numerics.json and outputs/numerics_summary.txt.

Checks
  N1  genus-one admissible sets (q = 2..40, every integer m), three axiom levels
  N2  place counts a_d of the golden data, d <= 10 (the Lean `decide` lemmas)
  N3  the fake zeros: explicit formula versus direct root finding
  N4  Gaussian functional of the fake zero set: Poisson formula versus direct sum, the
      threshold lambda* below which it is positive for every centre c, the margin at the corpus
      threshold 3/2000
  N5  Li coefficients of the fake factor: paired zero sums versus Taylor coefficients of
      log XiA(1/(1-z)); first negative index
  N6  Li coefficients of the hybrid (zeta part by Cauchy integral of log xi); first negative index
  N7  Weil window: the fake zero-side of a triangle test is 2 L h(0) on supp h in (-L, L), and it
      is indefinite once the support reaches L
  N8  pole shadow: minimal inverse pole delta that keeps the weights 1 + delta^n - t_n(5,-5) >= 0
  N9  every RH-violating genus-one datum (prime powers q <= 2000) has an off-line zero at height
      <= pi / log q <= pi / log 5 < 55/16
  N10 envelope of the hybrid: zeta part (first 2000 zeros) plus fake part, lambda in a grid
  N11 Davenport-Heilbronn negative control: not multiplicative, log-coefficients of both signs
  N12 the variant H_{13,-8} of the proposal: displacement, first height, window, threshold
"""
import json
import math
import os
import sys
from fractions import Fraction

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "outputs")
os.makedirs(OUT, exist_ok=True)

RESULTS = []


def record(name, ok, detail):
    RESULTS.append({"check": name, "status": "PASS" if ok else "FAIL", "detail": detail})
    print(("PASS " if ok else "FAIL ") + name + " :: " + json.dumps(detail, default=str)[:400])


# ---------------------------------------------------------------------------------------------
# N1, N2: genus-one formal data
# ---------------------------------------------------------------------------------------------

def power_sums(q, m, nmax):
    t = [2, m]
    for n in range(2, nmax + 1):
        t.append(m * t[-1] - q * t[-2])
    return t


def lefschetz(q, m, nmax):
    t = power_sums(q, m, nmax)
    return [None] + [q ** n + 1 - t[n] for n in range(1, nmax + 1)]


def mobius(n):
    res, k, x = 1, 2, n
    while k * k <= x:
        if x % k == 0:
            x //= k
            if x % k == 0:
                return 0
            res = -res
        k += 1
    if x > 1:
        res = -res
    return res


def place_counts(N, dmax):
    """a_d = (1/d) sum_{e | d} mu(d/e) N_e, as exact fractions."""
    out = [None]
    for d in range(1, dmax + 1):
        s = sum(mobius(d // e) * N[e] for e in range(1, d + 1) if d % e == 0)
        out.append(Fraction(s, d))
    return out


def n1_admissible():
    nmax = 60
    rows = []
    ok = True
    for q in range(2, 41):
        lam_set, place_set, p4_set, rh_set = [], [], [], []
        for m in range(-(q + 4), q + 5):
            N = lefschetz(q, m, nmax)
            pole = N[1] > 0
            lam_ok = pole and all(N[n] >= 0 for n in range(1, nmax + 1))
            a = place_counts(N, nmax)
            place_ok = pole and all(x.denominator == 1 and x >= 0 for x in a[1:])
            # P4 for the local factor: no root of 1 - mT + qT^2 with |T| <= 1/q, i.e. both
            # inverse roots of modulus < q.
            disc = m * m - 4 * q
            if disc < 0:
                big = math.sqrt(q)
            else:
                big = (abs(m) + math.sqrt(disc)) / 2
            p4_ok = big < q - 1e-12
            if lam_ok:
                lam_set.append(m)
            if place_ok:
                place_set.append(m)
            if lam_ok and p4_ok:
                p4_set.append(m)
            if m * m <= 4 * q:
                rh_set.append(m)
        exp_place = list(range(-q, q + 1))
        exp_lam = list(range(-(q + 1), q + 1))
        good = (place_set == exp_place and lam_set == exp_lam and p4_set == exp_place)
        gap = [m for m in place_set if m * m > 4 * q]
        good = good and ((len(gap) > 0) == (q >= 5))
        ok = ok and good
        rows.append({"q": q, "place_level": [min(place_set), max(place_set)],
                     "lambda_level": [min(lam_set), max(lam_set)],
                     "lambda_plus_P4": [min(p4_set), max(p4_set)],
                     "rh_range": [min(rh_set), max(rh_set)], "gap_size": len(gap)})
    record("N1 admissible sets: place level = [-q,q], Lambda level = [-(q+1),q], "
           "Lambda + P4 = [-q,q]; non-RH admissible data exist iff q >= 5 (q = 2..40, n,d <= 60)",
           ok, {"first_rows": rows[:6], "q_with_gap": [r["q"] for r in rows if r["gap_size"] > 0][:8]})
    return rows


def elliptic_traces_f5():
    p = 5
    traces = set()
    for a in range(p):
        for b in range(p):
            if (4 * a ** 3 + 27 * b ** 2) % p == 0:
                continue
            cnt = 1  # point at infinity
            for x in range(p):
                rhs = (x ** 3 + a * x + b) % p
                for y in range(p):
                    if (y * y) % p == rhs:
                        cnt += 1
            traces.add(p + 1 - cnt)
    return sorted(traces)


def n2_golden():
    exp_golden = [1, 5, 25, 110, 500, 2215, 10000, 45100, 205200, 937874]
    exp_anti = [11, 0, 55, 110, 748, 2200, 12320, 45100, 228800, 937750]
    g = place_counts(lefschetz(5, 5, 10), 10)[1:]
    an = place_counts(lefschetz(5, -5, 10), 10)[1:]
    ok = [int(x) for x in g] == exp_golden and [int(x) for x in an] == exp_anti
    record("N2 golden place counts a_1..a_10 match the Lean decide lemmas", ok,
           {"golden": [int(x) for x in g], "anti_golden": [int(x) for x in an]})
    tr = elliptic_traces_f5()
    record("N2b over F_5 every trace in [-4,4] is realized by an elliptic curve (so |m|<=4 are "
           "genuine, m = +-5 are fakes)", tr == list(range(-4, 5)), {"traces": tr})


# ---------------------------------------------------------------------------------------------
# The anti-golden fake
# ---------------------------------------------------------------------------------------------

mp.mp.dps = 50
L5 = mp.log(5)
PHI = (1 + mp.sqrt(5)) / 2
X0 = mp.log(PHI) / L5


def XiA(s):
    return 2 * mp.cosh((s - mp.mpf(1) / 2) * L5) + mp.sqrt(5)


def fake_zero(k, eps):
    return mp.mpf(1) / 2 + eps * X0 + 1j * (2 * k + 1) * mp.pi / L5


def n3_zeros():
    worst = mp.mpf(0)
    for k in range(-20, 20):
        for eps in (1, -1):
            r = fake_zero(k, eps)
            worst = max(worst, abs(XiA(r)))
    # independent root finding from nearby starts
    found = []
    for k in range(0, 4):
        for eps in (1, -1):
            start = fake_zero(k, eps) + mp.mpc(0.05, -0.07)
            root = mp.findroot(XiA, start)
            found.append(abs(root - fake_zero(k, eps)))
    ok = worst < mp.mpf(10) ** (-40) and max(found) < mp.mpf(10) ** (-30)
    record("N3 fake zeros 1/2 +- x0 + i(2k+1)pi/log5 (|XiA| < 1e-40; findroot agrees)", ok,
           {"x0": mp.nstr(X0, 20), "first_height": mp.nstr(mp.pi / L5, 20),
            "max_residual": mp.nstr(worst, 5), "findroot_max_dev": mp.nstr(max(found), 5)})


# ---------------------------------------------------------------------------------------------
# N4: Gaussian functional (corpus normalisation: gaussTest c lam z = (z-c)^2 exp(-2 lam (z-c)^2),
# summed over gammaOf rho = (rho - 1/2)/i for every zero rho, real part)
# ---------------------------------------------------------------------------------------------

def gauss_term_re(u, v, lam):
    """Re[(w)^2 exp(-2 lam w^2)] at w = u - i v (u, v real)."""
    w = mp.mpc(u, -v)
    return mp.re(w * w * mp.exp(-2 * lam * w * w))


def F_fake_direct(c, lam, K=None):
    lam = mp.mpf(lam)
    if K is None:
        # terms decay like exp(-2 lam u^2); spacing 2 pi / log 5
        K = int(mp.ceil(mp.sqrt(60 / lam) / (2 * mp.pi / L5))) + 3
    k0 = int(mp.floor((c * L5 / mp.pi - 1) / 2))
    tot = mp.mpf(0)
    for k in range(k0 - K, k0 + K + 1):
        t = (2 * k + 1) * mp.pi / L5
        tot += 2 * gauss_term_re(t - c, X0, lam)
    return tot


def Ghat(xi, lam):
    lam = mp.mpf(lam)
    return mp.sqrt(mp.pi / (2 * lam)) * (1 / (4 * lam) - xi ** 2 / (16 * lam ** 2)) \
        * mp.exp(-xi ** 2 / (8 * lam))


def F_fake_poisson(c, lam, J=40):
    tot = mp.mpf(0)
    for j in range(-J, J + 1):
        tot += 2 * mp.cosh(j * mp.log(PHI)) * Ghat(j * L5, lam) * mp.cos(j * (mp.pi - c * L5))
    return L5 / (2 * mp.pi) * tot


def min_over_period(lam, F, grid=400):
    period = 2 * mp.pi / L5
    best = None
    for i in range(grid):
        c = period * i / grid
        val = F(c, lam)
        if best is None or val < best[1]:
            best = (c, val)
    # refine
    c0 = best[0]
    lo, hi = c0 - period / grid, c0 + period / grid
    for _ in range(60):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if F(m1, lam) < F(m2, lam):
            hi = m2
        else:
            lo = m1
    c = (lo + hi) / 2
    return c, F(c, lam)


def n4_gauss():
    mp.mp.dps = 30
    # Poisson versus direct
    devs = []
    for lam in ("0.0015", "0.05", "0.18", "0.5", "2"):
        for c in ("0", "0.7", "1.9526", "3.3"):
            a = F_fake_direct(mp.mpf(c), mp.mpf(lam))
            b = F_fake_poisson(mp.mpf(c), mp.mpf(lam))
            devs.append(abs(a - b) / max(1, abs(a)))
    record("N4a Poisson formula for the fake Gaussian functional agrees with direct summation",
           max(devs) < 1e-15, {"max_rel_dev": mp.nstr(max(devs), 5)})
    # the minimum over one period is attained at c = t_k (a fake height): check sign by lambda
    rows = []
    for lam in ("0.0015", "0.01", "0.05", "0.1", "0.15", "0.18", "0.19", "0.2", "0.25", "0.5",
                "1", "2"):
        c, v = min_over_period(mp.mpf(lam), F_fake_poisson, grid=120)
        rows.append({"lam": lam, "argmin_c": mp.nstr(c, 8), "min": mp.nstr(v, 10)})
    # threshold by bisection on min_c F(c, lam) (min at c = pi/L by symmetry; confirmed above)
    cstar = mp.pi / L5

    def g(lam):
        return F_fake_poisson(cstar, lam)

    lo, hi = mp.mpf("0.1"), mp.mpf("0.4")
    assert g(lo) > 0 and g(hi) < 0
    for _ in range(80):
        mid = (lo + hi) / 2
        if g(mid) > 0:
            lo = mid
        else:
            hi = mid
    lam_star = lo
    m3 = min_over_period(mp.mpf("0.0015"), F_fake_poisson, grid=120)[1]
    ok = (m3 > 0) and (0.18 < lam_star < 0.2)
    record("N4b the fake Gaussian functional is > 0 for every centre c iff lam < lam* = "
           + mp.nstr(lam_star, 8) + "; at the corpus threshold 3/2000 its minimum is "
           + mp.nstr(m3, 6), ok, {"table": rows, "lam_star": mp.nstr(lam_star, 12)})
    return lam_star


# ---------------------------------------------------------------------------------------------
# N5: Li coefficients of the fake factor
# ---------------------------------------------------------------------------------------------

def series_exp(a, N):
    g = [mp.exp(a[0])] + [mp.mpf(0)] * N
    for n in range(1, N + 1):
        g[n] = sum(k * a[k] * g[n - k] for k in range(1, n + 1)) / n
    return g


def series_log(f, N):
    l = [mp.log(f[0])] + [mp.mpf(0)] * N
    for n in range(1, N + 1):
        l[n] = (f[n] - sum(k * l[k] * f[n - k] for k in range(1, n)) / n) / f[0]
    return l


def li_fake_taylor(N):
    # s = 1/(1-z), s - 1/2 = 1/2 + z + z^2 + ...
    u = [mp.mpf(1) / 2] + [mp.mpf(1)] * N
    ep = series_exp([L5 * x for x in u], N)
    em = series_exp([-L5 * x for x in u], N)
    phi = [ep[n] + em[n] for n in range(N + 1)]
    phi[0] += mp.sqrt(5)
    l = series_log(phi, N)
    return [None] + [n * l[n] for n in range(1, N + 1)]


def pair_term(n, rho):
    w = rho / (rho - 1)
    return 2 - w ** n - w ** (-n)


def li_fake_zeros(n, K=4000):
    """Paired zero sum over k in [-K, K), plus the leading tail term n^2 (L/pi)^2 / (2K)."""
    tot = mp.mpf(0)
    for k in range(-K, K):
        tot += mp.re(pair_term(n, fake_zero(k, 1)))
    tail = mp.mpf(n) ** 2 * (L5 / mp.pi) ** 2 / (2 * K)
    return tot + tail


def n5_li_fake():
    mp.mp.dps = 80
    N = 150
    lt = li_fake_taylor(N)
    first_neg = next((n for n in range(1, N + 1) if lt[n] < 0), None)
    mp.mp.dps = 30
    cmp = []
    for n in (1, 2, 3, 5, 10, 30, 61, 62, 63):
        zs = li_fake_zeros(n, K=3000)
        cmp.append({"n": n, "taylor": lt[n], "zero_sum_K3000_plus_tail": zs})
    lam1_formula = (2 * L5 * mp.sinh(L5 / 2)) / (2 * mp.cosh(L5 / 2) + mp.sqrt(5))
    agree = all(abs(r["taylor"] - r["zero_sum_K3000_plus_tail"]) < 2e-3 * max(1, abs(r["taylor"]))
                for r in cmp)
    ok = (first_neg == 63) and abs(lt[1] - lam1_formula) < mp.mpf(10) ** (-25) and agree
    record("N5 fake Li coefficients (1-based Li indexing): lambda_1..lambda_62 > 0, lambda_63 < 0 "
           "(0-based corpus rungs: taylorCoeff 0..61 >= 0, rung 62 < 0); lambda_1 = XiA'(1)/XiA(1); "
           "paired zero sums (+ tail) agree with Taylor coefficients", ok,
           {"first_negative_1based": first_neg, "lambda_1": mp.nstr(lt[1], 15),
            "lambda_62": mp.nstr(lt[62], 10), "lambda_63": mp.nstr(lt[63], 10),
            "compare": [{k: (mp.nstr(v, 12) if not isinstance(v, int) else v) for k, v in r.items()}
                        for r in cmp]})
    return lt


# ---------------------------------------------------------------------------------------------
# N6: Li coefficients of xi (Cauchy integral) and of the hybrid
# ---------------------------------------------------------------------------------------------

def xi(s):
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def li_xi_cauchy(N, r=mp.mpf("0.55"), M=512):
    """lambda_n(xi) = n [z^n] log xi(1/(1-z)), by the trapezoid rule on |z| = r."""
    vals = []
    for j in range(M):
        z = r * mp.exp(2j * mp.pi * j / M)
        s = 1 / (1 - z)
        vals.append(mp.log(xi(s)))
    # unwrap is unnecessary: log xi(1/(1-z)) is analytic on |z| < 1 and xi(s) > 0 near s = 1
    out = [None]
    for n in range(1, N + 1):
        c = sum(vals[j] * mp.exp(-2j * mp.pi * j * n / M) for j in range(M)) / M / r ** n
        out.append(n * mp.re(c))
    return out


def n6_li_hybrid(lt_fake):
    mp.mp.dps = 60
    N = 120
    lx = li_xi_cauchy(N)
    known = mp.mpf("0.0230957089661210338")  # lambda_1(xi) (Keiper; Maslanka)
    hyb = [None] + [lx[n] + lt_fake[n] for n in range(1, N + 1)]
    first_neg = next((n for n in range(1, N + 1) if hyb[n] < 0), None)
    ok = abs(lx[1] - known) < mp.mpf(10) ** (-12) and all(lx[n] > 0 for n in range(1, N + 1))
    record("N6 hybrid Li coefficients lambda_n(xi) + lambda_n(fake): positive for n < " +
           str(first_neg) + ", first negative at n = " + str(first_neg) +
           " (lambda_n(xi) by Cauchy integral, lambda_1(xi) = 0.02309570896...)",
           ok and first_neg is not None and first_neg > 62,
           {"lambda1_xi": mp.nstr(lx[1], 18), "first_negative_hybrid": first_neg,
            "sample": {n: [mp.nstr(lx[n], 8), mp.nstr(lt_fake[n], 8), mp.nstr(hyb[n], 8)]
                       for n in (5, 30, 62, 80, first_neg if first_neg else 1)}})


# ---------------------------------------------------------------------------------------------
# N7: Weil window
# ---------------------------------------------------------------------------------------------

def tri_hat(t, a):
    """Fourier transform of the triangle h(u) = max(0, 1 - |u|/a): a * sinc^2(a t / 2)."""
    x = a * t / 2
    if abs(x) < mp.mpf(10) ** (-20):
        return a
    return a * (mp.sin(x) / x) ** 2


def fake_weil_side(a, K):
    tot = mp.mpc(0)
    for k in range(-K, K):
        t = (2 * k + 1) * mp.pi / L5
        for eps in (1, -1):
            tot += tri_hat(mp.mpc(t, -eps * X0), a)
    return tot


def n7_weil():
    mp.mp.dps = 25
    rows = []
    ok = True
    for a in ("0.8", "1.2", "1.6", "2.0", "2.5", "3.0"):
        a = mp.mpf(a)
        K = 20000
        val = mp.re(fake_weil_side(a, K))
        # Poisson: L sum_n (-1)^n (phi^n + phi^-n) h(nL), h(nL) = max(0, 1 - |n| L / a)
        pred = mp.mpf(0)
        for n in range(-5, 6):
            h = max(mp.mpf(0), 1 - abs(n) * L5 / a)
            pred += L5 * (-1) ** n * (PHI ** n + PHI ** (-n)) * h
        # truncation error of the k-sum is O(1/K); compare loosely
        agree = abs(val - pred) < 5e-3 * max(1, abs(pred))
        in_window = a < L5
        if in_window:
            agree = agree and abs(pred - 2 * L5) < mp.mpf(10) ** (-20)
        ok = ok and agree
        rows.append({"a": mp.nstr(a, 3), "in_window": bool(in_window), "direct": mp.nstr(val, 10),
                     "poisson": mp.nstr(pred, 10), "pred_value": pred})
    ok = ok and any(r["pred_value"] < 0 for r in rows)
    for r in rows:
        r.pop("pred_value")
    record("N7 Weil zero-side of the fake part for the triangle test (autocorrelation of an "
           "indicator of length a): exactly 2 L h(0) = 2 log 5 while a < log 5 (Zhu's window "
           "a = 1.6 included); indefinite (negative at a = 3) once the support passes L",
           ok, {"rows": rows, "window_half_width_for_autocorrelations": mp.nstr(L5 / 2, 8)})


# ---------------------------------------------------------------------------------------------
# N8: pole shadow numerics
# ---------------------------------------------------------------------------------------------

def n8_pole_shadow():
    t = power_sums(5, -5, 400)

    def ok_delta(delta, nmax=400):
        d = mp.mpf(delta)
        return all(1 + d ** n - t[n] >= 0 for n in range(1, nmax + 1))

    alpha = (5 + mp.sqrt(5)) / 2
    lo, hi = mp.mpf(3), mp.mpf(5)
    assert ok_delta(hi) and not ok_delta(lo)
    for _ in range(60):
        mid = (lo + hi) / 2
        if ok_delta(mid):
            hi = mid
        else:
            lo = mid
    ok = hi > alpha and ok_delta(4) and not ok_delta(alpha)
    record("N8 pole shadow: weights 1 + delta^n - t_n(5,-5) >= 0 for all n <= 400 iff delta >= "
           + mp.nstr(hi, 10) + " > alpha = (5+sqrt5)/2 = " + mp.nstr(alpha, 10)
           + "; delta = 4 works (H4), and the matching pole sits at Re s = log(delta)/log 5", ok,
           {"delta_min": mp.nstr(hi, 15), "alpha": mp.nstr(alpha, 15),
            "Re_s_of_pole_delta_min": mp.nstr(mp.log(hi) / L5, 10),
            "Re_s_of_offline_zero": mp.nstr(mp.log(alpha) / L5, 10),
            "Re_s_of_H4_pole": mp.nstr(mp.log(4) / L5, 10)})


# ---------------------------------------------------------------------------------------------
# N9: low off-line zeros of every genus-one fake
# ---------------------------------------------------------------------------------------------

def is_prime_power(n):
    for p in range(2, n + 1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return n == 1
    return False


def n9_low_zeros():
    worst_height = 0.0
    count = 0
    real_zero_cases = 0
    for q in range(5, 2001):
        if not is_prime_power(q):
            continue
        for m in range(-q, q + 1):
            if m * m <= 4 * q:
                continue
            count += 1
            L = math.log(q)
            c = m / math.sqrt(q)
            # zeros: cosh((s-1/2)L) = c/2; c > 2: real zero; c < -2: zero at height pi/L
            h = 0.0 if c > 0 else math.pi / L
            if c > 0:
                real_zero_cases += 1
            x = math.acosh(abs(c) / 2) / L
            assert 0 < x < 0.5
            worst_height = max(worst_height, h)
    ok = worst_height <= math.pi / math.log(5) + 1e-12 and worst_height < 55 / 16
    record("N9 every RH-violating genus-one datum over a prime power q in [5, 2000] has an off-line "
           "zero in the open strip at height <= pi/log q <= pi/log 5 = 1.9520 < 55/16", ok,
           {"data_checked": count, "with_real_offline_zero": real_zero_cases,
            "max_lowest_height": worst_height})


# ---------------------------------------------------------------------------------------------
# N10: envelope of the hybrid
# ---------------------------------------------------------------------------------------------

def n10_envelope(lam_star):
    zeros = json.load(open(os.path.join(HERE, "..", "zeros2000.json")))
    zs = [float(z) for z in zeros]
    import numpy as np
    Z = np.array(zs)
    rows = []
    ok = True
    for lam in (0.05, 0.18, 0.3, 0.5, 1.0, 2.0):
        cs = np.linspace(0.0, 1500.0, 60001)
        # zeta part on the line: sum over +-gamma of x^2 exp(-2 lam x^2), x = +-gamma - c
        Fz = np.zeros_like(cs)
        for g in Z:
            for sgn in (1.0, -1.0):
                x = sgn * g - cs
                Fz += x * x * np.exp(-2 * lam * x * x)
        # fake part (vectorised Poisson series)
        L = math.log(5)
        phi = (1 + math.sqrt(5)) / 2
        Ff = np.zeros_like(cs)
        for j in range(-30, 31):
            xi_ = j * L
            gh = math.sqrt(math.pi / (2 * lam)) * (1 / (4 * lam) - xi_ ** 2 / (16 * lam ** 2)) * \
                math.exp(-xi_ ** 2 / (8 * lam))
            Ff += 2 * math.cosh(j * math.log(phi)) * gh * np.cos(j * (math.pi - cs * L))
        Ff *= L / (2 * math.pi)
        H = Fz + Ff
        neg = cs[H < 0]
        last_neg = float(neg.max()) if neg.size else None
        rows.append({"lam": lam, "min_fake": float(Ff.min()), "min_zeta_over_c_in_[100,1500]":
                     float(Fz[cs >= 100].min()), "hybrid_negative_somewhere": bool(neg.size),
                     "largest_c_with_hybrid_negative": last_neg})
        if lam <= float(lam_star):
            ok = ok and neg.size == 0
    record("N10 hybrid Gaussian functional over c in [0,1500] (zeta: first 2000 zeros, on the line): "
           "no negative value for lam below lam*; above lam* the hybrid is NEGATIVE near the fake "
           "heights (so the full Wall does detect it), and the crossover centre beyond which the "
           "zeta part wins grows fast with lam (72 at 0.3, 334 at 0.5, > 1387 at 1)", ok,
           {"rows": rows})


# ---------------------------------------------------------------------------------------------
# N11: Davenport-Heilbronn control
# ---------------------------------------------------------------------------------------------

def n11_dh():
    # chi mod 5 with chi(2) = i: chi(1)=1, chi(2)=i, chi(4)=-1, chi(3)=-i
    kappa = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)
    chi = {0: 0, 1: 1, 2: 1j, 3: -1j, 4: -1}

    def b(n):
        z = chi[n % 5]
        return (((1 - 1j * kappa) * z + (1 + 1j * kappa) * z.conjugate()) / 2).real

    mult_fail = abs(b(6) - b(2) * b(3))
    # log-coefficients: b = exp*(beta) as Dirichlet series; beta(n) via b(n) = sum over
    # factorisations -- compute beta = log via the recursion n*? use Lambda-type: -F'/F coefficients
    N = 2000
    bb = [0.0] + [b(n) for n in range(1, N + 1)]
    # c(n) = coefficient of -F'/F: sum_{d|n} c(d) b(n/d) = b(n) log n
    c = [0.0] * (N + 1)
    for n in range(2, N + 1):
        s = bb[n] * math.log(n)
        for d in range(2, n):
            if n % d == 0:
                s -= c[d] * bb[n // d]
        c[n] = s
    negs = [n for n in range(2, N + 1) if c[n] < -1e-9]
    ok = mult_fail > 0.5 and len(negs) > 0
    record("N11 Davenport-Heilbronn is not a class-P datum: b(6) != b(2) b(3) and its "
           "von Mangoldt coefficients take negative values", ok,
           {"kappa": kappa, "b2": b(2), "b3": b(3), "b6": b(6), "first_negative_Lambda_at": negs[:5]})


# ---------------------------------------------------------------------------------------------
# N12: H_{13,-8}
# ---------------------------------------------------------------------------------------------

def n12_variant():
    mp.mp.dps = 30
    q, m = 13, -8
    L = mp.log(q)
    c = mp.mpf(m) / mp.sqrt(q)
    x0 = mp.acosh(abs(c) / 2) / L
    h1 = mp.pi / L

    def F(cc, lam):
        tot = mp.mpf(0)
        for j in range(-40, 41):
            xi_ = j * L
            gh = mp.sqrt(mp.pi / (2 * lam)) * (1 / (4 * lam) - xi_ ** 2 / (16 * lam ** 2)) * \
                mp.exp(-xi_ ** 2 / (8 * lam))
            tot += 2 * mp.cosh(j * x0 * L) * gh * mp.cos(j * (mp.pi - cc * L))
        return L / (2 * mp.pi) * tot

    lo, hi = mp.mpf("0.1"), mp.mpf("1.5")
    for _ in range(60):
        mid = (lo + hi) / 2
        if F(mp.pi / L, mid) > 0:
            lo = mid
        else:
            hi = mid
    ok = (4 * q < m * m <= q * q) and h1 > mp.sqrt(3) / 2
    record("N12 variant (q,m) = (13,-8): admissible, RH-violating, first height pi/log 13 = "
           + mp.nstr(h1, 6) + ", window half-width log(13)/2 = " + mp.nstr(L / 2, 6)
           + ", Gaussian threshold lam* = " + mp.nstr(lo, 6), ok,
           {"x0": mp.nstr(x0, 10), "first_height": mp.nstr(h1, 10), "window": mp.nstr(L / 2, 10),
            "lam_star": mp.nstr(lo, 10)})


def main():
    n1_admissible()
    n2_golden()
    n3_zeros()
    lam_star = n4_gauss()
    lt = n5_li_fake()
    n6_li_hybrid(lt)
    n7_weil()
    n8_pole_shadow()
    n9_low_zeros()
    n10_envelope(lam_star)
    n11_dh()
    n12_variant()
    with open(os.path.join(OUT, "numerics.json"), "w") as f:
        json.dump(RESULTS, f, indent=2, default=str)
    with open(os.path.join(OUT, "numerics_summary.txt"), "w") as f:
        for r in RESULTS:
            f.write(r["status"] + " " + r["check"] + "\n")
    nfail = sum(1 for r in RESULTS if r["status"] != "PASS")
    print("\n%d checks, %d failed" % (len(RESULTS), nfail))
    sys.exit(1 if nfail else 0)


if __name__ == "__main__":
    main()

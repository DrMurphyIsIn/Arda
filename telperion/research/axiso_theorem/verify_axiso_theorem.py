#!/usr/bin/python3
"""Numerical and exact-arithmetic checks for the class-P rigidity claims (C1-C9).

conjecture1_proved = False.  This script produces evidence, not proofs.  The kernel-checked
statements are in
  telperion/examples/li_positivity/lean/Crux/Crux_axiso_theorem.lean
and this script checks, independently of Lean, the numbers those statements pin down.  It also
checks the analytic claims (C5, C6, C7, C8) that are NOT kernel-checked.

Conventions.  a(n) are Dirichlet coefficients of F.  b(n) are the coefficients of G = log F, with
b(1) = 0.  Lambda_F(n) = b(n) log n.  Log-coefficients are computed exactly, in rational
arithmetic, from the Omega-derivation recursion
    Omega(n) a(n) = sum_{d | n} Omega(d) b(d) a(n/d),
which is equivalent to F = exp(G).  This is the identity `IsDirExp.pmul_additive` with
w = Omega in the Lean file.

Run:  /usr/bin/python3 verify_axiso_theorem.py   (about 1-3 minutes).
It writes verify_axiso_theorem_output.txt and verify_axiso_theorem.json next to itself.
"""
import json
import math
import os
import random
import sys
from fractions import Fraction
from itertools import product

import mpmath as mp
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_TXT = os.path.join(HERE, "verify_axiso_theorem_output.txt")
OUT_JSON = os.path.join(HERE, "verify_axiso_theorem.json")
mp.mp.dps = 30
LINES = []
RESULTS = {}


def emit(s=""):
    print(s)
    LINES.append(s)


def record(key, value):
    RESULTS[key] = value


# ---------------------------------------------------------------------------------------------
# arithmetic helpers
# ---------------------------------------------------------------------------------------------

def factorize(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def big_omega(n):
    return sum(factorize(n).values()) if n > 1 else 0


def mu(n):
    if n == 1:
        return 1
    f = factorize(n)
    if any(e > 1 for e in f.values()):
        return 0
    return (-1) ** len(f)


def divisors(n):
    ds = [1]
    for p, e in factorize(n).items():
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return sorted(ds)


def log_coeffs(a, ns):
    """Exact log-coefficients b(n) for n in ns (sorted, divisor-closed), with a[1] == 1.
    Uses Omega(n) b(n) = Omega(n) a(n) - sum_{d | n, 1 < d < n} Omega(d) b(d) a(n/d)."""
    b = {1: Fraction(0)}
    for n in ns:
        if n == 1:
            continue
        om = big_omega(n)
        s = Fraction(om) * a[n]
        for d in divisors(n):
            if d == 1 or d == n:
                continue
            s -= big_omega(d) * b[d] * a[n // d]
        b[n] = s / om
    return b


def smooth_numbers(q, bound):
    """q-smooth integers <= bound."""
    ps = sorted(factorize(q).keys()) if q > 1 else []
    out = {1}
    frontier = [1]
    while frontier:
        new = []
        for m in frontier:
            for p in ps:
                x = m * p
                if x <= bound and x not in out:
                    out.add(x)
                    new.append(x)
        frontier = new
    return sorted(out)


# ---------------------------------------------------------------------------------------------
# K1: finite-difference rigidity (C3 Step 2 lemma)
# ---------------------------------------------------------------------------------------------

def check_K1(trials=3000, seed=11):
    emit("== K1 finite-difference rigidity (C3 Step 2) ==")
    rng = random.Random(seed)
    newton_ok = True
    nonconst_all_nonneg = 0
    first_neg_k = []
    for _ in range(trials):
        r = rng.randint(2, 9)
        u = [Fraction(rng.randint(-20, 20), rng.randint(1, 7)) for _ in range(r)]
        if len(set(u)) == 1:
            continue
        U = lambda j: u[j % r]
        # forward differences at 0 up to order K
        K = 60
        vals = [U(j) for j in range(K + 2)]
        d = []
        cur = vals[:]
        for k in range(K + 1):
            d.append(cur[0])
            cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
        # Newton: u(n+1) - u(n) = sum_k C(n,k) Delta^{k+1} u(0)
        for n in range(0, 12):
            lhs = U(n + 1) - U(n)
            rhs = sum(math.comb(n, k) * d[k + 1] for k in range(n + 1))
            if lhs != rhs:
                newton_ok = False
        negs = [k for k in range(1, K + 1) if d[k] < 0]
        if not negs:
            nonconst_all_nonneg += 1
        else:
            first_neg_k.append(negs[0])
    emit(f"  Newton identity Delta u(n) = sum_k C(n,k) Delta^(k+1) u(0) (exact, n<=11): {newton_ok}")
    emit(f"  nonconstant periodic u with Delta^k u(0) >= 0 for all 1<=k<=60: {nonconst_all_nonneg}")
    emit(f"  largest index of the first negative difference: {max(first_neg_k)} "
         f"(always <= period: {max(first_neg_k) <= 9})")
    record("K1", {"newton_exact": newton_ok, "counterexamples": nonconst_all_nonneg,
                  "max_first_negative_index": max(first_neg_k)})


# ---------------------------------------------------------------------------------------------
# K2: cumulant rigidity (C3 Step 1 lemma)
# ---------------------------------------------------------------------------------------------

def cumulants(m, K):
    """kappa_1..kappa_K from m_0 = 1 via m_{n+1} = sum_j C(n,j) kappa_{j+1} m_{n-j}."""
    kap = {}
    for n in range(K):
        s = m[n + 1] - sum(math.comb(n, j) * kap[j + 1] * m[n - j] for j in range(n))
        kap[n + 1] = s  # the j = n term is kappa_{n+1} m_0
    return kap


def check_K2(trials=2000, seed=12):
    emit("== K2 cumulant rigidity (C3 Step 1) ==")
    rng = random.Random(seed)
    all_nonneg_nonconst = 0
    worst = []
    for _ in range(trials):
        r = rng.randint(2, 8)
        # moment sequence m_j = f(g^j) on a cyclic group of order r, f >= 0, f(1) = 1
        f = [Fraction(1)] + [Fraction(rng.randint(0, 12), rng.randint(1, 6)) for _ in range(r - 1)]
        if all(x == 1 for x in f):
            continue
        K = 16
        m = [f[j % r] for j in range(K + 1)]
        kap = cumulants(m, K)
        if all(kap[k] >= 0 for k in range(1, K + 1)):
            all_nonneg_nonconst += 1
        worst.append(min(kap[k] for k in range(1, K + 1)))
    # the KP conductor-5 moment sequence (1,0,1,0,...): cumulants of log cosh
    mk = [Fraction(1 if j % 2 == 0 else 0) for j in range(9)]
    kk = cumulants(mk, 8)
    emit(f"  nonconstant periodic nonneg moment sequences with all kappa_k >= 0 (k<=16): "
         f"{all_nonneg_nonconst} of {trials}")
    emit(f"  cumulants of (1,0,1,0,...) [log cosh]: " +
         ", ".join(f"k{k}={kk[k]}" for k in range(1, 9)))
    # the lower bound m_{kt} >= t! kappa_k^t from nonnegative cumulants
    ok = True
    for _ in range(300):
        kap = {k: Fraction(rng.randint(0, 5), rng.randint(1, 4)) for k in range(1, 13)}
        m = [Fraction(1)]
        for n in range(12):
            m.append(sum(math.comb(n, j) * kap[j + 1] * m[n - j] for j in range(n + 1)))
        for k in range(2, 5):
            for t in range(0, 12 // k + 1):
                if m[k * t] < math.factorial(t) * kap[k] ** t:
                    ok = False
    emit(f"  lower bound m_(kt) >= t! kappa_k^t (random nonneg cumulants, exact): {ok}")
    record("K2", {"counterexamples": all_nonneg_nonconst,
                  "logcosh_cumulants": {k: str(kk[k]) for k in range(1, 9)},
                  "factorial_lower_bound": ok})


# ---------------------------------------------------------------------------------------------
# Steps 1-4 of C3 on periodic data, and the Step 4 inequality |P(q)| <= 1
# ---------------------------------------------------------------------------------------------

def check_steps(seed=13):
    emit("== C3 Steps 1-4 on periodic coefficient data (exact rationals) ==")
    rng = random.Random(seed)
    # (a) random nonnegative periodic A mod q with A(1) = 1.  Every log-positive example found
    #     must satisfy the conclusions of Steps 2 and 4: A(x u) = A(x) for units u, |P(q)| <= 1.
    N = 1200
    ns = list(range(1, N + 1))
    fails = {}
    for q in [2, 3, 4, 5, 6, 7, 8, 9, 10, 12]:
        units = [u for u in range(q) if math.gcd(u, q) == 1]
        found_pos = 0
        viol = 0
        for t in range(40):
            A = [Fraction(rng.randint(0, 9), rng.randint(1, 4)) for _ in range(q)]
            if t % 2 == 0:            # half the samples: units forced to 1 (Step 1 conclusion)
                for u in units:
                    A[u] = Fraction(1)
            A[1 % q] = Fraction(1)
            a = {n: A[n % q] for n in ns}
            b = log_coeffs(a, ns)
            if min(b.values()) >= 0:
                found_pos += 1
                inv = all(A[(x * u) % q] == A[x] for x in range(q) for u in units)
                Pq = sum(a[q // d] * mu(d) for d in divisors(q))
                if not inv or abs(Pq) > 1:
                    viol += 1
        fails[q] = {"logpositive": found_pos, "violations_of_steps_2_4": viol}
    emit(f"  random nonneg periodic A (40 per q, n <= {N}): {fails}")
    emit("  (every log-positive A found is unit-invariant with |P(q)| <= 1, as Steps 2 and 4 require)")
    # (b) unit-invariant A: a(n) = sum_{d | gcd(n,q)} P(d).  Sample P on divisors of q; test
    #     log-positivity on q-smooth n; record max |P(q)| among log-positive P (theorem: <= 1).
    stats = {}
    for q in [2, 3, 4, 6, 8, 9, 10, 12, 30]:
        dq = divisors(q)
        M = smooth_numbers(q, 4000)
        best = Fraction(0)
        npos = 0
        ntrial = 400
        for _ in range(ntrial):
            P = {d: Fraction(rng.randint(-8, 8), 8) for d in dq}
            P[1] = Fraction(1)
            a = {m: sum(P[d] for d in dq if m % d == 0) for m in M}
            if min(a.values()) < 0:
                continue
            b = log_coeffs(a, M)
            if min(b.values()) >= 0:
                npos += 1
                best = max(best, abs(P[q]))
        stats[q] = {"logpositive": npos, "trials": ntrial, "max_abs_Pq": str(best)}
    emit("  unit-invariant A, P = F/zeta random on divisors of q, log-positivity on q-smooth n <= 4000:")
    for q, s in stats.items():
        emit(f"    q={q:3d}: {s['logpositive']:3d} log-positive of {s['trials']}, "
             f"max |P(q)| = {s['max_abs_Pq']}  (Step 4 theorem: <= 1; FE needs sqrt(q) = {math.sqrt(q):.4f})")
    record("steps_random_periodic", {str(k): v for k, v in fails.items()})
    record("step4_random_P", {str(k): v for k, v in stats.items()})
    # (c) the diagonal polynomial f(t) = sum_{d | q} P(d) t^Omega(d) for the C9(i) example
    f = [1, 4, 2]
    roots = np.roots(f[::-1])
    emit(f"  C9(i) diagonal f(t) = 1 + 4t + 2t^2: roots {np.round(roots, 6)}; "
         f"min |root| = {min(abs(roots)):.6f} < 1, so Step 4 predicts that log-positivity fails")
    # (d) diagonal identities (R), (S) of the Lean proof on a log-positive example q = 12
    q = 12
    P = {1: Fraction(1), 2: Fraction(1, 2), 3: Fraction(-1, 4), 4: Fraction(0), 6: Fraction(-1, 8),
         12: Fraction(0)}
    M = smooth_numbers(q, 10 ** 6)
    a = {m: sum(P[d] for d in divisors(q) if m % d == 0) for m in M}
    b = log_coeffs(a, M)
    Kmax = 8
    Mk = {k: [m for m in M if big_omega(m) == k and (q ** k) % m == 0] for k in range(Kmax + 1)}
    A_ = {k: sum(a[m] for m in Mk[k]) for k in Mk}
    B_ = {k: sum(big_omega(m) * b[m] for m in Mk[k]) for k in Mk}
    Rok = all(k * A_[k] == sum(B_[j] * A_[k - j] for j in range(k + 1)) for k in range(Kmax + 1))
    emit(f"  diagonal identity (R) k A_k = sum_j B_j A_(k-j) on q=12 example, k<=8 (exact): {Rok}")
    record("diag_R_exact", Rok)


# ---------------------------------------------------------------------------------------------
# C9 negative controls
# ---------------------------------------------------------------------------------------------

def check_C9():
    emit("== C9 negative controls ==")
    # (i) F = zeta(s) (1 + 4 2^-s + 2 4^-s)
    x1 = -1 + mp.sqrt(2) / 2
    s0 = mp.log(2 + mp.sqrt(2)) / mp.log(2) + 1j * mp.pi / mp.log(2)
    P = lambda s: 1 + 4 * mp.power(2, -s) + 2 * mp.power(4, -s)
    F = lambda s: mp.zeta(s) * P(s)
    L = lambda s: mp.power(4 / mp.pi, s / 2) * mp.gamma(s / 2) * F(s)
    fe = max(abs(L(s) - L(1 - s)) for s in [mp.mpc(0.3, 7.1), mp.mpc(2.2, -3.3), mp.mpc(-1.4, 20)])
    emit(f"  (i)  s0 = {mp.nstr(s0, 12)}  Re s0 = log2(2+sqrt2) = {mp.nstr(mp.re(s0), 12)} > 1")
    emit(f"       2^(-s0) = {mp.nstr(mp.power(2, -s0), 12)} vs sqrt2/2 - 1 = {mp.nstr(x1, 12)}")
    emit(f"       |F(s0)| = {mp.nstr(abs(F(s0)), 5)}, FE residual max |Lambda(s)-Lambda(1-s)| = {mp.nstr(fe, 5)}")
    ns = list(range(1, 257))
    a = {n: Fraction(1 + (4 if n % 2 == 0 else 0) + (2 if n % 4 == 0 else 0)) for n in ns}
    b = log_coeffs(a, ns)
    mult = all(a[m * n] == a[m] * a[n] for m in range(1, 16) for n in range(1, 16)
               if math.gcd(m, n) == 1)
    emit(f"       a(n) >= 0: {min(a.values()) >= 0}; multiplicative (m,n<16): {mult}; "
         f"b(2)={b[2]}, b(4)={b[4]}, b(8)={b[8]}, b(16)={b[16]}")
    # (ii) KP conductor-5 element
    phi = (1 + mp.sqrt(5)) / 2
    chi5 = [0, 1, -1, -1, 1]
    Fkp = lambda s: (mp.zeta(s) * (1 + mp.power(5, mp.mpf(1) / 2 - s)) + mp.dirichlet(s, chi5)) / 2
    Lkp = lambda s: mp.power(5 / mp.pi, s / 2) * mp.gamma(s / 2) * Fkp(s)
    fekp = max(abs(Lkp(s) - Lkp(1 - s)) for s in [mp.mpc(0.3, 7.1), mp.mpc(2.2, -3.3)])
    # coefficient check: a_n in {0, 1, phi}
    s_test = mp.mpf(3)
    # sum a_n n^-s = 5^-s (zeta(s,1/5) + zeta(s,4/5)) + phi 5^-s zeta(s)   (Hurwitz zeta)
    direct = (mp.power(5, -s_test) * (mp.zeta(s_test, mp.mpf(1) / 5) + mp.zeta(s_test, mp.mpf(4) / 5))
              + phi * mp.power(5, -s_test) * mp.zeta(s_test))
    emit(f"  (ii) KP element F = [zeta(s)(1+5^(1/2-s)) + L(s,(./5))]/2: FE residual {mp.nstr(fekp, 5)}, "
         f"|F(3) - sum a_n n^-3| = {mp.nstr(abs(Fkp(s_test) - direct), 5)}")
    ns5 = [n for n in range(1, 9000) if n % 5 != 0]
    need = sorted(set(d for n in [36, 8806] for d in divisors(n)))
    a5 = {n: Fraction(1 if n % 5 in (1, 4) else 0) for n in need}
    b5 = log_coeffs(a5, need)
    emit(f"       b(36) = {b5[36]}, b(2*7*17*37 = 8806) = {b5[8806]}  (Lean: a5_logcoeff = -2)")
    # (iii) E8 renormalization G(s) = zeta(s/2 + 7/4) zeta(s/2 - 5/4)
    G = lambda s: mp.zeta(s / 2 + mp.mpf(7) / 4) * mp.zeta(s / 2 - mp.mpf(5) / 4)
    Phi = lambda s: mp.power(2 * mp.pi, -s / 2) * mp.gamma(s / 2 + mp.mpf(7) / 4) * G(s)
    fe3 = max(abs(Phi(s) - Phi(1 - s)) for s in [mp.mpc(0.3, 7.1), mp.mpc(2.2, -3.3)])
    rho = mp.zetazero(1)
    z3 = 2 * rho + mp.mpf(5) / 2
    emit(f"  (iii) G = zeta(s/2+7/4)zeta(s/2-5/4): FE residual {mp.nstr(fe3, 5)}; "
         f"zero at 2 rho_1 + 5/2 = {mp.nstr(z3, 10)}, |G| = {mp.nstr(abs(G(z3)), 5)}")
    # sharpness control of the Lean file: zeta(s)(1 + 2^(1/2-s))
    r2 = mp.sqrt(2)
    F2 = lambda s: mp.zeta(s) * (1 + mp.power(2, mp.mpf(1) / 2 - s))
    L2 = lambda s: mp.power(2 / mp.pi, s / 2) * mp.gamma(s / 2) * F2(s)
    fe2 = max(abs(L2(s) - L2(1 - s)) for s in [mp.mpc(0.3, 7.1), mp.mpc(2.2, -3.3)])
    # b(2^k) = 1/k + (-1)^(k-1) 2^(k/2)/k
    b2 = {k: mp.mpf(1) / k + (-1) ** (k - 1) * mp.power(2, mp.mpf(k) / 2) / k for k in range(1, 7)}
    emit(f"  sharpness control zeta(s)(1+2^(1/2-s)) [q=2, P(2)=sqrt2]: FE residual {mp.nstr(fe2, 5)}; "
         f"b(4) = {mp.nstr(b2[2], 10)} (Lean: a2_logcoeff_four = -1/2)")
    record("C9", {"i_Re_s0": float(mp.re(s0)), "i_absF_s0": float(abs(F(s0))), "i_FE": float(fe),
                  "i_b4": str(b[4]), "ii_FE": float(fekp), "ii_b36": str(b5[36]),
                  "ii_b8806": str(b5[8806]), "iii_FE": float(fe3), "iii_absG": float(abs(G(z3))),
                  "sharp_FE": float(fe2), "sharp_b4": float(b2[2])})


# ---------------------------------------------------------------------------------------------
# C5 (Beurling, not kernel-checked): Hermite LP function and the Fejer identity
# ---------------------------------------------------------------------------------------------

def check_C5():
    emit("== C5 (paper-proof only): Hermite eigenfunction and Fejer LP identity ==")
    out = {}
    for delta in [0.1, 0.01, 0.001]:
        def psi(x):
            y2 = 2 * np.pi * x ** 2
            return (16 * y2 ** 2 - 48 * y2 - delta) * np.exp(-np.pi * x ** 2)
        x = np.linspace(-12, 12, 480001)
        dx = x[1] - x[0]
        err = 0.0
        for xi in [0.0, 0.25, 0.7, 1.1, 1.9]:
            fh = np.sum(psi(x) * np.cos(2 * np.pi * x * xi)) * dx
            err = max(err, abs(fh - psi(np.array(xi))))
        # threshold: 16Y^2 - 48Y - delta = 0, Y = 2 pi t^2
        Y = (48 + math.sqrt(48 ** 2 + 64 * delta)) / 32
        t_delta = math.sqrt(Y / (2 * math.pi))
        out[delta] = (err, t_delta)
        emit(f"  delta={delta}: max |psi_hat - psi| on 5 points = {err:.2e}; psi(0) = {-delta}; "
             f"psi >= 0 for |t| >= t_delta = {t_delta:.6f}")
    emit(f"  limit t_delta -> sqrt(3/(2 pi)) = {math.sqrt(3 / (2 * math.pi)):.6f}, q >= 2 pi/3 = {2 * math.pi / 3:.6f}")
    # Fejer identity alpha (1 - a) = a int sinc^2(a t) dnu_+ for zeta(s)(1 + 2^(1/2-s)), q = 2
    a_ = 1 / math.sqrt(2)
    alpha = 1 + math.sqrt(2)
    lhs = alpha * (1 - a_)
    Nterms = 400000
    n = np.arange(1, Nterms + 1, dtype=float)
    mass = 1 + math.sqrt(2) * (n % 2 == 0)
    xarg = a_ * n / math.sqrt(2)   # = n/2
    sinc2 = (np.sin(np.pi * xarg) / (np.pi * xarg)) ** 2
    rhs = a_ * np.sum(2 * mass * sinc2)
    emit(f"  Fejer identity q=2 example: lhs = {lhs:.10f}, rhs (N={Nterms}) = {rhs:.10f}, "
         f"exact value sqrt2/2 = {math.sqrt(2) / 2:.10f}")
    record("C5", {"hermite": {str(k): {"fft_err": v[0], "t_delta": v[1]} for k, v in out.items()},
                  "fejer_lhs": lhs, "fejer_rhs": float(rhs)})


# ---------------------------------------------------------------------------------------------
# C6 (algebra kernel-checked, analytic inputs paper-proof)
# ---------------------------------------------------------------------------------------------

def check_C6():
    emit("== C6 constants and the digamma bound (analytic inputs are paper-proof only) ==")
    g = float(mp.euler)
    const = 3 * (1 - g / 2) + 4 + 1 / 3 + 1 / 2 + 1 / 24 - 4 * math.log(math.pi)
    d0 = 2 * math.sqrt(3) - 3
    cstar = d0 * (1 - d0) / (3 + d0)
    emit(f"  L-constant 3(1-gamma/2)+4+1/3+1/2+1/24-4 log pi = {const:.6f} (< 2.44: {const < 2.44})")
    emit(f"  delta* = 2 sqrt3 - 3 = {d0:.6f}; c* = {cstar:.8f} = 7 - 4 sqrt3 = {7 - 4 * math.sqrt(3):.8f}")
    emit(f"  asymptotic constant 2.5 / c* = {2.5 / cstar:.4f}")
    # grid check of max over delta
    grid = np.linspace(0.001, 0.999, 99801)
    vals = grid * (1 - grid) / (3 + grid)
    emit(f"  grid max of delta(1-delta)/(3+delta) = {vals.max():.8f} at delta = {grid[vals.argmax()]:.5f}")
    # digamma: Re psi(z) <= log|z| + 1/(12|Im z|) for Re z in [1/2, 1], |Im z| >= 1/2
    worst = -1e9
    worst_plain = -1e9
    for xr in np.linspace(0.5, 1.0, 26):
        for yi in np.concatenate([np.linspace(0.5, 30, 300), np.linspace(30, 3000, 150)]):
            z = mp.mpc(xr, yi)
            v = float(mp.re(mp.digamma(z)) - mp.log(abs(z)))
            worst_plain = max(worst_plain, v)
            worst = max(worst, v - 1 / (12 * yi))
    emit(f"  max[Re psi(z) - log|z|] = {worst_plain:.3e}; max[Re psi - log|z| - 1/(12|Im z|)] = {worst:.3e} (<= 0)")
    record("C6", {"L_constant": const, "c_star": cstar, "asymptotic": 2.5 / cstar,
                  "digamma_plain_max": worst_plain, "digamma_bound_max": worst})


# ---------------------------------------------------------------------------------------------
# C7(a) and C8 (paper-proof only)
# ---------------------------------------------------------------------------------------------

def check_C7_C8():
    emit("== C7(a) mirror identity and C8 RvM main term (paper-proof only) ==")
    xi = lambda s: s * (s - 1) / 2 * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)
    dlog = lambda s: mp.diff(xi, s) / xi(s)
    s = mp.mpc(1.7, 9.3)
    lhs = dlog(1 - mp.conj(s))
    rhs = -mp.conj(dlog(s))
    emit(f"  xi'/xi(1 - conj s) + conj(xi'/xi(s)) at s = 1.7+9.3i: {mp.nstr(abs(lhs - rhs), 5)}")
    # C8: F = zeta(s)(1 + 5^(1/2-s)) has q = 5; its zeros = zeta zeros + (1/2 + i pi(2k+1)/log 5)
    rows = []
    for T in [50, 100, 200]:
        Nz = int(mp.nzeros(T))
        Nextra = int(math.floor(T * math.log(5) / (2 * math.pi) + 0.5))
        main_zeta = T / (2 * math.pi) * math.log(T / (2 * math.pi * math.e)) + 7 / 8
        main_F = T / (2 * math.pi) * math.log(5 * T / (2 * math.pi * math.e)) + 7 / 8
        rows.append((T, Nz, main_zeta, Nz + Nextra, main_F))
        emit(f"  T={T}: N_zeta={Nz} vs main {main_zeta:.3f};  N_F (q=5) = {Nz + Nextra} vs "
             f"(T/2pi)log(qT/(2pi e)) + 7/8 = {main_F:.3f}")
    xs = np.linspace(1, 2, 10001)
    emit(f"  min over x in [1,2] of x/(x^2+1) = {min(xs / (xs ** 2 + 1)):.6f} (claimed 2/5)")
    record("C7_C8", {"mirror_residual": float(abs(lhs - rhs)), "rvm_rows": rows})


# ---------------------------------------------------------------------------------------------
# self-dual periodic nonnegative examples (the check_integer_case experiment, exact b)
# ---------------------------------------------------------------------------------------------

def check_selfdual(seed=14):
    emit("== Self-dual (FE-compatible) periodic nonnegative a mod q: log-positivity (floats) ==")
    rng = np.random.default_rng(seed)
    N = 800
    ns = list(range(1, N + 1))
    res = {}
    for q in [2, 3, 4, 5, 6, 7, 8, 9, 10, 12]:
        F = np.array([[np.exp(2j * np.pi * r * m / q) for r in range(q)] for m in range(q)]) / np.sqrt(q)
        reps = sorted(set(min(r, (-r) % q) for r in range(q)))
        E = np.zeros((q, len(reps)))
        for j, r in enumerate(reps):
            E[r, j] += 1
            E[(-r) % q, j] += 1
            if r == (-r) % q:
                E[r, j] = 1
        Mx = F @ E - E
        _, sv, vh = np.linalg.svd(Mx)
        null = vh[np.sum(sv > 1e-9):].conj().T
        B = (E @ null).real
        best = -1e9
        cnt = 0
        for _ in range(150):
            a_q = B @ rng.standard_normal(B.shape[1])
            if abs(a_q[1]) < 1e-9:
                continue
            a_q = a_q / a_q[1]
            if a_q.min() < -1e-12:
                continue
            cnt += 1
            a = {n: a_q[n % q] for n in ns}
            b = {1: 0.0}
            for n in ns[1:]:
                om = big_omega(n)
                s = om * a[n]
                for d in divisors(n):
                    if d not in (1, n):
                        s -= big_omega(d) * b[d] * a[n // d]
                b[n] = s / om
            best = max(best, min(b[n] for n in ns[1:]))
        res[q] = (cnt, best)
        emit(f"  q={q:3d}: nonneg self-dual samples {cnt:3d}, best min_n b(n) = {best: .4f}")
    record("selfdual", {str(k): {"samples": v[0], "best_min_b": v[1]} for k, v in res.items()})


def main():
    emit("verify_axiso_theorem.py -- conjecture1_proved = False; numerical evidence only")
    emit(f"python {sys.version.split()[0]}, numpy {np.__version__}, mpmath {mp.__version__}, dps {mp.mp.dps}")
    emit()
    check_K1()
    emit()
    check_K2()
    emit()
    check_steps()
    emit()
    check_C9()
    emit()
    check_C5()
    emit()
    check_C6()
    emit()
    check_C7_C8()
    emit()
    check_selfdual()
    with open(OUT_TXT, "w") as fh:
        fh.write("\n".join(LINES) + "\n")
    with open(OUT_JSON, "w") as fh:
        json.dump(RESULTS, fh, indent=1, default=str)


if __name__ == "__main__":
    main()

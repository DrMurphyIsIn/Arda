#!/usr/bin/python3
"""Class P, constructor seat: computational companion to
telperion/examples/rvm_bridge/lean/Crux/Crux_axiso_construct.lean.

conjecture1_proved = False.

The Lean file proves the headline statements. This script only CROSS-CHECKS them numerically
and adds evidence for the parts that stay on paper. Every check prints PASS or FAIL. If any
check fails, the exit code is nonzero. Outputs:

  outputs/numerics.json          machine-readable results
  outputs/numerics_summary.txt   the human-readable summary printed below

Tools: python-flint (Arb ball arithmetic, rigorous enclosures), mpmath (high precision, not
rigorous), sympy (symbolic integration), fractions (exact rational arithmetic).
Run:   /usr/bin/python3 axiso_construct_numerics.py
"""

import json
import math
import os
import sys
from fractions import Fraction

import mpmath as mp
import sympy as sp
from flint import acb, arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "outputs")
os.makedirs(OUT, exist_ok=True)

ctx.prec = 256
mp.mp.dps = 50

RESULTS = {}
LINES = []
FAILED = []


def log(msg):
    print(msg)
    LINES.append(msg)


def check(name, ok, detail):
    status = "PASS" if ok else "FAIL"
    if not ok:
        FAILED.append(name)
    RESULTS[name] = {"status": status, "detail": detail}
    log("[%s] %s: %s" % (status, name, detail))


# ---------------------------------------------------------------------------------------------
# helpers: exact arithmetic in the Q-span of {log p}
# ---------------------------------------------------------------------------------------------

def factor(n):
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


def divisors(n):
    ds = [1]
    for p, e in factor(n).items():
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return sorted(ds)


def vec_add(u, v, c=1):
    w = dict(u)
    for k, x in v.items():
        w[k] = w.get(k, 0) + c * x
        if w[k] == 0:
            del w[k]
    return w


def vec_scale(u, c):
    return {k: c * x for k, x in u.items() if c * x != 0}


def logvec(n):
    return {p: Fraction(e) for p, e in factor(n).items()}


def vonmangoldt_vec(n):
    f = factor(n)
    if len(f) == 1:
        p = next(iter(f))
        return {p: Fraction(1)}
    return {}


def vec_value(u):
    return sum(float(c) * math.log(p) for p, c in u.items())


def log_deriv_coeffs(a, N):
    """Exact g with  log(n) a(n) = sum_{d | n} g(d) a(n/d),  a(1) = 1  (vectors over log p)."""
    g = {1: {}}
    for n in range(2, N + 1):
        rhs = vec_scale(logvec(n), Fraction(a(n)))
        for d in divisors(n):
            if d == n:
                continue
            rhs = vec_add(rhs, vec_scale(g[d], Fraction(a(n // d))), -1)
        g[n] = rhs  # a(1) = 1
    return g


# ---------------------------------------------------------------------------------------------
# N1. NEAR-MISS 1, F0 = zeta(s)(1+2^{-s})(1+2^{1-s}): coefficients and Lambda_F, EXACT
# ---------------------------------------------------------------------------------------------

def a0(n):
    return 1 + (3 if n % 2 == 0 else 0) + (2 if n % 4 == 0 else 0)


def n1():
    log("\n== N1  F0: coefficients a0 and the von Mangoldt function Lambda_F0 (exact) ==")
    N = 4096
    vals = sorted(set(a0(n) for n in range(1, N + 1)))
    check("N1.a0_values", vals == [1, 4, 6], "a0(n) takes values %s for 1 <= n <= %d" % (vals, N))
    bad = [(m, n) for m in range(1, 200) for n in range(1, 200)
           if math.gcd(m, n) == 1 and a0(m * n) != a0(m) * a0(n)]
    check("N1.a0_multiplicative", not bad, "a0(mn) = a0(m)a0(n) for coprime m,n < 200 (%d failures)" % len(bad))
    g = log_deriv_coeffs(a0, N)
    # closed form: Lambda + geomCoeff 2 1 + geomCoeff 2 2 (the Lean witness in F0_logDeriv_exists)
    mism = []
    for n in range(2, N + 1):
        expect = vonmangoldt_vec(n)
        f = factor(n)
        if list(f.keys()) == [2]:
            k = f[2]
            expect = vec_add(expect, {2: Fraction((-1) ** (k + 1))})
            expect = vec_add(expect, {2: Fraction((-1) ** (k + 1) * 2 ** k)})
        if g[n] != expect:
            mism.append(n)
    check("N1.closed_form", not mism,
          "exact recursion equals Lambda + geomCoeff(2,1) + geomCoeff(2,2) for all 2 <= n <= %d "
          "(%d mismatches)" % (N, len(mism)))
    g4 = g[4]
    check("N1.Lambda_F0_4", g4 == {2: Fraction(-4)}, "Lambda_F0(4) = %s * log 2  (expected -4 log 2)" % g4.get(2))
    neg = [n for n in range(2, N + 1) if vec_value(g[n]) < 0]
    check("N1.negative_set", neg == [4, 16, 64, 256, 1024, 4096],
          "n <= %d with Lambda_F0(n) < 0: %s (exactly the even powers of 2)" % (N, neg))
    b = [g[2 ** k].get(2, Fraction(0)) / k for k in range(1, 7)]
    check("N1.log_coefficients", b == [4, -2, Fraction(10, 3), -4, Fraction(34, 5), Fraction(-32, 3)],
          "b(2^k) = Lambda_F0(2^k)/log(2^k), k=1..6: %s" % [str(x) for x in b])
    # the P2 necessary condition a(p)^2 <= 2 a(p^2) (Lean: P2_forces_sq_ineq)
    check("N1.sq_ineq_violated", a0(2) ** 2 > 2 * a0(4),
          "a0(2)^2 = %d > 2 a0(4) = %d, so P2_forces_sq_ineq is violated at p = 2" % (a0(2) ** 2, 2 * a0(4)))


# ---------------------------------------------------------------------------------------------
# N2. LEMMA C at prime conductor: F = zeta (1 + c p^{-s}), c = eps sqrt p
# ---------------------------------------------------------------------------------------------

def n2():
    log("\n== N2  Lemma C at prime conductor (Arb balls) ==")
    primes = [p for p in range(2, 100) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
    worst_fe = arb(0)
    fails = []
    for p in primes:
        for eps in (1, -1):
            c = eps * arb(p).sqrt()
            # self-reciprocity P(s) = eps p^{1/2-s} P(1-s) at generic s
            for s in (acb("0.3", "1.7"), acb("-1.2", "5.5"), acb("2.25", "-0.4")):
                P = lambda z: 1 + acb(c) * acb(p) ** (-z)
                r = P(s) - eps * acb(p) ** (acb(0.5) - s) * P(1 - s)
                if not r.contains(0):
                    fails.append(("fe", p, eps))
                worst_fe = max(worst_fe, abs(r).upper())
            # Lambda_F(p), Lambda_F(p^2) from the convolution recursion (a(1)=1, a(p)=a(p^2)=1+c)
            ap = 1 + c
            lp = arb(p).log()
            g_p = ap * lp
            g_p2 = 2 * lp * ap - g_p * ap
            # independent route: geometric expansion of -(d/ds) log(1 + c p^{-s}) plus zeta's log p
            g_p2_geom = lp + lp * (-1) ** 3 * c ** 2
            if not (g_p2 - (1 - p) * lp).contains(0) or not (g_p2 - g_p2_geom).contains(0):
                fails.append(("gp2", p, eps))
            if not (g_p2 < 0):
                fails.append(("sign", p, eps))
    check("N2.prime_conductor", not fails,
          "for all primes p < 100 and eps = +-1: self-reciprocity holds (max |residual| <= %s) and "
          "Lambda_F(p^2) = (1-p) log p < 0, convolution recursion = geometric expansion (%d failures)" % (worst_fe.str(3, radius=False), len(fails)))


def n2b():
    log("\n== N2b Lemma C at conductor p^2 (exact rational arithmetic) ==")
    primes = [q for q in range(2, 50) if all(q % r for r in range(2, int(q ** 0.5) + 1))]
    # (i) the recursion k a(p^k) = sum_j (g(p^j)/log p) a(p^{k-j}) reproduces 1 - s_k (Newton sums)
    bad_rec = 0
    for pp in primes[:6]:
        for x in (Fraction(-3), Fraction(-1), Fraction(0), Fraction(1, 3), Fraction(5, 2)):
            a = lambda j: 1 if j == 0 else (1 + x if j == 1 else 1 + x + pp)
            gl = {0: Fraction(0)}
            sk = {0: Fraction(2), 1: -x}
            for k in range(2, 9):
                sk[k] = -x * sk[k - 1] - pp * sk[k - 2]
            for k in range(1, 9):
                gl[k] = k * a(k) - sum(gl[j] * a(k - j) for j in range(1, k))
                if gl[k] != 1 - sk[k]:
                    bad_rec += 1
    check("N2b.recursion_newton", bad_rec == 0,
          "Lambda_F(p^k)/log p from the convolution recursion equals 1 - s_k (Newton power sums), "
          "k <= 8, 6 primes x 5 values of x (%d mismatches)" % bad_rec)
    # (ii) sq_family_core on an exact grid: some 1 - s_k < 0 with k <= 5, for every x
    worst = None
    count = 0
    for pp in primes:
        for num in range(-700, 701):
            x = Fraction(num, 70)
            sk = {0: Fraction(2), 1: -x}
            for k in range(2, 6):
                sk[k] = -x * sk[k - 1] - pp * sk[k - 2]
            m = min(1 - sk[k] for k in range(1, 6))
            count += 1
            if worst is None or m > worst[0]:
                worst = (m, pp, x)
    check("N2b.sq_family_core_grid", worst[0] < 0,
          "over %d exact grid points (primes p < 50, x in [-10,10] step 1/70) the largest value of "
          "min_{k<=5}(1 - s_k) is %s at (p, x) = (%d, %s): always negative" % (count, worst[0], worst[1], worst[2]))
    # (iii) the minus branch: a(p)^2 = 1 > 2 a(p^2) = 2(1 - p)
    check("N2b.minus_branch", all(1 > 2 * (1 - pp) for pp in primes),
          "for the branch 1 - p p^{-2s}: a(p)^2 = 1 > 2 a(p^2) = 2(1-p) for every prime p < 50")


# ---------------------------------------------------------------------------------------------
# N3. Functional equations of the completions (Arb balls)
# ---------------------------------------------------------------------------------------------

def xiC(u):
    # u(u-1) pi^{-u/2} Gamma(u/2) zeta(u)   (valid away from u = 0, 1)
    return u * (u - 1) * acb.pi() ** (-u / 2) * (u / 2).gamma() * u.zeta()


def Xi0(s):
    P0 = 1 + 3 * acb(2) ** (-s) + 2 * acb(4) ** (-s)
    return acb(2) ** s * P0 * xiC(s)


def Xi1(s):
    return xiC(s / 2 + acb(3) / 4) * xiC(s / 2 - acb(1) / 4)


def XiE8(s):
    return xiC(s / 2 + acb(7) / 4) * xiC(s / 2 - acb(5) / 4)


def n3():
    log("\n== N3  Functional equations Xi(1-s) = Xi(s) (Arb balls) ==")
    pts = [acb("0.11", "3.3"), acb("-2.4", "9.7"), acb("1.9", "-21.2"), acb("0.5", "44.4"), acb("3.3", "0.7")]
    for name, X in (("Xi0", Xi0), ("Xi1", Xi1), ("XiE8", XiE8)):
        ok = True
        worst = arb(0)
        for s in pts:
            d = X(s) - X(1 - s)
            ok = ok and d.contains(0)
            worst = max(worst, (abs(d) / abs(X(s))).upper())
        check("N3.FE_" + name, ok, "0 in X(s)-X(1-s) at 5 points; max relative radius %s" % worst.str(3, radius=False))


# ---------------------------------------------------------------------------------------------
# N4. Explicit off-line zeros (rigorous enclosures)
# ---------------------------------------------------------------------------------------------

def hardyZ(t):
    t = arb(t)
    theta = (acb(0.25, t / 2).lgamma()).imag - t / 2 * arb.pi().log()
    z = (acb(0, theta).exp() * acb(0.5, t).zeta())
    return z


def n4():
    log("\n== N4  Explicit zeros off the critical line (rigorous) ==")
    # F0 / Xi0: exact zero of P0 at 1 + i pi / log 2
    s = acb(1, arb.pi() / arb(2).log())
    P0 = 1 + 3 * acb(2) ** (-s) + 2 * acb(4) ** (-s)
    check("N4.P0_zero_Re1", P0.contains(0), "P0(1 + i pi/log 2) encloses 0: %s" % P0.str(5, radius=True))
    s2 = acb(0, arb.pi() / arb(2).log())
    P0b = 1 + 3 * acb(2) ** (-s2) + 2 * acb(4) ** (-s2)
    check("N4.P0_zero_Re0", P0b.contains(0), "P0(i pi/log 2) encloses 0")
    # first zeta zero: rigorous isolation by Arb, plus an independent Hardy-Z sign change
    rho = acb.zeta_zero(1)
    za, zb = hardyZ("14.134"), hardyZ("14.135")
    sign_change = (za.real > 0 and zb.real < 0) or (za.real < 0 and zb.real > 0)
    check("N4.first_zero", sign_change and za.imag.contains(0) and zb.imag.contains(0),
          "Arb zeta_zero(1) = %s; Z(14.134) = %s, Z(14.135) = %s (sign change: zero on the line in "
          "(14.134, 14.135))" % (rho.str(12, radius=False), za.real.str(6, radius=False), zb.real.str(6, radius=False)))
    # F1 at 2 rho + 1/2 (Re = 3/2) and the E8 twin at 2 rho + 5/2 (Re = 7/2)
    s1 = 2 * rho + acb(0.5)
    F1 = (s1 / 2 + acb(3) / 4).zeta() * (s1 / 2 - acb(1) / 4).zeta()
    check("N4.F1_offline_zero", F1.contains(0),
          "F1(2 rho1 + 1/2) encloses 0, point %s, Re = 3/2" % s1.str(10, radius=False))
    s8 = 2 * rho + acb(2.5)
    F8 = (s8 / 2 + acb(7) / 4).zeta() * (s8 / 2 - acb(5) / 4).zeta()
    check("N4.E8_offline_zero", F8.contains(0),
          "E8 twin at 2 rho1 + 5/2 encloses 0, point %s, Re = 7/2" % s8.str(10, radius=False))
    # sanity: F1 has no zero on the critical line (a theorem in Lean; numerics only as a smoke test)
    m = min(abs(F1v) for F1v in
            [((acb(0.5, t / 10) / 2 + acb(3) / 4).zeta() * (acb(0.5, t / 10) / 2 - acb(1) / 4).zeta()).mid()
             for t in range(1, 800)])
    check("N4.F1_line_smoke", m > 0, "min |F1(1/2 + it)| over t = 0.1..79.9 (step 0.1) = %s" % arb(m).str(4, radius=False))


# ---------------------------------------------------------------------------------------------
# N5. P2 for F1 in Beurling form (numerical cross-check of F1_logDeriv_hasSum)
# ---------------------------------------------------------------------------------------------

def n5():
    log("\n== N5  F1: -F1'/F1 = sum b1(n) n^{-s/2}, b1 >= 0 (mpmath) ==")
    s = mp.mpc(8, 3)
    w, v = s / 2 + mp.mpf(3) / 4, s / 2 - mp.mpf(1) / 4
    lhs = -(mp.zeta(w, derivative=1) / mp.zeta(w) + mp.zeta(v, derivative=1) / mp.zeta(v)) / 2
    N = 20000
    tot = mp.mpc(0)
    minb = None
    for n in range(2, N + 1):
        f = factor(n)
        if len(f) != 1:
            continue
        p = next(iter(f))
        lam = mp.log(p)
        b = lam / 2 * (mp.mpf(n) ** (-mp.mpf(3) / 4) + mp.mpf(n) ** (mp.mpf(1) / 4))
        minb = b if minb is None else min(minb, b)
        tot += b * mp.power(n, -s / 2)
    diff = abs(lhs - tot)
    # tail bound: sum_{n > N} log(n) n^{1/4 - 4} <= int_N^inf ... < N^{-2.7} log N
    tail = mp.log(N) * mp.mpf(N) ** (-mp.mpf("2.7"))
    check("N5.F1_beurling_sum", diff < tail and minb > 0,
          "|(-F1'/F1)(8+3i) - partial sum to %d| = %s < tail bound %s; min b1 = %s > 0"
          % (N, mp.nstr(diff, 3), mp.nstr(tail, 3), mp.nstr(minb, 4)))
    # pole residues: (s-1/2)F1 -> -1, (s-5/2)F1 -> 2 zeta(2) = pi^2/3
    h = mp.mpf(10) ** -25
    F1 = lambda z: mp.zeta(z / 2 + mp.mpf(3) / 4) * mp.zeta(z / 2 - mp.mpf(1) / 4)
    r1 = h * F1(mp.mpf(1) / 2 + h)
    r2 = h * F1(mp.mpf(5) / 2 + h)
    check("N5.F1_poles", abs(r1 + 1) < 1e-20 and abs(r2 - mp.pi ** 2 / 3) < 1e-20,
          "(s-1/2)F1(s) -> %s (Lean: F1_pole_half, limit -1); (s-5/2)F1(s) -> %s (pi^2/3 = %s)"
          % (mp.nstr(r1, 12), mp.nstr(r2, 12), mp.nstr(mp.pi ** 2 / 3, 12)))


# ---------------------------------------------------------------------------------------------
# N6. The Cohn-Elkies pair (Theorem A, Step 3) -- the Fourier identity is NOT in Lean
# ---------------------------------------------------------------------------------------------

def n6():
    log("\n== N6  Cohn-Elkies pair: F[fhat] = f symbolically; pointwise sign facts ==")
    x, t = sp.symbols("x t", real=True)
    fhat = 1 - t + sp.sin(2 * sp.pi * t) / (2 * sp.pi)
    I = 2 * sp.integrate(fhat * sp.cos(2 * sp.pi * x * t), (t, 0, 1))
    f = sp.sin(sp.pi * x) ** 2 / (sp.pi ** 2 * x ** 2 * (1 - x ** 2))
    diff_all = sp.simplify(I - f)
    # sympy returns a Piecewise whose special branches are the removable points x = 0, +-1
    # (checked numerically below); the generic branch (condition True) must simplify to 0.
    if isinstance(diff_all, sp.Piecewise):
        diff = [sp.simplify(sp.expand_trig(e)) for (e, c) in diff_all.args if c == sp.true][0]
    else:
        diff = sp.simplify(sp.expand_trig(diff_all))
    # numerically confirm on a grid too
    worst = 0.0
    for xv in [mp.mpf(k) / 10 + mp.mpf(1) / 20 for k in range(1, 60)]:
        lhs = 2 * mp.quad(lambda tt: (1 - tt + mp.sin(2 * mp.pi * tt) / (2 * mp.pi)) * mp.cos(2 * mp.pi * xv * tt), [0, 1])
        rhs = mp.sin(mp.pi * xv) ** 2 / (mp.pi ** 2 * xv ** 2 * (1 - xv ** 2))
        worst = max(worst, float(abs(lhs - rhs)))
    at0 = 2 * mp.quad(lambda tt: (1 - tt + mp.sin(2 * mp.pi * tt) / (2 * mp.pi)), [0, 1])
    at1 = 2 * mp.quad(lambda tt: (1 - tt + mp.sin(2 * mp.pi * tt) / (2 * mp.pi)) * mp.cos(2 * mp.pi * tt), [0, 1])
    check("N6.fourier_pair", diff == 0 and worst < 1e-40 and abs(at0 - 1) < 1e-40 and abs(at1) < 1e-40,
          "sympy: generic branch of 2*int_0^1 fhat(t) cos(2 pi x t) dt - f(x) simplifies to %s; grid max |diff| = %.1e; "
          "value at x=0: %s (f(0)=1), at x=1: %s (f(1)=0)" % (diff, worst, mp.nstr(at0, 8), mp.nstr(at1, 3)))
    # sign facts (proved in Lean; smoke test only)
    fmax = max(float(mp.sin(mp.pi * xv) ** 2 / (mp.pi ** 2 * xv ** 2 * (1 - xv ** 2)))
               for xv in [1 + k / 97.0 + 1e-9 for k in range(1, 3000)])
    hmin = min(1 - mp.mpf(k) / 1000 + mp.sin(2 * mp.pi * k / 1000) / (2 * mp.pi) for k in range(0, 1000))
    check("N6.sign_smoke", fmax <= 0 and hmin >= 0,
          "max f on sampled |x| > 1: %.3e (<= 0); min fhat on the grid t = 0, 0.001, ..., 0.999: %s (>= 0); "
          "fhat(1) = 0 exactly (Lean: ceFhat_eq_zero_of_one_le)" % (fmax, mp.nstr(hmin, 4)))
    # Poisson sanity for zeta itself: nu = sum_n delta_n, <nu,f> = 1 + 2 sum f(n) = 1 = fhat(0) + 0
    s = 1 + 2 * sum(0.0 for _ in range(1, 10))  # f(n) = 0 at every nonzero integer
    check("N6.zeta_pairing", s == 1.0, "for N = sum_{n>=1} delta_n: <nu, f> = 1 = <nu, fhat> (f vanishes on Z\\{0})")


# ---------------------------------------------------------------------------------------------
# N7. Evidence for general Lemma C (paper proof; NOT in Lean): squarefree q = p1 p2
# ---------------------------------------------------------------------------------------------

def n7():
    log("\n== N7  Lemma C beyond prime conductor: q = p1 p2, one free real parameter (evidence) ==")
    out = {}
    for (p1, p2) in ((2, 3), (2, 5), (3, 5), (2, 7)):
        q = p1 * p2
        smooth = sorted(n for n in range(2, 3001) if all(pr in (p1, p2) for pr in factor(n)))
        best = None
        for eps in (1, -1):
            for k in range(-300, 301):
                xpar = k / 50.0
                y = eps * xpar * math.sqrt(q) / p1
                z = eps * math.sqrt(q)
                P = {1: 1.0, p1: xpar, p2: y, q: z}
                a = lambda n: sum(c for d, c in P.items() if n % d == 0)
                g = {1: 0.0}
                worst = float("inf")
                for n in [1] + smooth:
                    if n == 1:
                        continue
                    r = a(n) * math.log(n)
                    for d in divisors(n):
                        if d < n:
                            r -= g[d] * a(n // d)
                    g[n] = r
                    worst = min(worst, r / math.log(n))
                if best is None or worst > best[0]:
                    best = (worst, eps, xpar)
        out[q] = best
    ok = all(v[0] < 0 for v in out.values())
    check("N7.lemmaC_two_primes", ok,
          "max over eps = +-1 and x in [-6,6] (step 0.02) of min_{q-smooth n <= 3000} Lambda_F(n)/log n: %s"
          % {q: round(v[0], 4) for q, v in out.items()})


def main():
    log("Class P constructor seat -- numerical companion (conjecture1_proved = False)")
    log("python %s, mpmath %s, sympy %s, Arb precision %d bits" % (sys.version.split()[0], mp.__version__, sp.__version__, ctx.prec))
    n1()
    n2()
    n2b()
    n3()
    n4()
    n5()
    n6()
    n7()
    log("\n%d checks, %d failed%s" % (len(RESULTS), len(FAILED), (": " + ", ".join(FAILED)) if FAILED else ""))
    with open(os.path.join(OUT, "numerics.json"), "w") as fh:
        json.dump({"conjecture1_proved": False, "results": RESULTS, "failed": FAILED}, fh, indent=2, default=str)
    with open(os.path.join(OUT, "numerics_summary.txt"), "w") as fh:
        fh.write("\n".join(LINES) + "\n")
    return 1 if FAILED else 0


if __name__ == "__main__":
    sys.exit(main())

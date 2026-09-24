"""
Crux2 unified-barrier, BUILD stage: independent numerical cross-checks of the NEW kernel theorems in
telperion/examples/li_positivity/lean/Crux/Crux2_unified_barrier.lean.  conjecture1_proved = False.

These are COMPUTED checks (mpmath, 40 digits; the integer identities are exact).  The Lean file is
the proof; this script only guards against a mis-stated theorem.

N1  support-prime duality (`surg_explicit_formula`): for W_{p,c} with c^2 != 4p, alpha with
    2 cos(alpha) = -c/sqrt p, and a test g, the sum over k of h((alpha+2 pi k)/L) + h((-alpha+2 pi k)/L)
    (L = log p, h(z) = int g(x) e^{ixz} dx) equals
      2 L g(0)                                         if supp g in (-L, L),
      2 L (g(0) - (c/(2 sqrt p)) (g(L) + g(-L)))       if supp g in (-2L, 2L),
    and the second formula FAILS once supp g reaches 2L (the m = +-2 lattice points appear).
    Tests: centred cardinal B-splines (explicit entire Fourier transform (sin(zw/2)/(zw/2))^m).
N1b the sign consequence: the positive-type test g = f * f~, f = bump(x - L/2) + bump(x + L/2),
    has surgery zero-sum 4 L Phi(0) (1 - c/(2 sqrt p)): NEGATIVE iff c > 2 sqrt p (off-line).
N2  (X6) `robust_positivity_iff`: the defect sum_m max(0, t_m - 1) log p / p^m converges for
    |c| < p + 1 and its partial sums grow linearly at |c| = p + 1.
N3  `tLoc_large` / `surgery_not_selberg`: for every m, t_m^2 > p^m or |t_{2m}| >= p^m (exact, all
    |c| <= p + 1, including on-line c), hence max_{k<=K} |t_k| / p^{k/2} >= 1 for every K.
N4  `LSeries_aW`: sum_n a_W(n) n^{-s} = zeta(s)(1 + c p^{-s} + p p^{-2s}) at Re s > 1.
N5  `aW_isMultiplicative`: a_W(mn) = a_W(m) a_W(n) for coprime m, n.
N6  `surg_edge_iff`: at c = p + 1 the surgery factor vanishes at s = 1 + i pi / log p (Re s = 1).
N7  `prime_square_surgery`: for A = 2p + 1 the log-coefficients of zeta(s)(1 + A p^-2s + p^2 p^-4s)
    satisfy P2 at p, p^2, p^3 and at every prime square, fail at p^4 (exact rationals, from the
    Newton identities), the L-series identity holds at Re s > 1, and the completion factor
    2 cosh((s-1/2) log p^2) + A/p vanishes at a point with 1/2 < Re s < 1.
"""
import mpmath as mp
from math import comb, gcd, isqrt

mp.mp.dps = 40
ok = True


def check(name, cond, info=""):
    global ok
    ok = ok and bool(cond)
    print(("PASS " if cond else "FAIL ") + name + ("  " + info if info else ""))


# ---------------------------------------------------------------- B-spline tests
def bspline(m, x):
    """Centred cardinal B-spline M_m (support [-m/2, m/2], integral 1)."""
    x = mp.mpf(x)
    s = mp.mpf(0)
    for j in range(m + 1):
        u = x + mp.mpf(m) / 2 - j
        if u > 0:
            s += (-1) ** j * comb(m, j) * u ** (m - 1)
    return s / mp.factorial(m - 1)


def g_spline(m, w, x):
    return bspline(m, x / w) / w


def h_spline(m, w, z):
    """int g(x) e^{ixz} dx for g(x) = M_m(x/w)/w: (sin(zw/2)/(zw/2))^m (entire)."""
    u = z * w / 2
    if abs(u) < mp.mpf(10) ** -30:
        return mp.mpf(1)
    return (mp.sin(u) / u) ** m


def zero_sum(p, c, hfun, K=4000):
    L = mp.log(p)
    alpha = mp.acos(-mp.mpf(c) / (2 * mp.sqrt(p)))
    tot = mp.mpc(0)
    for k in range(-K, K + 1):
        tot += hfun((alpha + 2 * mp.pi * k) / L) + hfun((-alpha + 2 * mp.pi * k) / L)
    return tot, alpha


m = 8   # C^6 test; h decays like |z|^-8 on horizontal lines, so K = 4000 terms suffice
for (p, c) in [(29, 11), (5, 5), (41, 13), (7, 3), (29, 10)]:
    L = mp.log(p)
    for ratio in [0.7, 0.99, 1.5, 1.99, 2.5]:
        a = ratio * L                # support radius
        w = 2 * a / m                # support [-m w/2, m w/2] = [-a, a]
        hf = lambda z: h_spline(m, w, z)
        gf = lambda x: g_spline(m, w, x)
        S, alpha = zero_sum(p, c, hf)
        # the two zeros are simple and the branches disjoint: sin(alpha) != 0
        small = 2 * L * gf(0)
        two = 2 * L * (gf(0) - (mp.mpf(c) / (2 * mp.sqrt(p))) * (gf(L) + gf(-L)))
        if ratio < 1:
            check(f"N1 (p,c)=({p},{c}) supp/L={ratio}: zero-sum = 2L g(0) (c-independent)",
                  abs(S - small) < mp.mpf(10) ** -10, f"sum={mp.nstr(S.real, 14)} 2Lg0={mp.nstr(small, 14)}")
        if ratio < 2:
            check(f"N1 (p,c)=({p},{c}) supp/L={ratio}: zero-sum = 2L(g0 - c/(2sqrt p)(gL + g-L))",
                  abs(S - two) < mp.mpf(10) ** -10, f"sum={mp.nstr(S.real, 14)} formula={mp.nstr(two, 14)}")
        else:
            check(f"N1 (p,c)=({p},{c}) supp/L={ratio}: three-point formula FAILS beyond 2L (as stated)",
                  abs(S - two) > mp.mpf(10) ** -6, f"sum={mp.nstr(S.real, 14)} formula={mp.nstr(two, 14)}")
    check(f"N1 (p,c)=({p},{c}) zeros simple / branches disjoint (sin alpha != 0)",
          abs(mp.sin(alpha)) > mp.mpf(10) ** -20, f"alpha={mp.nstr(alpha, 10)}")

# N1b sign of the surgery zero-sum on the positive-type test f * f~, f = bump(x-L/2) + bump(x+L/2)
for (p, c) in [(29, 11), (5, 5), (41, 13), (29, 10), (7, 3)]:
    L = mp.log(p)
    mm = 4
    wphi = (L / 4) / (mm / 2)        # bump phi = M_4(x/w)/w with support [-L/4, L/4]
    # g = f*f~ = 2 Phi + Phi(.-L) + Phi(.+L), Phi = phi*phi = M_8(x/w)/w (B-spline convolution)
    hPhi = lambda z: h_spline(2 * mm, wphi, z)
    hg = lambda z: hPhi(z) * (2 + mp.exp(1j * z * L) + mp.exp(-1j * z * L))
    S, alpha = zero_sum(p, c, hg, K=3000)
    Phi0 = g_spline(2 * mm, wphi, 0)
    pred = 4 * L * Phi0 * (1 - mp.mpf(c) / (2 * mp.sqrt(p)))
    offline = c * c > 4 * p
    check(f"N1b (p,c)=({p},{c}) positive-type two-bump test: zero-sum = 4 L Phi(0)(1 - c/(2 sqrt p))",
          abs(S - pred) < mp.mpf(10) ** -8, f"sum={mp.nstr(S.real, 12)} pred={mp.nstr(pred, 12)}")
    check(f"N1b (p,c)=({p},{c}) sign: negative iff off-line (c^2 > 4p: {offline})",
          (S.real < 0) == offline)


# ---------------------------------------------------------------- local power sums
def t_seq(p, c, M):
    """t_m = x1^m + x2^m for x^2 + c x + p (exact integers), m = 0..M."""
    t = [2, -c]
    for n in range(2, M + 1):
        t.append(-c * t[-1] - p * t[-2])
    return t


# N2 robust positivity defect.  Below the trivial bound the kernel proof bounds the term at p^m by
# 2 log p (R/p)^m with R = max(sqrt p, bigRoot) < p; we check that termwise bound and the resulting
# geometric tail bound.  At or beyond the bound the partial sums grow linearly.
for (p, c) in [(5, 5), (5, 6), (5, -6), (29, 29), (29, 30), (29, -30), (7, 3), (29, 11)]:
    M = 400
    t = t_seq(p, c, M)
    L = mp.log(p)
    parts = {}
    s = mp.mpf(0)
    below = abs(c) < p + 1
    if c * c > 4 * p:
        R = (abs(c) + mp.sqrt(c * c - 4 * p)) / 2
    else:
        R = mp.sqrt(p)
    termwise = True
    for mth in range(1, M + 1):
        term = max(0, t[mth] - 1) * L / mp.mpf(p) ** mth
        if below and term > 2 * L * (R / p) ** mth * (1 + mp.mpf(10) ** -30):
            termwise = False
        s += term
        if mth in (50, 100, 200, 400):
            parts[mth] = s
    if below:
        tail = 2 * L * (R / p) ** (M + 1) / (1 - R / p)
        check(f"N2 (p,c)=({p},{c}) |c|<p+1: term at p^m <= 2 log p (R/p)^m, R={mp.nstr(R, 8)} < p",
              termwise and R < p, f"B in [{mp.nstr(parts[M], 10)}, {mp.nstr(parts[M] + tail, 10)}]")
    else:
        growth = parts[400] - parts[200]
        check(f"N2 (p,c)=({p},{c}) |c|>=p+1: defect partial sums grow (divergence)",
              growth > 10, "S50,S100,S200,S400=" + ", ".join(mp.nstr(parts[k], 6) for k in (50, 100, 200, 400)))

# N3 Selberg dichotomy (exact integers)
allgood = True
worst = None
for p in [2, 3, 5, 7, 11, 29]:
    for c in range(-p - 1, p + 2):
        t = t_seq(p, c, 160)
        for mth in range(1, 80):
            if not (t[mth] ** 2 > p ** mth or abs(t[2 * mth]) >= p ** mth):
                allgood = False
                worst = (p, c, mth)
check("N3 t_m^2 > p^m or |t_2m| >= p^m for all primes p<=29, |c|<=p+1, m<80 (exact)", allgood,
      "" if allgood else str(worst))
for (p, c) in [(5, 0), (5, 3), (7, 5), (29, 10)]:     # on-line surgeries too
    t = t_seq(p, c, 200)
    ratios = [abs(t[k]) / mp.mpf(p) ** (mp.mpf(k) / 2) for k in range(1, 201)]
    check(f"N3 on-line (p,c)=({p},{c}): sup_k |t_k|/p^(k/2) >= 1 (Selberg theta<1/2 fails)",
          max(ratios[100:]) >= 1, "max over k in [101,200] = " + mp.nstr(max(ratios[100:]), 6))


# N4 L-series identity and N5 multiplicativity
def aW(p, c, n):
    return 1 + (c if n % p == 0 else 0) + (p if n % (p * p) == 0 else 0)


for (p, c) in [(5, 5), (29, 11), (7, -3)]:
    s = mp.mpc(3, 2)
    N = 20000
    part = mp.fsum(aW(p, c, n) * mp.power(n, -s) for n in range(1, N + 1))
    tail_bound = (1 + abs(c) + p) * mp.power(N, -2) / 2
    rhs = mp.zeta(s) * (1 + c * mp.power(p, -s) + p * mp.power(p, -2 * s))
    check(f"N4 (p,c)=({p},{c}) L(a_W, 3+2i) = zeta(s)(1 + c p^-s + p p^-2s)",
          abs(part - rhs) < 2 * tail_bound, f"|diff|={mp.nstr(abs(part - rhs), 3)} tail<={mp.nstr(tail_bound, 3)}")
    good = all(aW(p, c, a * b) == aW(p, c, a) * aW(p, c, b)
               for a in range(1, 200) for b in range(1, 200) if gcd(a, b) == 1)
    check(f"N5 (p,c)=({p},{c}) a_W multiplicative on coprime pairs < 200", good)

# N6 edge failure exactly at the trivial bound
for p in [5, 29]:
    c = p + 1
    s = 1 + 1j * mp.pi / mp.log(p)
    val = 2 * mp.cosh((s - mp.mpf(1) / 2) * mp.log(p)) + c / mp.sqrt(p)
    check(f"N6 c=p+1={c}: surg vanishes at s = 1 + i pi/log p (edge fails at Re s = 1)",
          abs(val) < mp.mpf(10) ** -30, f"|surg|={mp.nstr(abs(val), 3)}")

# N7 prime-square surgery
from fractions import Fraction
for p in [3, 5, 7, 29]:
    A = 2 * p + 1
    e = {0: 1, 2: A, 4: p * p}
    # Newton: k e_k = -sum_{i<k} s_{k-i} e_i  -> power sums s_k (exact rationals)
    sp = {}
    for k in range(1, 13):
        acc = Fraction(0)
        for i in range(1, k):
            acc += sp[i] * e.get(k - i, 0)
        sp[k] = -k * e.get(k, 0) - acc
    b = {k: Fraction(1, k) - sp[k] / k for k in range(1, 13)}   # b(p^k) = 1/k - s_k/k
    okP2 = b[1] >= 0 and b[2] >= 0 and b[3] >= 0 and b[4] < 0
    check(f"N7 p={p}, A={A}: b(p)={b[1]}, b(p^2)={b[2]}, b(p^3)={b[3]} >= 0 > b(p^4)={b[4]}", okP2)
    # agreement with the Lean formula s_{2j} = 2 t_j, t = power sums of y^2 + A y + p^2
    t = [2, -A]
    for n in range(2, 7):
        t.append(-A * t[-1] - p * p * t[-2])
    agree = all(sp[2 * j] == 2 * t[j] for j in range(1, 7)) and all(sp[2 * j + 1] == 0 for j in range(0, 6))
    check(f"N7 p={p}: Newton power sums = (0 at odd k, 2 t_(k/2) at even k), as in `s4`", agree)
    # L-series identity at s = 3 + i
    ss = mp.mpc(3, 1)
    def a4(n):
        tot = 0
        for d, v in ((1, 1), (p * p, A), (p ** 4, p * p)):
            if n % d == 0:
                tot += v
        return tot
    N = 20000
    part = mp.fsum(a4(n) * mp.power(n, -ss) for n in range(1, N + 1))
    rhs = mp.zeta(ss) * (1 + A * mp.power(p, -2 * ss) + p * p * mp.power(p, -4 * ss))
    check(f"N7 p={p}: L(a, 3+i) = zeta(s)(1 + A p^-2s + p^2 p^-4s)", abs(part - rhs) < 1e-6,
          f"|diff|={mp.nstr(abs(part - rhs), 3)}")
    # off-line zero of the completion factor in the strip
    L2 = 2 * mp.log(p)
    eta = mp.acosh(mp.mpf(A) / (2 * p))
    z = mp.mpf(1) / 2 + eta / L2 + 1j * mp.pi / L2
    val = 2 * mp.cosh((z - mp.mpf(1) / 2) * L2) + mp.mpf(A) / p
    check(f"N7 p={p}: completion factor zero at Re s = {mp.nstr(z.real, 8)} in (1/2, 1)",
          abs(val) < 1e-30 and 0.5 < z.real < 1, f"|value|={mp.nstr(abs(val), 3)}")

print("ALL PASS" if ok else "SOME CHECK FAILED")

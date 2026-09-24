"""Numerical cross-check of every closed form proved in
telperion/examples/rvm_bridge/lean/Crux/CruxFQ_negative_control.lean (mpmath, 30 digits, single process).

conjecture1_proved = False.  Trust class: COMPUTED (floating point, not interval-certified).  The point
is only to confirm that each Lean statement says what the README says it says; the kernel is the proof.
"""
import mpmath as mp

mp.mp.dps = 30


def log_deriv_coeffs(a, N):
    """Lambda_F(n), F = sum a[n] n^{-s}, a[1] = 1, from a(n) log n = sum_{d|n} Lambda(d) a(n/d)."""
    Lam = [mp.mpf(0)] * (N + 1)
    divs = [[] for _ in range(N + 1)]
    for d in range(2, N + 1):
        for m in range(d, N + 1, d):
            divs[m].append(d)
    for n in range(2, N + 1):
        s = a[n] * mp.log(n)
        for d in divs[n]:
            if d < n:
                s -= Lam[d] * a[n // d]
        Lam[n] = s
    return Lam


def is_prime_power(n):
    if n < 2:
        return False
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            return n == 1
        p += 1
    return True


def vonmangoldt(n):
    if not is_prime_power(n):
        return mp.mpf(0)
    p = 2
    while n % p:
        p += 1
    return mp.log(p)


def section(t):
    print("\n==", t)


# ---------------- B. Davenport-Heilbronn ----------------
section("B. DH dual weights (Lean: dh_dual_values, dh_dual_negative_atom, dh_dual_off_prime_powers)")
k = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
chi = [0, 1, k, -k, -1]
N = 200
a = [mp.mpf(0)] + [chi[n % 5] for n in range(1, N + 1)]
L = log_deriv_coeffs(a, N)
closed = {2: k * mp.log(2), 3: -k * mp.log(3), 4: -(2 + k * k) * mp.log(2), 6: (1 + k * k) * mp.log(6)}
print("kappa =", mp.nstr(k, 15), " (0 < kappa < 1)")
for n, v in closed.items():
    print("  n=%d  recursion %s  Lean closed form %s  diff %s" % (n, mp.nstr(L[n], 15), mp.nstr(v, 15),
                                                                  mp.nstr(L[n] - v, 3)))
neg = [n for n in range(2, N) if L[n] < -mp.mpf('1e-25')]
npp = [n for n in range(2, N) if abs(L[n]) > mp.mpf('1e-25') and not is_prime_power(n)]
print("  n<200: %d negative values; %d non-prime-power n with Lambda_D(n) != 0 (first: %s)"
      % (len(neg), len(npp), npp[:8]))

# ---------------- C. W2 ----------------
section("C. W2 two-prime defect (Lean: W2_dual_defect, W2_fooling_instance) and Lee-Yang (LY2_leeYang_iff)")
p1, p2 = 101, 10007
aa = 1 + mp.mpf('1e-4')
# coefficients of zeta * E_a at the divisors of p1 p2 (all that the recursion at p1 p2 uses)
c = {1: mp.mpf(1), p1: 1 + aa * mp.sqrt(p1), p2: 1 + aa * mp.sqrt(p2),
     p1 * p2: 1 + aa * mp.sqrt(p1) + aa * mp.sqrt(p2) + mp.sqrt(p1 * p2)}
Lp1 = c[p1] * mp.log(p1)
Lp2 = c[p2] * mp.log(p2)
Lpq = c[p1 * p2] * mp.log(p1 * p2) - Lp1 * c[p2] - Lp2 * c[p1]
print("  Lambda_W2(101*10007): recursion %s ; Lean closed form sqrt(p1p2)(1-a^2)log(p1p2) = %s"
      % (mp.nstr(Lpq, 12), mp.nstr(mp.sqrt(p1 * p2) * (1 - aa * aa) * mp.log(p1 * p2), 12)))
# Lee-Yang: for real a, 1 + a(z+w) + zw has a zero with |z|,|w| < 1 iff |a| > 1
for av in [mp.mpf('0.5'), mp.mpf('-0.99'), mp.mpf(1), mp.mpf('1.0001'), mp.mpf(-2)]:
    if abs(av) > 1:
        r = -av + mp.sqrt(av * av - 1) if av > 1 else -av - mp.sqrt(av * av - 1)
        print("  a=%s: witness r=%s, |r|<1: %s, P(r,r)=%s  -> not Lee-Yang" %
              (av, mp.nstr(r, 10), abs(r) < 1, mp.nstr(1 + 2 * av * r + r * r, 3)))
    else:
        # sample: min over a grid of |P| on the polydisc |z|,|w| <= 0.999 is attained ... report min |w| on zero set
        worst = mp.mpf(10)
        for i in range(40):
            for j in range(40):
                z = mp.mpf(i) / 41 * mp.expjpi(mp.mpf(2) * j / 40)
                if abs(av + z) > 1e-20:
                    w = -(1 + av * z) / (av + z)
                    worst = min(worst, abs(w))
        print("  a=%s: on the zero set, |z|<1 forces |w| >= %s (>= 1: Lee-Yang)" % (av, mp.nstr(worst, 8)))

# ---------------- D. finite rank ----------------
section("D. finite-rank trichotomy (Lean: qw_bounded_iff, Qc_zeros_on_line_iff, quad_roots_unimodular_iff)")


def qw(c, K):
    w = [mp.mpf(2), -c]
    for kk in range(2, K + 1):
        w.append(-c * w[kk - 1] - w[kk - 2])
    return w


for cv in [mp.mpf('1.5'), mp.mpf(2), mp.mpf(-2), mp.mpf('2.001'), mp.sqrt(5), 11 / mp.sqrt(29), mp.mpf(-3)]:
    w = qw(cv, 200)
    disc = mp.sqrt(mp.mpc(cv * cv - 4))
    roots = [(-cv + disc) / 2, (-cv - disc) / 2]   # roots of x^2 + c x + 1 (double at |c| = 2)
    print("  c=%-10s max_{k<=200}|qw| = %-12s |roots| = %s" % (mp.nstr(cv, 6), mp.nstr(max(abs(x) for x in w), 6),
                                                               [mp.nstr(abs(r), 8) for r in roots]))
phi = (1 + mp.sqrt(5)) / 2
w = qw(mp.sqrt(5), 12)
print("  golden: qw(sqrt5,k) vs (-1)^k (phi^k+phi^-k):",
      [(kk, mp.nstr(w[kk], 8), mp.nstr((-1) ** kk * (phi ** kk + phi ** -kk), 8)) for kk in range(1, 7)])
alpha, beta = -mp.sqrt(5) * phi, -mp.sqrt(5) / phi
Nk = [5 ** kk + 1 - (alpha ** kk + beta ** kk) for kk in range(1, 16)]
print("  golden counts N_k = 5^k+1-(alpha^k+beta^k), k=1..8:", [int(mp.nint(x)) for x in Nk[:8]],
      " all > 0 up to k=15:", all(x > 0 for x in Nk))
XiA = lambda s: mp.power(5, s - mp.mpf(1) / 2) + mp.sqrt(5) + mp.power(5, mp.mpf(1) / 2 - s)
d = mp.log(phi) / mp.log(5)
print("  golden zeros at Re = 1/2 +- log(phi)/log5 = %s, %s ; |XiA| there: %s, %s" %
      (mp.nstr(0.5 + d, 12), mp.nstr(0.5 - d, 12),
       mp.nstr(abs(XiA(mp.mpc(0.5 + d, mp.pi / mp.log(5)))), 3), mp.nstr(abs(XiA(mp.mpc(0.5 - d, mp.pi / mp.log(5)))), 3)))

# ---------------- E. shift control ----------------
section("E. E_theta (Lean: LambdaTheta_*, Etheta_logDeriv_hasSum, Etheta_offline_zeros, RH_iff_XiTheta_two_lines)")
th = mp.mpf('0.2')
N = 2000
aE = [mp.mpf(0)] * (N + 1)
for dd in range(1, N + 1):
    for m in range(dd, N + 1, dd):
        aE[m] += mp.power(dd, -th) * mp.power(m // dd, th)
LE = log_deriv_coeffs(aE, N)
mx = max(abs(LE[n] - vonmangoldt(n) * (mp.power(n, th) + mp.power(n, -th))) for n in range(2, N + 1))
print("  theta=0.2: max_n<=2000 |Lambda_E(n) - Lambda(n)(n^th+n^-th)| = %s ; min Lambda_E = %s" %
      (mp.nstr(mx, 3), mp.nstr(min(LE[2:]), 3)))
s = mp.mpc(3, '0.5')
E = lambda z: mp.zeta(z + th) * mp.zeta(z - th)
lhs = -mp.diff(E, s) / E(s)
rhs = sum(vonmangoldt(n) * (mp.power(n, th) + mp.power(n, -th)) * mp.power(n, -s) for n in range(2, 20001))
print("  -E'/E(3+0.5i) = %s ; truncated sum_{n<=20000} Lambda_theta(n) n^{-s} = %s" % (mp.nstr(lhs, 12), mp.nstr(rhs, 12)))
print("  decay: max Lambda_theta(n)/sqrt(n) on [1000,2000] = %s, on [100,200] = %s" %
      (mp.nstr(max(vonmangoldt(n) * (mp.power(n, th) + mp.power(n, -th)) / mp.sqrt(n) for n in range(1000, 2001)), 6),
       mp.nstr(max(vonmangoldt(n) * (mp.power(n, th) + mp.power(n, -th)) / mp.sqrt(n) for n in range(100, 201)), 6)))
rho = mp.zetazero(1)
print("  first zeta zero %s -> E_theta zeros at Re %s and %s (both off 1/2); |E| there: %s, %s" %
      (mp.nstr(rho, 10), mp.nstr((rho + th).real, 6), mp.nstr((rho - th).real, 6),
       mp.nstr(abs(E(rho + th)), 3), mp.nstr(abs(E(rho - th)), 3)))
print("  residue at 1+theta: (s-1-theta)E(s) at s = 1+theta+1e-12 -> %s ; zeta(1+2theta) = %s" %
      (mp.nstr((mp.mpf('1e-12')) * E(1 + th + mp.mpf('1e-12')), 10), mp.nstr(mp.zeta(1 + 2 * th), 10)))

# ---------------- F. finite-rank temperedness ----------------
section("F. finite-rank temperedness (Lean: dualSum_polyBounded_iff_real)")
gam = [mp.mpc(14.134725, 0), mp.mpc(21.022040, 0), mp.mpc(25.0, -0.3)]
m = [1, 1, 1]
for X in [0, 10, 20, 40, 80]:
    v = sum(mm * mp.exp(1j * g * X) for mm, g in zip(m, gam))
    print("  one off-line point at Im = -0.3: |dual(X=%d)| = %s (grows like e^{0.3 X})" % (X, mp.nstr(abs(v), 6)))

# ---------------- degree-2 segment (claim 5, paper + COMPUTED) ----------------
section("Claim 5: F_t = zeta_K + (2t-1) L(chi_-4) L(chi_5), K = Q(sqrt-5) (COMPUTED; not in Lean)")


def chi_m4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)


def chi_5(n):
    r = n % 5
    return 0 if r == 0 else (1 if r in (1, 4) else -1)


NN = 10000
aK = [0] * (NN + 1)
bb = [0] * (NN + 1)
for dd in range(1, NN + 1):
    for mm in range(dd, NN + 1, dd):
        aK[mm] += chi_m4(dd) * chi_5(dd)
        bb[mm] += chi_m4(dd) * chi_5(mm // dd)
print("  min over n<=10^4 of a_K(n) - |b(n)| =", min(aK[n] - abs(bb[n]) for n in range(1, NN + 1)),
      " (>= 0: every F_t, t in [0,1], has nonnegative coefficients)")
print("  a_K(1),a_K(2),a_K(3),a_K(6) =", aK[1], aK[2], aK[3], aK[6], "; b(1),b(2),b(3),b(6) =", bb[1], bb[2], bb[3], bb[6])
# c_t = a_K + (2t-1) b has c_t(1) = 2t; multiplicativity of c_t / c_t(1) at (2,3) is c(1)c(6) = c(2)c(3)
rows = []
for tt in [0, 0.25, 0.5, 0.75, 1]:
    c = lambda n: aK[n] + (2 * tt - 1) * bb[n]
    rows.append((tt, c(1) * c(6) - c(2) * c(3)))
print("  multiplicativity defect c_t(1)c_t(6) - c_t(2)c_t(3) = 8(2t-1), zero on [0,1] only at t = 1/2:", rows)
print("  t = 1 is the lattice sum of x^2+5y^2 (r(2), r(3), r(6) =",
      aK[2] + bb[2], aK[3] + bb[3], aK[6] + bb[6], "), t = 0 is 2x^2+2xy+3y^2, t = 1/2 is zeta_K")

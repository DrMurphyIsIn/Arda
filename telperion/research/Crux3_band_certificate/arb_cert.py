"""crux3: Arb (python-flint) certification of both sides of the band separation.

Band V = span{cos(k1 u), cos(k2 u)} 1_[-A,A], A = 9 pi/14, k1 = 763/9, k2 = 259/3 (Dirichlet: k A = pi(m+1/2),
m = 54, 55).  Tests v_c = c1 cos(k1 u) + c2 cos(k2 u) on [-A, A]; ||v_c||^2 = A (c1^2 + c2^2).

ZETA side (the certificate that the Lean file reproduces): the closed-form LOWER bound
    Q_zeta(v_c) >= c^T Mcert c,  Mcert = (C_N - log pi) A I - sum_{j=0}^N J(j + 1/4) - P,
    C_N = -gamma + H_N (psiR >= C_N - sum_j Lz(j+1/4, r), tail of the digamma series dropped, pole >= 0 dropped),
    J_ii(b) = 2A 2b/(4b^2+k^2) + 2k^2 (1+E)/(4b^2+k^2)^2,  J_12(b) = 2 s k1 k2 (1+E)/((4b^2+k1^2)(4b^2+k2^2)),
    E = e^{-4bA}, s = (-1)^{m1+m2} = -1,
    P_ii = sum_n Lam(n)/sqrt n [(2A - y) cos(k_i y) + sin(k_i y)/k_i],
    P_12 = sum_n Lam(n)/sqrt n 2 s [k1 sin(k2 y) - k2 sin(k1 y)]/(k1^2 - k2^2),  y = log n, n < e^{2A}.
  Certified: Mcert - lam A I is positive definite (lam = 1/2), in ball arithmetic.

D side (the counterexample): the EXACT band matrix of D's explicit-formula functional (no pole,
Gamma_R(s+1), conductor 5, c_D = coefficients of -D'/D), in the closed forms of weilfreq.py (digamma /
trigamma at 3/4 +- i k/2 and geometric tails), in Arb; certified Rayleigh quotient at an explicit
RATIONAL vector c* is negative.
"""
import flint
from flint import arb, acb
import sys

flint.ctx.prec = 256
PI = arb.pi()
q = arb(9) / 14
A = q * PI
ms = (54, 55)
ks = [arb(2 * m + 1) / (2 * q) for m in ms]     # 763/9, 259/3 exactly
s12 = -1  # (-1)^(54+55)


def vonmangoldt(nmax):
    lam = [arb(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        m, p = n, None
        for d in range(2, n + 1):
            if m % d == 0:
                p = d
                break
        while m % p == 0:
            m //= p
        if m == 1:
            lam[n] = arb(p).log()
    return lam


def dh_lambda(nmax):
    s5 = arb(5).sqrt()
    kap = ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)
    cv = {1: arb(1), 2: kap, 3: -kap, 4: arb(-1), 0: arb(0)}
    a = [arb(0)] + [cv[n % 5] for n in range(1, nmax + 1)]
    lam = [arb(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = a[n] * arb(n).log()
        for d in range(2, n):
            if n % d == 0:
                acc -= lam[d] * a[n // d]
        lam[n] = acc
    return lam


X = (2 * A).exp()
NMAX = int(float(X.mid()))   # 56
assert X > NMAX and X < NMAX + 1


def gij(ki, kj, y, diag):
    if diag:
        return (2 * A - y) * (ki * y).cos() / 2 + (ki * y).sin() / (2 * ki)
    return s12 * (ki * (kj * y).sin() - kj * (ki * y).sin()) / (ki * ki - kj * kj)


def prime_matrix(w):
    P = [[arb(0)] * 2 for _ in range(2)]
    for n in range(2, NMAX + 1):
        if w[n] == 0:
            continue
        y = arb(n).log()
        c = w[n] / arb(n).sqrt()
        for i in range(2):
            for j in range(2):
                P[i][j] += c * 2 * gij(ks[i], ks[j], y, i == j)
    return P


def zeta_cert(N=100, lam=arb(1) / 2):
    w = vonmangoldt(NMAX)
    P = prime_matrix(w)
    J = [[arb(0)] * 2 for _ in range(2)]
    for jj in range(N + 1):
        b = arb(jj) + arb(1) / 4
        E = (-4 * b * A).exp()
        for i in range(2):
            J[i][i] += 2 * A * 2 * b / (4 * b * b + ks[i] ** 2) + 2 * ks[i] ** 2 * (1 + E) / (4 * b * b + ks[i] ** 2) ** 2
        J[0][1] += 2 * s12 * ks[0] * ks[1] * (1 + E) / ((4 * b * b + ks[0] ** 2) * (4 * b * b + ks[1] ** 2))
    J[1][0] = J[0][1]
    HN = sum((arb(1) / (k + 1) for k in range(N)), arb(0))
    CN = -arb.const_euler() + HN - PI.log()
    M = [[CN * A * (1 if i == j else 0) - J[i][j] - P[i][j] for j in range(2)] for i in range(2)]
    a = M[0][0] - lam * A
    d = M[1][1] - lam * A
    b = M[0][1]
    det = a * d - b * b
    print('ZETA  N=%d lam=%s' % (N, lam))
    print('  Mcert/A =', [[(M[i][j] / A).str(8) for j in range(2)] for i in range(2)])
    print('  prime P/A =', [[(P[i][j] / A).str(8) for j in range(2)] for i in range(2)])
    print('  a = M11 - lam A =', a.str(10), ' d =', d.str(10), ' det =', det.str(10))
    ok = (a > 0) and (d > 0) and (det > 0)
    print('  CERTIFIED Mcert - lam A I > 0:', ok)
    return M, P, J


def dh_band_matrix():
    """exact D band matrix (even sector) via the general-frequency closed forms (weilfreq.py), in Arb."""
    beta0 = arb(3) / 2
    c0 = (arb(5) / PI).log()
    a = 2 * A
    Jn = 60
    betas = [beta0 + 2 * j for j in range(Jn)]
    psi_half = acb(beta0 / 2).digamma().real
    CL = c0 + psi_half + sum((2 * (-b * a).exp() / b for b in betas), arb(0))
    tail_bound = 2 * (-(beta0 + 2 * Jn) * a).exp() / (beta0 * (1 - (-2 * a).exp()))

    def I(lam):
        v = acb(beta0 / 2, -lam / 2).digamma() - psi_half
        for b in betas:
            z = acb(b, -lam)
            v -= 2 * ((-b * a).exp() / b - (-z * a).exp() / z)
        return v + acb(arb(0, tail_bound.mid() * 4), arb(0, tail_bound.mid() * 4))

    def Cu(k):
        v = acb(beta0 / 2, k / 2).polygamma(1).real / 2
        for b in betas:
            z = acb(b, -k)
            v -= 2 * ((-z * a).exp() * (a / z + 1 / (z * z))).real
        return v + arb(0, (tail_bound * (a + 1)).mid() * 4)

    def gram(km, kn):
        d_ = km - kn
        if d_ == 0:
            return 2 * A
        return 2 * (d_ * A).sin() / d_

    def arch(km, kn, same):
        if same:
            return acb(2 * A * CL + 2 * A * I(km).real + Cu(km))
        d_ = km - kn
        e1 = acb(0, d_ * A).exp() / acb(0, 2 * d_)
        e2 = -acb(0, -d_ * A).exp() / acb(0, 2 * d_)
        return gram(km, kn) * CL + e1 * (I(kn) + I(-km)) + e2 * (I(km) + I(-kn))

    w = dh_lambda(NMAX)
    primes = [(n, w[n] / arb(n).sqrt(), arb(n).log()) for n in range(2, NMAX + 1) if not (w[n] == 0)]

    def gpair(km, kn, y, same):
        d_ = km - kn
        if same:
            return acb(2 * (2 * A - y) * (km * y).cos())
        e1 = acb(0, d_ * A).exp()
        e2 = acb(0, -d_ * A).exp()
        return (e1 * (acb(0, kn * y).exp() + acb(0, -km * y).exp()) - e2 * (acb(0, km * y).exp() + acb(0, -kn * y).exp())) / acb(0, d_)

    def prime(km, kn, same):
        return sum((c * gpair(km, kn, y, same) for (n, c, y) in primes), acb(0))

    allk = [ks[0], ks[1], -ks[0], -ks[1]]
    Mc = [[arch(allk[i], allk[j], i == j) - prime(allk[i], allk[j], i == j) for j in range(4)] for i in range(4)]
    Me = [[((Mc[i][j] + Mc[i][j + 2] + Mc[i + 2][j] + Mc[i + 2][j + 2]) / 4) for j in range(2)] for i in range(2)]
    return Me


if __name__ == '__main__':
    for N in (50, 100, 200):
        zeta_cert(N)
    Me = dh_band_matrix()
    print('D band matrix (even, unnormalised):', [[Me[i][j].real.str(10) for j in range(2)] for i in range(2)])
    print('   imaginary parts:', [[Me[i][j].imag.str(3) for j in range(2)] for i in range(2)])
    # explicit rational counterexample vector c* = (-3, 2)
    for cs in [(-3, 2), (-586, 389), (-1, 1)]:
        c = [arb(cs[0]), arb(cs[1])]
        Qv = sum((c[i] * c[j] * Me[i][j].real for i in range(2) for j in range(2)), arb(0))
        nrm = A * (c[0] ** 2 + c[1] ** 2)
        print('  c* = %s : Q_D(v)/||v||^2 = %s   (negative certified: %s)' % (cs, (Qv / nrm).str(10), bool(Qv < 0)))

"""Exact-rational mirror of the Lean prime-side checker (Crux3).  Fractions only.

For each prime power n = p^e <= 56:
  log n in [lo_n, hi_n]   verified by  (S_K(lo/8) + R_K(lo/8))^8 <= n <= (S_K(hi/8) - R_K(hi/8))^8
  1/sqrt n in [q0, q1]     verified by  q0^2 n <= 1 <= q1^2 n, q0 >= 0
  pi in [PLO, PHI] (Mathlib pi_gt_d20 / pi_lt_d20)
Ball arithmetic (centre c, radius r, |x - c| <= r):
  y = log n, Lam = y/e, w = 2 Lam (1/sqrt n), A = 9 pi/14,
  theta_i = k_i y, phi_i = theta_i - 2 m_i pi (m_i chosen), recentred at a 10^-RD rational,
  cos theta_i in (tayl0(phi0), 2|phi0|^(2M)/(2M)! + r), sin theta_i in (tayl1(phi0), 2|phi0|^(2M+1)/(2M+1)! + r),
  gD_i = (2A - y) cos_i/2 + sin_i/(2 k_i),  gX = s1 s2 (k1 sin_2 - k2 sin_1)/(k1^2 - k2^2),
  terms  w gD_1, w gD_2, w gX  -> summed.
"""
from fractions import Fraction as Fr
import math

PLO = Fr(314159265358979323846, 10 ** 20)
PHI = Fr(314159265358979323847, 10 ** 20)
K1 = Fr(763, 9)
K2 = Fr(259, 3)
S1S2 = -1
Q = Fr(9, 14)          # A = Q pi
KEXP = 22              # exp Taylor terms
MT = 15                # cos/sin Taylor order: tayl 0 MT (deg < 2 MT), tayl 1 MT
RD = 18                # recentring digits
RT = 24                # term rounding digits


def fact(n):
    return math.factorial(n)


def expS(x, K):
    return sum(x ** m / fact(m) for m in range(K))


def expR(x, K):
    return abs(x) ** K * Fr(K + 1, fact(K) * K)


def exp_up(q):          # upper bound of exp(q), q >= 0, q/8 <= 1
    x = q / 8
    return (expS(x, KEXP) + expR(x, KEXP)) ** 8


def exp_lo(q):
    x = q / 8
    v = expS(x, KEXP) - expR(x, KEXP)
    assert v >= 0
    return v ** 8


def floorR(q, R):
    return Fr(math.floor(q * 10 ** R), 10 ** R)


def ball_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def ball_sub(a, b):
    return (a[0] - b[0], a[1] + b[1])


def ball_mul(a, b):
    return (a[0] * b[0], abs(a[0]) * b[1] + abs(b[0]) * a[1] + a[1] * b[1])


def ball_cmul(q, a):
    return (q * a[0], abs(q) * a[1])


def ball_round(a, R):
    c = floorR(a[0], R)
    return (c, a[1] + (a[0] - c))


def tayl(par, M, y):
    return sum((-1) ** m * y ** (2 * m + par) / fact(2 * m + par) for m in range(M))


def trig_balls(theta, pib, m):
    """cos/sin balls of theta via phi = theta - 2 m pi."""
    phi = ball_sub(theta, ball_cmul(2 * m, pib))
    phi = ball_round(phi, RD)
    c, r = phi
    assert abs(c) <= Fr(2 * MT + 1, 2), (c, MT)
    cosb = (tayl(0, MT, c), 2 * abs(c) ** (2 * MT) / fact(2 * MT) + r)
    sinb = (tayl(1, MT, c), 2 * abs(c) ** (2 * MT + 1) / fact(2 * MT + 1) + r)
    return cosb, sinb


def prime_powers(N):
    out = []
    for n in range(2, N + 1):
        m, p = n, None
        for d in range(2, n + 1):
            if m % d == 0:
                p = d
                break
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        if m == 1:
            out.append((n, p, e))
    return out


import mpmath
mpmath.mp.dps = 50


def log_encl(n, digits=15):
    L = Fr(mpmath.nstr(mpmath.log(n), 40))
    lo = floorR(L, digits) - Fr(1, 10 ** digits)
    hi = floorR(L, digits) + Fr(2, 10 ** digits)
    assert exp_up(lo) <= n, n
    assert n <= exp_lo(hi), n
    return lo, hi


def sqrt_encl(n, digits=18):
    s = Fr(mpmath.nstr(1 / mpmath.sqrt(n), 40))
    q0 = floorR(s, digits) - Fr(1, 10 ** digits)
    q1 = floorR(s, digits) + Fr(2, 10 ** digits)
    assert q0 >= 0 and q0 * q0 * n <= 1 <= q1 * q1 * n
    return q0, q1


def run():
    pib = ((PLO + PHI) / 2, (PHI - PLO) / 2)
    Ab = ball_cmul(Q, pib)
    table = []
    tot = [(Fr(0), Fr(0))] * 3
    for (n, p, e) in prime_powers(56):
        lo, hi = log_encl(n)
        q0, q1 = sqrt_encl(n)
        yb = ((lo + hi) / 2, (hi - lo) / 2)
        lamb = ball_cmul(Fr(1, e), yb)
        qb = ((q0 + q1) / 2, (q1 - q0) / 2)
        wb = ball_mul(ball_cmul(2, lamb), qb)
        th1 = ball_cmul(K1, yb)
        th2 = ball_cmul(K2, yb)
        m1 = round(float(th1[0]) / (2 * math.pi))
        m2 = round(float(th2[0]) / (2 * math.pi))
        c1b, s1b = trig_balls(th1, pib, m1)
        c2b, s2b = trig_balls(th2, pib, m2)
        twoAmy = ball_sub(ball_cmul(2, Ab), yb)
        gD1 = ball_add(ball_cmul(Fr(1, 2), ball_mul(twoAmy, c1b)), ball_cmul(1 / (2 * K1), s1b))
        gD2 = ball_add(ball_cmul(Fr(1, 2), ball_mul(twoAmy, c2b)), ball_cmul(1 / (2 * K2), s2b))
        gX = ball_cmul(Fr(S1S2) / (K1 ** 2 - K2 ** 2), ball_sub(ball_cmul(K1, s2b), ball_cmul(K2, s1b)))
        t = [ball_round(ball_mul(wb, g), RT) for g in (gD1, gD2, gX)]
        for i in range(3):
            tot[i] = ball_add(tot[i], t[i])
        table.append((n, p, e, lo, hi, q0, q1, m1, m2))
    return tot, table


if __name__ == '__main__':
    tot, table = run()
    for name, b in zip(('P11', 'P22', 'P12'), tot):
        print('%s = %.12f +- %.3e' % (name, float(b[0]), float(b[1])))
    print('entries', len(table))
    print('max |m|', max(max(abs(t[7]), abs(t[8])) for t in table))
    # check the separation facts log 56 < 2A < log 57
    lo57, hi57 = log_encl(57)
    lo56, hi56 = log_encl(56)
    print('hi56 < 9 PLO/7:', hi56 < 9 * PLO / 7, ' lo57 > 9 PHI/7:', lo57 > 9 * PHI / 7)

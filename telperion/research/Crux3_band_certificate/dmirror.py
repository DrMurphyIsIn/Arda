"""Exact-rational mirror of the D prime-side checker (Crux3 D side) and the final D bound."""
from fractions import Fraction as Fr
import math, json
import mpmath
mpmath.mp.dps = 50
from mirror import (PLO, PHI, K1, K2, Q, KEXP, MT, RD, RT, fact, expS, expR, exp_up, exp_lo, floorR,
                    ball_add, ball_sub, ball_mul, ball_cmul, ball_round, tayl, trig_balls, log_encl, sqrt_encl)
d = json.load(open('dh_coeffs.json'))
# kappa ball
def kap_ball():
    s5 = Fr(mpmath.nstr(mpmath.sqrt(5), 40))
    a5 = floorR(s5, 30) - Fr(1, 10**30); b5 = floorR(s5, 30) + Fr(2, 10**30)
    assert a5 * a5 <= 5 <= b5 * b5 and a5 > 0
    lo_in, hi_in = 10 - 2 * b5, 10 - 2 * a5
    s = Fr(mpmath.nstr(mpmath.sqrt(10 - 2 * mpmath.sqrt(5)), 40))
    c = floorR(s, 30) - Fr(1, 10**30); dd = floorR(s, 30) + Fr(2, 10**30)
    assert c * c <= lo_in and hi_in <= dd * dd and c > 2
    klo = (c - 2) / (b5 - 1); khi = (dd - 2) / (a5 - 1)
    return (a5, b5, c, dd), ((klo + khi) / 2, (khi - klo) / 2)
sq, KB = kap_ball()
primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53]
LP = {p: log_encl(p) for p in primes}
def lp_ball(p):
    lo, hi = LP[p]; return ((lo + hi) / 2, (hi - lo) / 2)
def poly_ball(coeffs, xb):
    # Horner: q0 + x (q1 + x (...))
    acc = (Fr(0), Fr(0))
    for q in reversed(coeffs):
        acc = ball_add((Fr(q), Fr(0)), ball_mul(xb, acc))
    return acc
def cd_ball(n):
    acc = (Fr(0), Fr(0))
    for p, poly in d.get(str(n), {}).items():
        degs = {int(k): Fr(v) for k, v in poly.items()}
        coeffs = [degs.get(i, Fr(0)) for i in range(max(degs) + 1)]
        acc = ball_add(ball_mul(poly_ball(coeffs, KB), lp_ball(int(p))), acc)
    return acc
def run(c1=Fr(-3), c2=Fr(2)):
    pib = ((PLO + PHI) / 2, (PHI - PLO) / 2)
    Ab = ball_cmul(Q, pib)
    tot = [(Fr(0), Fr(0))] * 3
    rows = []
    for n in range(2, 57):
        if not d.get(str(n)):
            continue
        lo, hi = log_encl(n); q0, q1 = sqrt_encl(n)
        yb = ((lo + hi) / 2, (hi - lo) / 2)
        qb = ((q0 + q1) / 2, (q1 - q0) / 2)
        wb = ball_mul(ball_cmul(2, cd_ball(n)), qb)
        th1 = ball_cmul(K1, yb); th2 = ball_cmul(K2, yb)
        m1 = round(float(th1[0]) / (2 * math.pi)); m2 = round(float(th2[0]) / (2 * math.pi))
        c1b, s1b = trig_balls(th1, pib, m1); c2b, s2b = trig_balls(th2, pib, m2)
        twoAmy = ball_sub(ball_cmul(2, Ab), yb)
        gD1 = ball_add(ball_cmul(Fr(1, 2), ball_mul(twoAmy, c1b)), ball_cmul(1 / (2 * K1), s1b))
        gD2 = ball_add(ball_cmul(Fr(1, 2), ball_mul(twoAmy, c2b)), ball_cmul(1 / (2 * K2), s2b))
        gX = ball_cmul(Fr(-1) / (K1 ** 2 - K2 ** 2), ball_sub(ball_cmul(K1, s2b), ball_cmul(K2, s1b)))
        t = [ball_round(ball_mul(wb, g), RT) for g in (gD1, gD2, gX)]
        for i in range(3):
            tot[i] = ball_add(tot[i], t[i])
        rows.append((n, lo, hi, q0, q1, m1, m2))
    return tot, rows
if __name__ == '__main__':
    tot, rows = run()
    for name, b in zip(('PD11', 'PD22', 'PD12'), tot):
        print('%s = %.12f +- %.3e' % (name, float(b[0]), float(b[1])))
    print('kappa ball', float(KB[0]), float(KB[1]))
    P11, P22, P12 = tot
    Pform_lo = 9 * (P11[0] - P11[1]) + 4 * (P22[0] - P22[1]) - 12 * (P12[0] + P12[1])
    print('prime form at c*=(-3,2) >= %.6f' % float(Pform_lo))
    # arch upper bound at c*, N = 300, R = 175
    N = 300; R = Fr(175)
    H = sum(Fr(1, m + 1) for m in range(N))
    Ahi = Q * PHI; Alo = Q * PLO
    A0hi = 13 * Ahi; A0lo = 13 * Alo
    b = [j + Fr(3, 4) for j in range(N + 1)]
    S1 = [sum(4 * x / (4 * x * x + k * k) for x in b) for k in (K1, K2)]
    S2 = [sum(2 * k * k / (4 * x * x + k * k) ** 2 for x in b) for k in (K1, K2)]
    Sx = sum(2 * K1 * K2 / ((4 * x * x + K1 * K1) * (4 * x * x + K2 * K2)) for x in b)
    lorLo = 9 * (Alo * S1[0] + S2[0]) + 4 * (Alo * S1[1] + S2[1]) + 12 * Sx
    log5hi = LP[5][1]
    logpilo = Fr(11447, 10000)
    Kp = Fr(8, 3) * (3 * K1 + 2 * K2)
    const = (log5hi - logpilo) + (Fr(-1, 2) + H + Fr(3, 4) / N)
    arch_ub = const * A0hi - lorLo + (R * R * A0hi + Kp * Kp / R) / (8 * N * N)
    Q_ub = arch_ub - Pform_lo
    print('const=%.6f arch_ub=%.6f  Q_D <= %.6f ; ||v||^2 in [%.4f, %.4f] ; Q_D/||v||^2 <= %.4f' % (float(const), float(arch_ub), float(Q_ub), float(A0lo), float(A0hi), float(Q_ub / A0lo)))
    json.dump([[str(x) for x in r] for r in rows], open('drows.json', 'w'))

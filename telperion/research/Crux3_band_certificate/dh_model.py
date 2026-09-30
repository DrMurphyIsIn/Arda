"""Upper-bound model for D's band form at c* = (-3, 2), mirroring the planned Lean proof."""
import mpmath as mp
from weilmodes import lambda_dh
mp.mp.dps = 30
q = mp.mpf(9) / 14
A = q * mp.pi
k1, k2 = mp.mpf(763) / 9, mp.mpf(259) / 3
c1, c2 = mp.mpf(-3), mp.mpf(2)
s12 = -1
A0 = A * (c1 ** 2 + c2 ** 2)
def gD(k, y): return (2 * A - y) * mp.cos(k * y) / 2 + mp.sin(k * y) / (2 * k)
def gX(y): return s12 * (k1 * mp.sin(k2 * y) - k2 * mp.sin(k1 * y)) / (k1 ** 2 - k2 ** 2)
def Jd(k, b, E): return 2 * A * 2 * b / (4 * b * b + k * k) + 2 * k * k * (1 + E) / (4 * b * b + k * k) ** 2
def Jx(b, E): return 2 * s12 * k1 * k2 * (1 + E) / ((4 * b * b + k1 * k1) * (4 * b * b + k2 * k2))
w = lambda_dh(56)
P = sum(2 * w[n] / mp.sqrt(n) * (c1 ** 2 * gD(k1, mp.log(n)) + 2 * c1 * c2 * gX(mp.log(n)) + c2 ** 2 * gD(k2, mp.log(n))) for n in range(2, 57))
for N in (100, 300, 1000):
    for R in (175, 200):
        gam_lo = mp.mpf(1) / 2
        H = mp.harmonic(N)
        # arch upper: log(5/pi) A0 + [(-gam_lo + H_N + (3/4)/N) A0 - sum_j J(b_j)] + (1/(2pi)) (1/(8N^2)) (R^2 2 pi A0 + 2 pi K'^2 / R)
        J = 0
        for j in range(N + 1):
            b = j + mp.mpf(3) / 4
            E = mp.exp(-4 * b * A)
            J += c1 ** 2 * Jd(k1, b, 0) + 2 * c1 * c2 * Jx(b, 1 if (c1 * c2 * s12) < 0 else 0) + c2 ** 2 * Jd(k2, b, 0)
        Kp = mp.mpf(8) / 3 * (abs(c1) * k1 + abs(c2) * k2)
        r2term = (R ** 2 * A0 + Kp ** 2 / R) / (8 * N * N)
        arch_ub = mp.log(5 / mp.pi) * A0 + (-gam_lo + H + mp.mpf(3) / (4 * N)) * A0 - J + r2term
        Q_ub = arch_ub - P
        print('N=%4d R=%d: arch_ub=%.4f  prime P=%.4f  Q_D upper bound=%.4f  (true -17.18; per ||v||^2: %.4f); r2term=%.4f' % (N, R, float(arch_ub), float(P), float(Q_ub), float(Q_ub / A0), float(r2term)))

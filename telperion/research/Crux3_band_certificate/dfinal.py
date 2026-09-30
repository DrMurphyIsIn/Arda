"""Exact-rational thresholds for the Crux3 D-side kernel certificate (Lean Crux3_BandDH)."""
from fractions import Fraction as Fr
import math
from mirror import PLO, PHI, K1, K2, Q
from dmirror import run, LP

def floor9(x):
    return Fr(math.floor(x * 10**9) - 1, 10**9)
def ceil9(x):
    return Fr(math.ceil(x * 10**9) + 1, 10**9)

tot, rows = run()
(P11, P22, P12) = tot
PD11lo = floor9(P11[0] - P11[1]); PD22lo = floor9(P22[0] - P22[1]); PD12hi = ceil9(P12[0] + P12[1])
PD11hi = ceil9(P11[0] + P11[1]); PD22hi = ceil9(P22[0] + P22[1]); PD12lo = floor9(P12[0] - P12[1])
print('PD11 in [%s, %s]' % (PD11lo, PD11hi)); print('PD22 in [%s, %s]' % (PD22lo, PD22hi)); print('PD12 in [%s, %s]' % (PD12lo, PD12hi))
N = 300; R = Fr(175)
H = sum(Fr(1, m + 1) for m in range(N)); Hhi = ceil9(H)
bs = [j + Fr(3, 4) for j in range(N + 1)]
S1a = sum(4 * x / (4 * x * x + K1 * K1) for x in bs); S1b = sum(4 * x / (4 * x * x + K2 * K2) for x in bs)
S2a = sum(2 * K1 * K1 / (4 * x * x + K1 * K1) ** 2 for x in bs); S2b = sum(2 * K2 * K2 / (4 * x * x + K2 * K2) ** 2 for x in bs)
Sx = sum(2 * K1 * K2 / ((4 * x * x + K1 * K1) * (4 * x * x + K2 * K2)) for x in bs)
S1alo, S1blo, S2alo, S2blo, Sxlo = map(floor9, (S1a, S1b, S2a, S2b, Sx))
print('Hhi', Hhi, float(Hhi)); print('S1alo', S1alo, 'S1blo', S1blo, 'S2alo', S2alo, 'S2blo', S2blo, 'Sxlo', Sxlo)
log5hi = LP[5][1]; print('log5hi', log5hi, float(log5hi))
logpilo = Fr(11447, 10000)
Kp = Fr(8, 3) * (3 * K1 + 2 * K2); print('Kp', Kp)
Chi = log5hi - logpilo - Fr(1, 2) + Hhi + Fr(3, 4) / N
print('Chi', float(Chi))
Alo = Q * PLO; Ahi = Q * PHI
def arch_ub(A):
    return Chi * 13 * A - (9 * (A * S1alo + S2alo) + 4 * (A * S1blo + S2blo) + 12 * Sxlo) + (R * R * 13 * A + Kp * Kp / R) / (8 * N * N)
prime_lo = 9 * PD11lo - 12 * PD12hi + 4 * PD22lo
for A in (Alo, Ahi):
    a = arch_ub(A); nv = 13 * A
    print('A=%.6f arch_ub=%.6f (%.5f |v|^2)  prime_lo=%.6f (%.5f |v|^2)  Q<= %.6f (%.5f |v|^2)' % (float(A), float(a), float(a / nv), float(prime_lo), float(prime_lo / nv), float(a - prime_lo), float((a - prime_lo) / nv)))
    assert a <= Fr(433, 100) * nv, 'arch'
    assert prime_lo >= Fr(486, 100) * nv, 'prime'
    assert a - prime_lo <= -Fr(1, 2) * nv
print('ALL OK')

from fractions import Fraction as Fr
from mirror import run, PLO, PHI, K1, K2, Q
N = 100
tot, table = run()
P11, P22, P12 = tot
GUP = Fr(58112, 100000)
LPUP = Fr(11448, 10000)
H = sum(Fr(1, n + 1) for n in range(N))
Clo = -GUP + H
Alo, Ahi = Q * PLO, Q * PHI
S1 = [sum(4 * (j + Fr(1, 4)) / (4 * (j + Fr(1, 4)) ** 2 + k ** 2) for j in range(N + 1)) for k in (K1, K2)]
S2 = [sum(2 * k ** 2 / (4 * (j + Fr(1, 4)) ** 2 + k ** 2) ** 2 for j in range(N + 1)) for k in (K1, K2)]
Sx = sum(2 * K1 * K2 / ((4 * (j + Fr(1, 4)) ** 2 + K1 ** 2) * (4 * (j + Fr(1, 4)) ** 2 + K2 ** 2)) for j in range(N + 1))
lam = Fr(1, 2)
alpha = (Clo - LPUP) * Alo - Ahi * S1[0] - 2 * S2[0] - (P11[0] + P11[1]) - lam * Ahi
delta = (Clo - LPUP) * Alo - Ahi * S1[1] - 2 * S2[1] - (P22[0] + P22[1]) - lam * Ahi
m12lo = Sx - (P12[0] + P12[1]); m12hi = 2 * Sx - (P12[0] - P12[1])
beta = max(abs(m12lo), abs(m12hi))
print('Clo - LPUP =', float(Clo - LPUP))
print('alpha = %.6f delta = %.6f beta = %.6f  alpha*delta - beta^2 = %.6f' % (float(alpha), float(delta), float(beta), float(alpha * delta - beta ** 2)))
print('sizes: S1 denom digits', len(str(S1[0].denominator)), 'H digits', len(str(H.denominator)))

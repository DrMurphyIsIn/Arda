"""BUILDER check of the explicit-formula normalisation (P1), independent of the idea's check_ef.py:
arithmetic side in the u-DOMAIN (Weil's form, no digamma) versus the zero side 2 sum_k |F(gamma_k)|^2 over the
first 2000 zeros (RH verified far beyond this height, so these are all the zeros up to 2515).
Test function: f(u) = (1 - (u/a)^2)^5 (1 + u/3) on [-a, a] (real, mixes both parity sectors; F = O(t^-6)).
conjecture1_proved = False."""
import json, sys
import mpmath as mp

mp.mp.dps = 40
a = mp.mpf(249) / 256
if len(sys.argv) > 1:
    p, q = sys.argv[1].split('/')
    a = mp.mpf(int(p)) / int(q)
# polynomial coefficients of f in u (ascending)
u = mp.mpf
P1 = [mp.mpf(1), mp.mpf(0), -1 / a ** 2]          # 1 - (u/a)^2
def pmul(A, B):
    C = [mp.mpf(0)] * (len(A) + len(B) - 1)
    for i, x in enumerate(A):
        for j, y in enumerate(B):
            C[i + j] += x * y
    return C
f = [mp.mpf(1)]
for _ in range(5):
    f = pmul(f, P1)
f = pmul(f, [mp.mpf(1), mp.mpf(1) / 3])
def peval(c, x):
    s = mp.mpf(0)
    for cc in reversed(c):
        s = s * x + cc
    return s
def pder(c):
    return [i * c[i] for i in range(1, len(c))]

def F(t):
    """int_{-a}^{a} f(u) e^{itu} du, exact: repeated integration by parts (f polynomial)."""
    t = mp.mpc(t)
    tot = mp.mpc(0)
    c = f
    j = 0
    while c and any(x != 0 for x in c):
        term = (peval(c, a) * mp.exp(1j * t * a) - peval(c, -a) * mp.exp(-1j * t * a)) / (1j * t) ** (j + 1)
        tot += (-1) ** j * term
        c = pder(c)
        j += 1
    return tot

def g(x):
    """autocorrelation g(x) = int f(v + x) f(v) dv (x >= 0), polynomial integrand: Gauss-Legendre exact."""
    lo, hi = -a, a - x
    if hi <= lo:
        return mp.mpf(0)
    return mp.quad(lambda v: peval(f, v + x) * peval(f, v), [lo, hi], method='gauss-legendre')

g0 = g(mp.mpf(0))
# F(+-i/2) directly
Fp = mp.quad(lambda v: peval(f, v) * mp.exp(-v / 2), [-a, a])      # F(i/2)
Fm = mp.quad(lambda v: peval(f, v) * mp.exp(v / 2), [-a, a])       # F(-i/2)
pole = 2 * Fp * Fm
const = (-mp.euler - mp.log(mp.pi) - mp.log(1 - mp.exp(-4 * a))) * g0
arch = mp.quad(lambda x: 2 * (mp.exp(-2 * x) * g0 - mp.exp(-x / 2) * g(x)) / (1 - mp.exp(-2 * x)), [0, a, 2 * a])
prime = mp.mpf(0)
n = 2
while mp.log(n) < 2 * a:
    m, pp = n, None
    for qq in range(2, n + 1):
        if m % qq == 0:
            pp = qq
            break
    while m % pp == 0:
        m //= pp
    if m == 1:
        prime += 2 * mp.log(pp) / mp.sqrt(n) * g(mp.log(n))
    n += 1
Q_arith = pole + const + arch - prime
zeros = json.load(open('/Users/peterwmurphy/arda-crux2/telperion/research/zeros2000.json'))
Q_zero = mp.mpf(0)
for zs in zeros:
    gam = mp.mpf(zs)
    Q_zero += 2 * abs(F(gam)) ** 2
last = mp.mpf(zeros[-1])
tail_est = 2 * abs(F(last)) ** 2 * (mp.log(last / (2 * mp.pi)) / (2 * mp.pi)) * last / 11   # int_T^inf t^-12 density
print("a =", a, " g(0) = ||f||^2 =", mp.nstr(g0, 20))
print("pole %s  const %s  arch %s  prime %s" % tuple(mp.nstr(x, 20) for x in (pole, const, arch, prime)))
print("Q arithmetic (u-domain) = %s" % mp.nstr(Q_arith, 25))
print("Q zero side (2000 zeros) = %s   tail estimate %s" % (mp.nstr(Q_zero, 25), mp.nstr(tail_est, 3)))
print("difference = %s" % mp.nstr(Q_arith - Q_zero, 5))

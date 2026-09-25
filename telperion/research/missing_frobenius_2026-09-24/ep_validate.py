"""Independent check of the degree-2 explicit formula (prime side + arch quadrature + pole) against zero sums,
for a smooth even test f(u) = (1-(u/A)^2)^4 on [-A,A]. Q_arith = pole + arch - prime;  Q_zero = sum_rho F(gamma_rho)^2."""
import mpmath as mp, sys
from ep_core import coeffs, logderiv_weights, chi_m20
from weilmodes import von_mangoldt
mp.mp.dps = 20
A = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.log(12) / 2
f = lambda u: (1 - (u / A) ** 2) ** 4 if abs(u) < A else mp.mpf(0)
def F(z): return 2 * mp.quad(lambda u: f(u) * mp.cos(z * u), [0, A])
def g(y):
    y = abs(y)
    if y >= 2 * A: return mp.mpf(0)
    return mp.quad(lambda v: f(v) * f(v - y), [y - A, A])
def arch_family(beta0, c0):
    g0 = g(0)
    W = lambda u: 2 * mp.exp(-beta0 * u) / (1 - mp.exp(-2 * u))
    I1 = mp.quad(lambda u: g0 * mp.exp(-2 * u) / u - W(u) * g(u), [0, A, 2 * A])
    I2 = mp.quad(lambda u: g0 * mp.exp(-2 * u) / u, [2 * A, mp.inf])
    return c0 * g0 + I1 + I2
x = mp.exp(2 * A); nmax = int(mp.floor(x))
lam = von_mangoldt(nmax)
wK = [0, 0] + [lam[n] * (1 + chi_m20(n)) for n in range(2, nmax + 1)]
aE, _, _ = coeffs(nmax); wE = logderiv_weights(aE, nmax)
arch = arch_family(mp.mpf(1) / 2, -mp.log(mp.pi)) + arch_family(mp.mpf(3) / 2, mp.log(20 / mp.pi))
h = mp.mpc(0, 0.5); pole = F(h) ** 2 + F(-h) ** 2
def prime(w): return sum(w[n] / mp.sqrt(n) * 2 * g(mp.log(n)) for n in range(2, nmax + 1) if w[n] != 0)
def zsum(fn):
    tot = mp.mpc(0)
    for line in open(fn):
        re_, im_ = map(mp.mpf, line.split())
        gm = (mp.mpc(re_, im_) - mp.mpf(1) / 2) / mp.j
        tot += F(gm) ** 2
    return 2 * mp.re(tot)
for name, w, fn in (('ZK', wK, 'zeros_ZK.txt'), ('E', wE, 'zeros_E.txt')):
    Qa = pole + arch - prime(w)
    print('%s: x=%.2f  Q_arith=%.10f  Q_zero(T<=100)=%.10f  (pole %.4f arch %.4f prime %.4f)' % (name, float(x), float(mp.re(Qa)), float(zsum(fn)), float(mp.re(pole)), float(arch), float(prime(w))), flush=True)

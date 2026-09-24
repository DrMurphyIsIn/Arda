"""Independent sanity check of the Weil-form normalization: arithmetic side vs zero side.
f(u) = (1-(u/a)^2)^3 on [-a,a];  F(t) = a sqrt(pi) 6 (2/(a t))^{7/2} J_{7/2}(a t)."""
import mpmath as mp
import json
mp.mp.dps = 30
a = mp.mpf(249)/256
def F(t):
    x = a*t
    if x == 0:
        return a*mp.mpf(32)/35   # int_{-1}^1 (1-s^2)^3 ds = 32/35
    return a*mp.sqrt(mp.pi)*6*(2/x)**mp.mpf(3.5)*mp.besselj(3.5, x)
Fi = a*mp.sqrt(mp.pi)*6*(2/(a/2))**mp.mpf(3.5)*mp.besseli(3.5, a/2)
primes = [(2, mp.log(2)), (3, mp.log(3)), (4, mp.log(2)), (5, mp.log(5))]
def Psi(t):
    v = mp.re(mp.digamma(mp.mpf(1)/4 + 1j*t/2)) - mp.log(mp.pi)
    for (n, lp) in primes:
        v -= 2*lp/mp.sqrt(n)*mp.cos(t*mp.log(n))
    return v
pole = 2*Fi**2
integral = mp.quad(lambda t: Psi(t)*F(t)**2, mp.linspace(0, 400, 81) + [mp.inf]) / mp.pi
Q_arith = pole + integral
# zero side
zs = json.load(open('/Users/peterwmurphy/arda-crux2/telperion/research/zeros2000.json')) if False else None
S = mp.mpf(0)
K = 2000
last = None
for k in range(1, K+1):
    g = mp.im(mp.zetazero(k))
    S += 2*F(g)**2
    last = g
tail = mp.quad(lambda t: 2*F(t)**2*mp.log(t/(2*mp.pi))/(2*mp.pi), [last, mp.inf])
print("pole =", mp.nstr(pole, 15), " integral =", mp.nstr(integral, 15))
print("Q arithmetic side      =", mp.nstr(Q_arith, 15))
print("zero side (2000 zeros) =", mp.nstr(S, 15), " + smooth tail est", mp.nstr(tail, 5), " =", mp.nstr(S+tail, 15))

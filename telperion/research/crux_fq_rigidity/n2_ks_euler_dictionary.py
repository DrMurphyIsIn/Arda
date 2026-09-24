# N2: Kurasov-Sarnak / Lee-Yang dictionary at the primes.
# (a) local roots of the Euler-product negative controls -> real parts of their local (lattice) zeros.
#     Local factor R(T) = prod (1 - a_j T), T = p^{-s}: zeros at Re s = log|a_j| / log p;
#     local Lee-Yang (roots of R(p^{-1/2} z) on |z| = 1)  <=>  |a_j| = sqrt(p)  <=>  Re s = 1/2.
# (b) a genuinely two-variable Lee-Yang polynomial on the prime logs (log 2, log 3):
#     p(z1,z2) = det(I + diag(z1,z2) U), U in SO(2): real zeros, but mixed log-coefficient c_11 != 0,
#     i.e. Fourier mass at the composite frequency log 6 (where Lambda(6) = 0 for zeta).
import numpy as np, mpmath as mp
mp.mp.dps = 30
def local_lines(coeffs_T, p, name):
    # coeffs_T: [1, c1, c2, ...] of R(T) = 1 + c1 T + c2 T^2 + ...
    # R(T) = prod(1 - a_j T)  => a_j are roots of T^d R(1/T) = T^d + c1 T^{d-1} + ... (reversed poly)
    a = np.roots(coeffs_T)  # np.roots takes highest degree first: for [1,c1,c2] -> x^2 + c1 x + c2
    res = []
    for aj in a:
        res.append((complex(aj), abs(aj), float(mp.log(abs(aj))/mp.log(p))))
    print(f"{name}: p={p}, sqrt(p)={np.sqrt(p):.6f}")
    for aj, m, re in res:
        print(f"    a={aj:.6f}  |a|={m:.6f}  local zero line Re s = {re:.6f}")
local_lines([1, 5, 5], 5, "golden-fake numerator 1+5T+5T^2 (H4 / Z_{5,-5})")
local_lines([1, 11, 29], 29, "W1(29,11) factor 1+11T+29T^2")
local_lines([1, 5, 20, 25, 25], 5, "formal curve F(5,5): 1+5T+(25-5)T^2+25T^3+25T^4")
local_lines([1, -1], 2, "zeta Euler factor 1 - T (as a factor of 1/zeta)")
local_lines([1, 2*np.sqrt(3)*np.cos(0.7), 3], 3, "a Ramanujan (local Lee-Yang) factor 1 - 2 sqrt3 cos(.7) T + 3T^2")
# (b)
print("\n(b) two-variable Lee-Yang example on (log 2, log 3)")
th = mp.pi/3
U = mp.matrix([[mp.cos(th), mp.sin(th)], [-mp.sin(th), mp.cos(th)]])
def P(z1, z2):
    return 1 + U[0,0]*z1 + U[1,1]*z2 + (U[0,0]*U[1,1]-U[0,1]*U[1,0])*z1*z2
# mixed Taylor coefficient of log P at 0: c11 = d^2/dz1dz2 log P (0,0)
c11 = mp.diff(lambda a, b: mp.log(P(a, b)), (0, 0), (1, 1))
print("   P(z1,z2) =", "1 + %s z1 + %s z2 + %s z1 z2" % (mp.nstr(U[0,0],6), mp.nstr(U[1,1],6), mp.nstr(U[0,0]*U[1,1]-U[0,1]*U[1,0],6)))
print("   mixed log-coefficient c_11 =", mp.nstr(c11, 12), "(nonzero => KS Fourier side has mass at log 6)")
l1, l2 = mp.log(2), mp.log(3)
f = lambda x: P(mp.e**(1j*l1*x), mp.e**(1j*l2*x))
# count zeros of f in the box [0, X] x [-H, H] by the argument principle and compare with real zeros
X, H = mp.mpf(60), mp.mpf(3)
def argcount(X, H, n=6000):
    pts = [mp.mpc(0,-H) + (X)*k/n for k in range(n)] + [mp.mpc(X,-H) + 1j*2*H*k/n for k in range(n)] \
        + [mp.mpc(X, H) - X*k/n for k in range(n)] + [mp.mpc(0, H) - 1j*2*H*k/n for k in range(n+1)]
    tot = 0
    for a, b in zip(pts[:-1], pts[1:]):
        d = mp.arg(f(b)/f(a)); tot += d
    return tot/(2*mp.pi)
# real zeros via sign changes of f(x)*exp(-i (l1+l2) x/2) which is real (self-inversive)
g = lambda x: mp.re(f(x)*mp.e**(-1j*(l1+l2)*x/2))
gi = lambda x: mp.im(f(x)*mp.e**(-1j*(l1+l2)*x/2))
xs = [X*k/12000 for k in range(12001)]
vals = [g(x) for x in xs]
real_zeros = sum(1 for a, b in zip(vals[:-1], vals[1:]) if a*b < 0)
print("   max |Im part| of f*e^{-i(l1+l2)x/2} on grid:", mp.nstr(max(abs(gi(x)) for x in xs[::50]), 5))
print("   zeros in box [0,60]x[-3,3] (argument principle):", mp.nstr(argcount(X, H), 6), "  real sign changes on [0,60]:", real_zeros)
# the separable (Euler-supported) counterpart: P1(z1) P2(z2) -> zero set = union of arithmetic progressions
print("   separable counterpart (1+z1)(1+z2): zeros = (2k+1)pi/log2  U  (2k+1)pi/log3  (two lattices, periodic pieces)")

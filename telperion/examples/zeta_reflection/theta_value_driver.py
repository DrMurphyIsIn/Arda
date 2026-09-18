#!/usr/bin/env python3
"""ANDÚRIL θ-value driver -- numeric validation + certificate hints for ThetaValue.lean.

Validates the φ(14) = arg Γℝ(1/2+14i) = Riemann-Siegel θ(14) target three ways, exhibits the
Euler/Weierstrass series decomposition the Lean instrument certifies, and prints the rational
certificate constants (arctan Taylor boxes, honest/rational/cubic split) the scale-up emits.

conjecture1_proved = False.  A numeric oracle for the kernel instrument, not a proof.
"""
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 50
X = mp.mpf(1) / 4          # Re of Gamma argument (s/2 = 1/4 + it/2 for s=1/2+it)
Y = mp.mpf(7)             # Im  (t/2 = 7 at t=14)
T = mp.mpf(14)


def target_three_ways():
    phi_siegel = mp.siegeltheta(T)
    s = mp.mpf("0.5") + 1j * T
    phi_argGR = mp.arg(mp.pi ** (-s / 2) * mp.gamma(s / 2))
    phi_series = -(T / 2) * mp.log(mp.pi) + mp.im(mp.loggamma(mp.mpc(X, Y)))
    return phi_siegel, phi_argGR, phi_series


def imLn(n):
    """Im L_n = y*log n - sum_{k=0}^n arctan(y/(x+k)) -- the finite value ThetaValue.imLn_formula."""
    return Y * mp.log(n) - sum(mp.atan(Y / (X + k)) for k in range(0, n + 1))


def phi_box(K0=30, K1=2000):
    """The full phi(14) box via honest arctan (k<=K0) + rational harmonic tail + cubic bracket."""
    honest = Y * mp.log(K0) - sum(mp.atan(Y / (X + k)) for k in range(0, K0 + 1))
    Hrat = sum(F(4, 4 * k + 1) for k in range(K0 + 1, K1 + 1))     # exact rational sum 1/(x+k)
    z = mp.mpf(K1) + 1 + X
    Afar_lo = mp.log(z) - 1 / (2 * z) - 1 / (12 * z ** 2)
    Afar_hi = mp.log(z) - 1 / (2 * z)
    LIN_lo = Y * (-mp.log(K0) + (-float(Hrat) + Afar_lo))
    LIN_hi = Y * (-mp.log(K0) + (-float(Hrat) + Afar_hi))
    cub_hi = sum((Y / (X + k)) ** 3 / 3 for k in range(K0 + 1, 300000))
    cub_lo = sum((Y / (X + k)) ** 3 / 3 - (Y / (X + k)) ** 5 / 5 for k in range(K0 + 1, 300000))
    imlogG_lo, imlogG_hi = honest + LIN_lo + cub_lo, honest + LIN_hi + cub_hi
    lp, hp = mp.mpf("1.1447298858"), mp.mpf("1.1447298859")   # log pi box
    return (-7 * hp + imlogG_lo, -7 * lp + imlogG_hi)


def arctan_taylor_box(a, b, N):
    """Rational box for arctan(a/b), a,b>0: reflect if a/b>1, then N-term Taylor bracket."""
    u = F(a, b)
    if u > 1:
        u = 1 / u
        ps = sum((-1) ** j * u ** (2 * j + 1) / (2 * j + 1) for j in range(N))
        err = u ** (2 * N + 1) / (2 * N + 1)
        return ("reflected pi/2 - box", ps, err)
    ps = sum((-1) ** j * u ** (2 * j + 1) / (2 * j + 1) for j in range(N))
    err = u ** (2 * N + 1) / (2 * N + 1)
    return ("direct", ps, err)


if __name__ == "__main__":
    s, g, ser = target_three_ways()
    print("=== phi(14) target, three ways (all agree) ===")
    print(f"  siegeltheta(14)             = {mp.nstr(s, 20)}")
    print(f"  arg GammaR(1/2+14i)         = {mp.nstr(g, 20)}")
    print(f"  -7 log pi + Im loggamma(1/4+7i) = {mp.nstr(ser, 20)}")
    print()
    print("=== Im L_n convergence (ThetaValue.imLnVal), limit = Im loggamma = arg Gamma + 2pi ===")
    print(f"  arg Gamma(z)   = {float(mp.arg(mp.gamma(mp.mpc(X, Y)))):.6f}  (principal, WRONG branch)")
    print(f"  Im loggamma(z) = {float(mp.im(mp.loggamma(mp.mpc(X, Y)))):.6f}  (continuous, the limit Lambda)")
    for n in (1, 2, 5, 50, 500, 5000):
        print(f"  Im L_{n:<5} = {float(imLn(n)):+.5f}")
    print()
    lo, hi = phi_box()
    print("=== phi(14) kernel box (honest K0=30, rational K1=2000, cubic tail) ===")
    print(f"  box = [{float(lo):.7f}, {float(hi):.7f}]  width={float(hi - lo):.2e}  target -1.7829487")
    print(f"  contains target: {float(lo) <= float(s) <= float(hi)};  width<=2e-3: {float(hi-lo)<=2e-3}")
    print()
    print("=== arctan Taylor box certificate constants (ThetaValue.arctan_inv28_box / arctan28_box) ===")
    kind, ps, err = arctan_taylor_box(1, 28, 2)
    print(f"  arctan(1/28) N=2: atanPS={ps}={float(ps):.10f}  err<={err}={float(err):.2e}")
    print(f"  arctan(28) = pi/2 - arctan(1/28), same box width")

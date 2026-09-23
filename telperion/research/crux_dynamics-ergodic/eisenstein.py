"""Rigorous (Arb) evaluators for the crux_dynamics-ergodic lane.

conjecture1_proved = False.  Trust class: Arb interval arithmetic (python-flint), not the kernel.

* estar(x, y, s): the completed Eisenstein series of PSL(2,Z),
      E*(z, s) = Lambda(2s) E(z, s),  Lambda(w) = pi^{-w/2} Gamma(w/2) zeta(w),
  from its Fourier expansion
      E*(z,s) = Lambda(2s) y^s + Lambda(2s-1) y^{1-s}
                + 4 sqrt(y) sum_{n>=1} n^{s-1/2} sigma_{1-2s}(n) K_{s-1/2}(2 pi n y) cos(2 pi n x),
  truncated at n <= N, plus a RIGOROUS tail ball, valid when 1/2 <= Re s <= 1:
      |K_nu(x)| <= K_{Re nu}(x) <= K_{1/2}(x) = sqrt(pi/(2x)) e^{-x}   (0 <= Re nu <= 1/2),
      |n^{s-1/2}| <= n^{1/2},  |sigma_{1-2s}(n)| <= d(n) <= n,
  so |tail| <= 2 sum_{n>N} n q^n <= 2 (N+1) q^{N+1} / (1-q)^2 with q = e^{-2 pi y}.
  E*(z, s) = E*(z, 1-s), and E*(z, s) = pi^{-s} Gamma(s) Z_Q(s) / 2 where Z_Q is the Epstein zeta
  function of Q(m, n) = |m z + n|^2 / y; so zeros of E*(z, .) in the strip are zeros of Z_Q.
* estar_lattice(x, y, s): brute-force lattice sum (floats), only for Re s large (sanity check).
* epstein_x2_5y2(s): Z_{x^2+5y^2}(s) = zeta(s) L(s, chi_-20) + L(s, chi_-4) L(s, chi_5) (genus
  theory; no truncation).
* dh(s): the Davenport-Heilbronn function (conductor 5), from Hurwitz zeta values.
"""
from __future__ import annotations

import math
from fractions import Fraction

from flint import acb, arb, ctx

ctx.prec = 200


def arb_q(x) -> arb:
    if isinstance(x, arb):
        return x
    x = Fraction(x)
    return arb(x.numerator) / arb(x.denominator)


def completed_zeta(w: acb) -> acb:
    """Lambda(w) = pi^{-w/2} Gamma(w/2) zeta(w)."""
    return arb.pi() ** (-w / 2) * (w / 2).gamma() * w.zeta()


def divisors(n: int):
    small = [d for d in range(1, int(math.isqrt(n)) + 1) if n % d == 0]
    return sorted(set(small + [n // d for d in small]))


def estar(x, y, s: acb, N: int = 30, rigorous: bool = True) -> acb:
    """Rigorous enclosure of E*(x + i y, s) for 1/2 <= Re s <= 1 (s may be a ball).
    With rigorous=False the truncated sum is returned without the tail ball (sanity checks at
    Re s > 1 only; not a certificate)."""
    if rigorous and not (s.real.lower() >= arb("0.5") and s.real.upper() <= 1):
        raise ValueError("tail bound only certified for 1/2 <= Re s <= 1")
    xa, ya = arb_q(x), arb_q(y)
    yc = acb(ya)
    total = completed_zeta(2 * s) * yc ** s + completed_zeta(2 * s - 1) * yc ** (1 - s)
    nu = s - acb("0.5")
    acc = acb(0)
    for n in range(1, N + 1):
        sig = acb(0)
        for d in divisors(n):
            sig += acb(d) ** (1 - 2 * s)
        k = acb(2 * arb.pi() * n * ya).bessel_k(nu)
        c = (2 * arb.pi() * n * xa).cos()
        acc += acb(n) ** nu * sig * k * c
    total += 4 * ya.sqrt() * acc
    if not rigorous:
        return total
    q = (-2 * arb.pi() * ya).exp()
    tail = 2 * (N + 1) * q ** (N + 1) / (1 - q) ** 2
    rad = tail.upper()
    return total + acb(arb(0, rad), arb(0, rad))


def estar_lattice(x: float, y: float, s: complex, M: int = 300) -> complex:
    """Float lattice sum E*(z,s) = pi^{-s} Gamma(s) Z_Q(s)/2 (only for Re s large)."""
    import mpmath
    tot = mpmath.mpf(0)
    for m in range(-M, M + 1):
        for n in range(-M, M + 1):
            if m == 0 and n == 0:
                continue
            q = ((m * x + n) ** 2 + (m * y) ** 2) / y
            tot += mpmath.power(q, -s)
    return complex(mpmath.power(mpmath.pi, -s) * mpmath.gamma(s) * tot / 2)


def _chi_m4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)


def _chi_5(n):
    r = n % 5
    return 0 if r == 0 else (1 if r in (1, 4) else -1)


def _chi_m20(n):
    return _chi_m4(n) * _chi_5(n)


def dirichlet_L(s: acb, chi, q: int) -> acb:
    tot = acb(0)
    for a in range(1, q + 1):
        c = chi(a)
        if c:
            tot += c * s.zeta(acb(a) / q)
    return acb(q) ** (-s) * tot


def epstein_x2_5y2(s: acb) -> acb:
    """Z_{x^2 + 5 y^2}(s) via genus theory: zeta(s) L(s,chi_-20) + L(s,chi_-4) L(s,chi_5)."""
    return s.zeta() * dirichlet_L(s, _chi_m20, 20) + dirichlet_L(s, _chi_m4, 4) * dirichlet_L(s, _chi_5, 5)


_sq5 = arb(5).sqrt()
DH_KAPPA = ((arb(10) - 2 * _sq5).sqrt() - 2) / (_sq5 - 1)


def dh(s: acb) -> acb:
    """Davenport-Heilbronn function 5^{-s} (zeta(s,1/5) + k zeta(s,2/5) - k zeta(s,3/5) - zeta(s,4/5))."""
    return acb(5) ** (-s) * (s.zeta(acb(1) / 5) + DH_KAPPA * s.zeta(acb(2) / 5)
                             - DH_KAPPA * s.zeta(acb(3) / 5) - s.zeta(acb(4) / 5))

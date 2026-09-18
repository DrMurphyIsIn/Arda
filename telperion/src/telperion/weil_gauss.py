"""Rigorous rational enclosures of the Weil functional on Gaussian autocorrelations
(``weil_form_enclosure`` backend).

conjecture1_proved = False.  Nothing here proves, approaches, or claims RH.

WHAT IS COMPUTED
----------------
For the registry vocabulary ``WeilExplicit`` (mirrored in
``telperion/missions/mirrormere/lean/Statements/MMDefs.lean`` and
``telperion/missions/rh/lean/Statements/RHDefs.lean``), the W3c membership goal
``MM_zeta_comb_membership`` asks for the sign of

    W(g) := Re (weilForm (autocorr g))
          = Re (archSide (autocorr g) - primeSide (autocorr g)).

This module computes a rigorous two-sided rational enclosure ``lo <= W(g) <= hi`` for one
explicitly parameterised family of test functions -- the shifted, frequency-modulated
Gaussians

    g(u) = exp(-(u - c)^2 / (2 a^2)) * exp(i omega u),          a > 0, c, omega real,

for which every term of ``weilForm (autocorr g)`` has a closed form (section "CLOSED FORMS"
below).  The enclosure is produced with Arb/FLINT ball arithmetic (python-flint), the same
documented non-kernel trust seam as ``li_coeff`` and ``bragg_coeff``.

WHY A GAUSSIAN AND NOT A BUMP (stated, not hidden)
--------------------------------------------------
A Gaussian is NOT in the registered test class ``WeilExplicit.IsWeilTest`` (smooth AND
compactly supported); it is in the larger Guinand class, where the Weil/Guinand identity
also holds.  It is used here for the same reason the E8 design memo
(``telperion/docs/E8_LIMIT_EXPLICIT_FORMULA_DESIGN_2026-09-18.md`` section 4) used it: every
term is available in closed form, so the numeric read-back tests the NORMALISATION of the
statement (a missing conj, ``1 - conj rho`` vs ``rho``, a factor 2pi) rather than the quality
of a quadrature.  The value certified is therefore a read-back datum about the vocabulary,
NOT an instance of the registry goal's quantifier.  A compactly supported instance is a
strictly harder quadrature problem and is queued with the D2/D3 finite faces.

CLOSED FORMS (derived, then numerically re-checked against the defining integrals)
---------------------------------------------------------------------------------
With ``f := autocorr g``, ``f u = integral_v g v * conj (g (v - u))``:

    f(u)      = a sqrt(pi) exp(-u^2 / (4 a^2)) exp(i omega u)        (c cancels)
    f(0)      = a sqrt(pi)
    H_f(s)    = weilKernel f s = 2 pi a^2 exp(a^2 z^2),  z = s - 1/2 + i omega
    H_f(0) + H_f(1) = 4 pi a^2 exp(a^2 (1/4 - omega^2)) cos(a^2 omega)
    h_f(r)    = H_f(1/2 + i r) = 2 pi a^2 exp(-a^2 (r + omega)^2) = |h_g(r)|^2 >= 0

(the last line is the Weil-criterion shape: the autocorrelation's transform is a square on
the critical line), so

    W(g) = 4 pi a^2 exp(a^2 (1/4 - omega^2)) cos(a^2 omega)
           - a sqrt(pi) log pi
           + a^2 * INT,    INT := integral_r exp(-a^2 (r + omega)^2) Re psi(1/4 + i r/2) dr
           - 2 a sqrt(pi) * SUM,
           SUM := sum_{n >= 2} Lambda(n) n^{-1/2} exp(-(log n)^2 / (4 a^2)) cos(omega log n).

Both ``INT`` and ``SUM`` are enclosed with explicit, elementary tail bounds:

  * prime tail, n > N:  |Lambda(n)| <= log n, and with x = log n,
    sum_{n > N} log n * n^{-1/2} e^{-(log n)^2/(4a^2)}
      <= integral_{log N}^{infinity} x e^{x/2} e^{-x^2/(4 a^2)} dx
      <= integral_X^infinity x e^{-x^2/(8 a^2)} dx = 4 a^2 exp(-X^2 / (8 a^2)),
    valid once X := log N >= 4 a^2 (then x/2 <= x^2/(8 a^2)); the code REFUSES a cutoff that
    violates X >= 4 a^2.
  * archimedean tail, |r| > R:  |Re psi(1/4 + i r/2)| <= 1 + |r| for all real r (Binet's
    formula gives Re psi(1/4 + i y) = log|1/4 + i y| + O(1/|y|^2), so the linear bound has
    enormous slack; it is the documented literature-grade input of this module, and R is
    chosen so the Gaussian factor at R is below 1e-60, making the tail contribution smaller
    than the Arb radius of the main term by many orders).  With U := R - |omega| > 0,
    integral_{|r|>R} e^{-a^2 (r + omega)^2}(1 + |r|) dr
      <= 2 e^{-a^2 U^2} ((1 + |omega|)/(2 a^2 U) + 1/(2 a^2)).

EXTERNAL ANCHOR (refuse-to-emit gate)
-------------------------------------
``anchor_check`` re-derives f(0), f(u) at sample points, H_f(0), H_f(1) and h_f(r) by DIRECT
numerical quadrature of the defining integrals (``autocorr``/``weilKernel`` as written in
MMDefs) and compares them with the closed forms above.  A normalisation slip -- a dropped
conjugate, ``g (v - u)`` vs ``g (u - v)``, ``e^{(s-1/2)u}`` vs ``e^{(1/2-s)u}`` -- fails here
and ABORTS before any certificate is minted.  This is the numeric half of the blind read-back
the W3c design memo mandates.

Dependency: python-flint (Arb/FLINT) for the enclosures, mpmath for the anchor quadratures.
conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Tuple

# python-flint is imported INSIDE the functions: telperion/__init__ imports the emitter
# module unconditionally (sensitivity-registry completeness), so nothing at module level
# here may require flint.


@dataclass(frozen=True)
class WeilGaussParams:
    """One Gaussian test function g(u) = exp(-(u-c)^2/(2a^2)) e^{i omega u}.

    ``c`` is carried for provenance only: the autocorrelation, and hence every term of
    ``weilForm (autocorr g)``, is independent of ``c`` (a translation of g is a phase on
    its transform and cancels against the conjugate factor).  ``anchor_check`` verifies that
    cancellation numerically rather than assuming it."""

    a: Fraction
    omega: Fraction
    c: Fraction = Fraction(0)
    cutoff: int = 5000          # prime-side truncation N
    r_radius: Fraction = Fraction(0)   # archimedean truncation R (0 = auto)
    prec_bits: int = 256

    def __post_init__(self):
        if self.a <= 0:
            raise ValueError(f"weil_gauss REFUSED: need a > 0, got {self.a}")
        if self.cutoff < 4:
            raise ValueError(f"weil_gauss REFUSED: need cutoff >= 4, got {self.cutoff}")


def _ball_to_fractions(ball) -> Tuple[Fraction, Fraction]:
    """Outward exact (lo, hi) of an arb ball; see rh_jensen.coefficients._arb_ball_to_fractions."""
    from .rh_jensen.coefficients import _arb_ball_to_fractions

    return _arb_ball_to_fractions(ball)


def _von_mangoldt(n: int) -> int | None:
    """Return the prime p with n = p^k (k >= 1), else None (Lambda(n) = log p, resp. 0)."""
    if n < 2:
        return None
    p = 2
    while p * p <= n:
        if n % p == 0:
            break
        p += 1
    else:
        p = n
    q = n
    while q % p == 0:
        q //= p
    return p if q == 1 else None


# ---------------------------------------------------------------------------
# Anchor: the closed forms against the DEFINING integrals of MMDefs
# ---------------------------------------------------------------------------

_ANCHOR_TOL = 1e-20


def anchor_check(params: WeilGaussParams) -> None:
    """Re-derive the closed forms by direct quadrature of the MMDefs definitions; raise on drift.

    Checks, at 30-digit working precision:
      autocorr g u  ==  a sqrt(pi) exp(-u^2/(4a^2)) exp(i omega u)     (u = 0, 0.7, -1.3)
      weilKernel (autocorr g) s == 2 pi a^2 exp(a^2 (s - 1/2 + i omega)^2)   (s = 0, 1, 1/2 + 2i)
      weilKernel (autocorr g) (1/2 + i r) == |weilKernel g (1/2 + i r)|^2    (r = 0.4)
    The conjugate in ``autocorr`` and the sign of the exponent in ``weilKernel`` are exactly
    what these catch.  conjecture1_proved = False."""
    import mpmath as mp

    old = mp.mp.dps
    try:
        mp.mp.dps = 30
        a = mp.mpf(params.a.numerator) / params.a.denominator
        c = mp.mpf(params.c.numerator) / params.c.denominator
        om = mp.mpf(params.omega.numerator) / params.omega.denominator

        def g(v):
            return mp.e ** (-((v - c) ** 2) / (2 * a ** 2)) * mp.e ** (1j * om * v)

        def autocorr(u):
            return mp.quad(lambda v: g(v) * mp.conj(g(v - u)), [-mp.inf, c, mp.inf])

        def closed_f(u):
            return a * mp.sqrt(mp.pi) * mp.e ** (-(u ** 2) / (4 * a ** 2)) * mp.e ** (1j * om * u)

        for u in (mp.mpf(0), mp.mpf("0.7"), mp.mpf("-1.3")):
            got, want = autocorr(u), closed_f(u)
            if abs(got - want) > _ANCHOR_TOL * (1 + abs(want)):
                raise ValueError(
                    f"weil_gauss ANCHOR FAILED: autocorr({u}) = {got} but closed form = {want}")

        def weil_kernel(fn, s):
            return mp.quad(lambda u: fn(u) * mp.e ** ((s - mp.mpf(1) / 2) * u),
                           [-mp.inf, 0, mp.inf])

        def closed_H(s):
            z = s - mp.mpf(1) / 2 + 1j * om
            return 2 * mp.pi * a ** 2 * mp.e ** (a ** 2 * z ** 2)

        for s in (mp.mpf(0), mp.mpf(1), mp.mpf(1) / 2 + 2j):
            got, want = weil_kernel(closed_f, s), closed_H(s)
            if abs(got - want) > _ANCHOR_TOL * (1 + abs(want)):
                raise ValueError(
                    f"weil_gauss ANCHOR FAILED: weilKernel (autocorr g) {s} = {got} but "
                    f"closed form = {want}")

        # the Weil-criterion factorisation on the line: H_{g*g~}(1/2+ir) = |H_g(1/2+ir)|^2
        r = mp.mpf("0.4")
        hg = weil_kernel(g, mp.mpf(1) / 2 + 1j * r)
        hf = closed_H(mp.mpf(1) / 2 + 1j * r)
        if abs(hf - abs(hg) ** 2) > _ANCHOR_TOL * (1 + abs(hf)):
            raise ValueError(
                f"weil_gauss ANCHOR FAILED: h_f({r}) = {hf} but |h_g({r})|^2 = {abs(hg) ** 2}")
    finally:
        mp.mp.dps = old


# ---------------------------------------------------------------------------
# The rigorous enclosure
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class WeilGaussEnclosure:
    """Arb-enclosed rational data for one Gaussian instance.  ``lo <= W(g) <= hi``."""

    params: WeilGaussParams
    pole_lo: Fraction
    pole_hi: Fraction
    logpi_lo: Fraction
    logpi_hi: Fraction
    arch_lo: Fraction
    arch_hi: Fraction
    prime_lo: Fraction
    prime_hi: Fraction

    @property
    def lo(self) -> Fraction:
        return self.pole_lo - self.logpi_hi + self.arch_lo - self.prime_hi

    @property
    def hi(self) -> Fraction:
        return self.pole_hi - self.logpi_lo + self.arch_hi - self.prime_lo


def enclose_weil_gauss(params: WeilGaussParams) -> WeilGaussEnclosure:
    """Rigorous rational enclosure of ``Re (weilForm (autocorr g))`` for the Gaussian ``params``.

    Runs ``anchor_check`` first (refuse-to-emit gate).  Every term is an Arb ball widened
    outward to exact rationals; the two truncation tails are added as symmetric slack using
    the elementary bounds documented in the module docstring.  conjecture1_proved = False."""
    from flint import arb, acb, ctx

    anchor_check(params)

    old_prec = ctx.prec
    try:
        ctx.prec = params.prec_bits
        a = arb(params.a.numerator) / params.a.denominator
        om = arb(params.omega.numerator) / params.omega.denominator
        pi = arb.pi()

        # ---- pole terms: 4 pi a^2 exp(a^2 (1/4 - omega^2)) cos(a^2 omega)
        pole = 4 * pi * a ** 2 * (a ** 2 * (arb(1) / 4 - om ** 2)).exp() * (a ** 2 * om).cos()

        # ---- -g(0) log pi term, with f(0) = a sqrt(pi)
        logpi = a * pi.sqrt() * pi.log()

        # ---- archimedean: a^2 * INT, INT = int e^{-a^2 (r+om)^2} Re psi(1/4 + i r/2) dr
        R = params.r_radius
        if R == 0:
            # Gaussian factor e^{-a^2 U^2} < 1e-60 with U = R - |omega|
            import math
            u_needed = math.sqrt(60 * math.log(10)) / float(params.a)
            R = Fraction(math.ceil(u_needed + abs(float(params.omega)) + 1))
        R_arb = arb(R.numerator) / R.denominator
        U = R - abs(params.omega)
        if U <= 0:
            raise ValueError(
                f"weil_gauss REFUSED: archimedean radius R={R} does not exceed |omega|")

        def integrand(z, analytic):
            # e^{-a^2 (z+om)^2} * (psi(1/4 + i z/2) + psi(1/4 - i z/2)) / 2 -- entire on the
            # real axis (the poles of psi sit at z = +- i(1/2 + 2k), off the contour).
            w = acb(-1) * (acb(a) ** 2) * (z + acb(om)) ** 2
            half = acb(1) / 2
            psi_plus = (acb(1) / 4 + acb(0, 1) * z / 2).digamma()
            psi_minus = (acb(1) / 4 - acb(0, 1) * z / 2).digamma()
            return w.exp() * half * (psi_plus + psi_minus)

        integral = acb.integral(integrand, -R_arb, R_arb)
        if abs(integral.imag.mid()) > 1e-20:
            raise ValueError(
                f"weil_gauss REFUSED: archimedean integral has nonreal value {integral}")
        # tail: 2 e^{-a^2 U^2} ((1+|omega|)/(2 a^2 U) + 1/(2 a^2)), with |Re psi| <= 1 + |r|
        U_arb = arb(U.numerator) / U.denominator
        om_abs = arb(abs(params.omega).numerator) / abs(params.omega).denominator
        tail_arch = 2 * (-(a ** 2) * U_arb ** 2).exp() * (
            (1 + om_abs) / (2 * a ** 2 * U_arb) + 1 / (2 * a ** 2))
        arch_ball = a ** 2 * integral.real
        arch_tail_hi = _ball_to_fractions(a ** 2 * tail_arch)[1]
        arch_lo, arch_hi = _ball_to_fractions(arch_ball)
        arch_lo -= arch_tail_hi
        arch_hi += arch_tail_hi

        # ---- prime side: 2 a sqrt(pi) * sum_{n>=2} Lambda(n) n^{-1/2} e^{-(log n)^2/(4a^2)} cos(om log n)
        X = Fraction(params.cutoff).numerator  # cutoff N; the bound needs log N >= 4 a^2
        import math
        logN = math.log(params.cutoff)
        if logN < 4 * float(params.a) ** 2:
            raise ValueError(
                f"weil_gauss REFUSED: cutoff {params.cutoff} too small for the tail bound "
                f"(need log N >= 4 a^2 = {4 * float(params.a) ** 2})")
        total = arb(0)
        for n in range(2, params.cutoff + 1):
            p = _von_mangoldt(n)
            if p is None:
                continue
            lam = arb(p).log()
            ln = arb(n).log()
            total += lam / arb(n).sqrt() * (-(ln ** 2) / (4 * a ** 2)).exp() * (om * ln).cos()
        prime_ball = 2 * a * pi.sqrt() * total
        logN_arb = arb(params.cutoff).log()
        tail_prime = 4 * a ** 2 * (-(logN_arb ** 2) / (8 * a ** 2)).exp()
        prime_tail_hi = _ball_to_fractions(2 * a * pi.sqrt() * tail_prime)[1]
        prime_lo, prime_hi = _ball_to_fractions(prime_ball)
        prime_lo -= prime_tail_hi
        prime_hi += prime_tail_hi

        pole_lo, pole_hi = _ball_to_fractions(pole)
        logpi_lo, logpi_hi = _ball_to_fractions(logpi)
    finally:
        ctx.prec = old_prec

    return WeilGaussEnclosure(
        params=params,
        pole_lo=pole_lo, pole_hi=pole_hi,
        logpi_lo=logpi_lo, logpi_hi=logpi_hi,
        arch_lo=arch_lo, arch_hi=arch_hi,
        prime_lo=prime_lo, prime_hi=prime_hi,
    )


def round_enclosure(lo: Fraction, hi: Fraction, digits: int = 12) -> Tuple[Fraction, Fraction]:
    """Round (lo, hi) OUTWARD to `digits` decimals -- short literals for the Lean statement.

    Outward rounding keeps the true value enclosed, so the emitted rational bounds stay
    rigorous while remaining human-readable."""
    scale = 10 ** digits
    import math

    lo_r = Fraction(math.floor(lo * scale), scale)
    hi_r = Fraction(math.ceil(hi * scale), scale)
    return lo_r, hi_r

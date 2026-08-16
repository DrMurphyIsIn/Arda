"""The (L) legs layer, Telperion-re-derived: length-2 legs are optimal.

Origin: proof/verification/legs.py (certify_cherries_optimal), Lean-green in
origin as R47Legs.lean — this is the audit's independent second path.  Every
claim is a PURE RATIONAL FACT (no symbols): the pipeline emits kernel facts in
unevaluated-power spelling.

  * the ell = 2 reference identity  F_2(1+5) = 621/64  (= rho_B^11);
  * ell = 1: three exact power comparisons + the 2^11 < (621/64)^5 tail;
  * the ell >= 3 induction bases: beta^2 >= beta + 1/4, phi_3 <= beta^3,
    phi_4 <= beta^4  (beta = 483/400);
  * THE BIGNUM: beta^253 * (3/2)^11 < (621/64)^23  (the 726-digit crux,
    ratio ~1.108 — same kernel class as the exponent-317 crux);
  * the finite region: F_ell(1+c)^11 < (621/64)^(1+c*ell) for every
    (ell, c) with 3 <= ell <= 21 and c*ell <= 21  (39 cells).
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from telperion import GridSpec, InequalityFamily, LeanProfile, ValidationReport

RB = Fr(621, 64)
BETA = Fr(483, 400)


def phi(ell: int) -> Fr:
    if ell <= 1:
        return Fr(1)
    a, b = Fr(1), Fr(3, 2)
    for _ in range(3, ell + 1):
        a, b = b, b + Fr(1, 4) * a
    return b


def arm_base(ell: int, c: int) -> Fr:
    d = 1 + c
    delta = 1 if ell == 1 else 2
    return phi(ell) ** c + c * Fr(1, d * delta) * phi(ell - 1) * phi(ell) ** (c - 1)


def _pow(base: Fr, e: int) -> sp.Expr:
    return sp.Pow(sp.Rational(base), sp.Integer(e), evaluate=False)


def _claims():
    """(name, lhs, rel, rhs) in unevaluated spelling; the certified target is
    the reduced difference."""
    out = []
    # ell = 2 reference identity
    out.append(("legs_ell2_reference", sp.Rational(arm_base(2, 5)), "=",
                sp.Rational(RB)))
    # ell = 1
    for c in (1, 2, 3):
        out.append((f"legs_ell1_c{c}", _pow(arm_base(1, c), 11), "<",
                    _pow(RB, 1 + c)))
    out.append(("legs_ell1_tail", _pow(Fr(2), 11), "<", _pow(RB, 5)))
    # induction bases
    out.append(("legs_beta_step", sp.Rational(BETA + Fr(1, 4)), "≤",
                _pow(BETA, 2)))
    out.append(("legs_phi3_base", sp.Rational(phi(3)), "≤", _pow(BETA, 3)))
    out.append(("legs_phi4_base", sp.Rational(phi(4)), "≤", _pow(BETA, 4)))
    # THE BIGNUM (726 digits when expanded; spelled unevaluated)
    out.append(("legs_bignum",
                sp.Mul(_pow(BETA, 253), _pow(Fr(3, 2), 11), evaluate=False),
                "<", _pow(RB, 23)))
    # the finite region
    for ell in range(3, 22):
        for c in range(1, 21 // ell + 1):
            out.append((f"legs_ell{ell}_c{c}", _pow(arm_base(ell, c), 11), "<",
                        _pow(RB, 1 + c * ell)))
    return out


_CLAIMS = None


def claims():
    global _CLAIMS
    if _CLAIMS is None:
        _CLAIMS = _claims()
    return _CLAIMS


def family() -> InequalityFamily:
    cs = claims()

    def target(pt):
        name, lhs, rel, rhs = cs[pt["i"]]
        l, r = lhs.doit(), rhs.doit()
        return sp.expand(r - l) if rel in ("<", "≤") else sp.expand(l - r)

    return InequalityFamily(
        name="LegsCerts",
        symbols=(),
        grid=GridSpec([("i", list(range(len(cs))))]),
        lean_name=lambda pt: cs[pt["i"]][0],
        target=target,
    )


def spelling(pt):
    name, lhs, rel, rhs = claims()[pt["i"]]
    return (lhs, rel, rhs)


def profile() -> LeanProfile:
    return LeanProfile(namespace=("L", "Legs"))


def validation() -> ValidationReport:
    """Dual-engine: the origin module's own Fraction checks, re-run inline."""

    def origin_equiv():
        assert arm_base(2, 5) == RB
        assert all(arm_base(1, c) ** 11 < RB ** (1 + c) for c in (1, 2, 3))
        assert Fr(2) ** 11 < RB**5
        assert BETA**2 >= BETA + Fr(1, 4)
        assert phi(3) <= BETA**3 and phi(4) <= BETA**4
        assert BETA**253 * Fr(3, 2) ** 11 < RB**23
        for ell in range(3, 22):
            for c in range(1, 21 // ell + 1):
                assert arm_base(ell, c) ** 11 < RB ** (1 + c * ell), (ell, c)

    return ValidationReport.from_asserts([("legs_origin_equivalent", origin_equiv)])

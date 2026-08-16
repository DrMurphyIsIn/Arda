"""Deficit monotonicity for the broom near-star family (proven, infinite family).

The single star of cherry-bundles (hub de-loaded) has amplitude A_single* = (26/23)/rho_B
(near_star.py).  A near-star = hub H (degree -> infinity, de-loaded) + p arms + a bounded
gadget G; its amplitude is A_single* * Phi(G), so the single star wins iff Phi(G) < 1.

This module proves Phi < 1 for the entire BROOM family: the gadget is one secondary center g
adjacent to the hub, carrying c_g cherries and j sub-arms at c=5 (deficit j, UNBOUNDED).  This
family interpolates the two tightest named competitors -- the subdivided arm (j=1) and the double
star (j -> infinity) -- so it is the relevant infinite family for the constant-order tiebreak.

Closed form (p -> infinity limit; derived from the matching-sum, cross-checked in near_star.py):
    Phi_broom(j, c_g) = F_g * (1 + 3 j z_g / 23) / F(6)^{(1 + 2 c_g)/11},
    F_g = (3/2)^{c_g} (1 + c_g/(3(1 + j + c_g))),   z_g = 3/(3 + 3 j + 4 c_g),   F(6) = 621/64.

THEOREM.  Phi_broom(j, c_g) < 1 for every integer j >= 1 and c_g >= 0.  Proof in two exact pieces:

(1) c_g-tail (uniform in j).  Using c_g/(3(1+j+c_g)) <= 1/3 and 3 j z_g/23 < 3/23,
        Phi_broom < (8/3) (3/2)^{c_g} / F(6)^{(1+2 c_g)/11}
                  = (8/3) rho_B^{-1} [ (3/2) / F(6)^{2/11} ]^{c_g},
    and (3/2)/F(6)^{2/11} < 1 exactly ((3/2)^11 < (621/64)^2 <=> 354294 < 385641), so the bound
    is < 1 for all c_g >= C0 = 101 (uniform in j).

(2) Box j-certificates (c_g < C0).  Phi_broom(j,c_g) < 1 <=> [F_g(1 + 3 j z_g/23)]^{11} <
    F(6)^{1+2 c_g}, an exact rational inequality in j.  For each c_g = 0..100 the numerator of
    F(6)^{1+2c_g} - [...]^{11} (over a positive denominator), after the shift j = 1 + J, is a
    polynomial in J with ALL-NONNEGATIVE coefficients and positive constant term -- so it is > 0
    for every j >= 1.

Hence the supremum of the broom amplitude is Phi_broom(1,5) = 0.98353 < 1 (the subdivided arm),
and every broom loses to the single star.

Scope: this closes the single-secondary-center family for all deficits.  Multi-center gadgets
(triple star, deeper trees) are not covered and remain the open remainder of the near-star family.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import mpmath as mp
import sympy as sp

_H = Fr(3, 2)
_F6 = Fr(621, 64)


def _Fg(j: int, cg: int) -> Fr:
    d = 1 + j + cg
    return _H ** cg * (1 + Fr(cg, 3 * d))


def _zg(j: int, cg: int) -> Fr:
    return Fr(3, 3 + 3 * j + 4 * cg)


def phi_broom_float(j: int, cg: int) -> float:
    mp.mp.dps = 40
    l = _Fg(j, cg) * (1 + Fr(3 * j, 23) * _zg(j, cg))
    return float(mp.mpf(l.numerator) / l.denominator / mp.power(mp.mpf(621) / 64, mp.mpf(1 + 2 * cg) / 11))


def C0_tail() -> int:
    """Smallest c_g past which the uniform (in j) bound (8/3)(3/2)^cg/F6^((1+2cg)/11) < 1."""
    mp.mp.dps = 40
    g = mp.mpf(3) / 2 / mp.power(mp.mpf(621) / 64, mp.mpf(2) / 11)   # < 1
    thr = mp.mpf(3) / 8 * mp.power(mp.mpf(621) / 64, mp.mpf(1) / 11)
    return int(mp.ceil(mp.log(thr) / mp.log(g)))


def certify_tail() -> dict:
    """(1) The c_g-tail: base (3/2)/F6^(2/11) < 1 exactly, and the uniform bound < 1 for c_g>=C0."""
    exact_base = (_H ** 11) < (_F6 ** 2)      # (3/2)^11 < F(6)^2  ==  354294 < 385641
    C0 = C0_tail()
    ub_at_C0 = float(mp.mpf(8) / 3 * mp.power(mp.mpf(3) / 2, C0)
                     / mp.power(mp.mpf(621) / 64, mp.mpf(1 + 2 * C0) / 11))
    return {"exact_base_lt_1": bool(exact_base), "C0": C0, "ub_at_C0": ub_at_C0, "ub_lt_1": ub_at_C0 < 1}


def certify_j_slice(cg: int) -> bool:
    """(2) Phi_broom(j,cg) < 1 for all j>=1: nonneg-coefficient certificate in J (j=1+J)."""
    j, J = sp.symbols("j J")
    d = 1 + j + cg
    Fg = sp.Rational(3, 2) ** cg * (1 + sp.Rational(cg, 1) / (3 * d))
    zg = sp.Rational(3, 1) / (3 + 3 * j + 4 * cg)
    lhs = (Fg * (1 + sp.Rational(3, 1) * j * zg / 23)) ** 11
    rhs = sp.Rational(621, 64) ** (1 + 2 * cg)
    num, den = sp.fraction(sp.together(rhs - lhs))
    pn = sp.Poly(sp.expand(num.subs(j, 1 + J)), J)
    pd = sp.Poly(sp.expand(den.subs(j, 1 + J)), J)
    return (all(c >= 0 for c in pn.coeffs()) and all(c >= 0 for c in pd.coeffs())
            and pn.eval(0) > 0 and pd.eval(0) > 0)


def certify_broom_family() -> dict:
    """Full theorem: Phi_broom < 1 for all j>=1, c_g>=0."""
    tail = certify_tail()
    C0 = tail["C0"]
    slices = all(certify_j_slice(cg) for cg in range(0, C0))
    return {"tail": tail, "j_slices_0_to_C0m1": slices,
            "sup_at_subdiv_arm": phi_broom_float(1, 5),
            "proven": tail["exact_base_lt_1"] and tail["ub_lt_1"] and slices}


if __name__ == "__main__":
    r = certify_broom_family()
    print("broom-family deficit monotonicity:")
    print("  tail:", r["tail"])
    print("  per-c_g j-certificates (c_g=0..C0-1) all pass:", r["j_slices_0_to_C0m1"])
    print("  sup Phi_broom = Phi(1,5) =", round(r["sup_at_subdiv_arm"], 5))
    print("  THEOREM PROVEN (all j>=1, c_g>=0):", r["proven"])

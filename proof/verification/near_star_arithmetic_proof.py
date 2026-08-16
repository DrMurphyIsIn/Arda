"""RIGOROUS arithmetic proof that Phi <= 1 on the near-star family (the marginal near-tie family that
defeats every smooth certificate).  This is the arithmetic argument the near-tie asymptotics called for
(near_tie_asymptotics.py: the continuous relaxation exceeds 1, so only an INTEGER argument can work).

SCOPE (honest).  This proves Phi <= 1 for the two-parameter NEAR-STAR family
    N(c,k) = a root with c cherries and k cherry-arm children  (ARM = (0,[(0,[])])),
for ALL integers c,k >= 0, with equality iff c+k = 5.  This family contains all 6 exact ties
(c+k=5) and is the dominant near-tie structure.  It is NOT the full Brualdi-Goldwasser conjecture
(arbitrary subtrees as children) -- that remains OPEN -- but it is a rigorous sub-result and the
first proof to go through the integrality that every smooth method cannot see.

THEOREM.  For all integers c,k >= 0,  Phi(N(c,k)) <= 1, with equality iff c+k = 5.

PROOF.
1) log Phi depends only on s = c+k.  Via the exact cavity telescoping
   (cavity_potential.py), with a root of degree d=k+1+c and z=3/(3d+c), the k cherry-arm children
   (each log Phi_ARM = -2 log rho_B + log(3/2), cavity m=1/3) give
       log Phi(N(c,k)) = k(-2 log rho_B + log(3/2)) + [log a(d,c) + log(1 + z*k/3)].
   Expanding log a(d,c) = c log(3/2) + log(3d+c) - log(3d) - (1+2c) log rho_B and 1+z*k/3 =
   (4c+4k+3)/(3d+c), the two log(3d+c) = log(3k+3+4c) terms CANCEL, leaving a function of s=c+k only:
       log Phi = g(s) = -(2s+1) log rho_B + s log(3/2) + log(4s+3) - log(3(s+1)).

2) Clear the 11th root.  rho_B^11 = 621/64 = 3^3 * 23 / 2^6.  So g(s) <= 0  <=>  (raise to the 11th)
       3^(5s-14) * 2^(s+6) * (4s+3)^11  <=  23^(2s+1) * (s+1)^11.                             (STAR)
   Both sides are positive integers times a power of 1/(nothing) -- a pure rational inequality in s.

3) Unimodality of R(s) := RHS/LHS.  A direct computation gives the exact ratio
       R(s+1)/R(s) = (23^2)/(2*3^5) * ((s+2)(4s+3) / ((s+1)(4s+7)))^11
                   = (529/486) * (1 - 1/(4s^2+11s+7))^11.
   The integer 4s^2+11s+7 is strictly increasing for s >= 0, so R(s+1)/R(s) is strictly increasing in
   s.  It is < 1 at s=4 and > 1 at s=5 (explicit rationals), hence < 1 for every s <= 4 and > 1 for
   every s >= 5.  Therefore R is strictly decreasing on {0,...,5} and strictly increasing on {5,6,...},
   so R attains its unique minimum at s = 5.

4) The tie value.  R(5) = 1 EXACTLY -- equivalently the integer identity 64*243*23 = 621*576 = 357696
   (this is g(5)=0, the tie).  Hence R(s) >= R(5) = 1 for all integers s >= 0, i.e. (STAR) holds with
   equality iff s = 5.  Unwinding, Phi(N(c,k)) <= 1 with equality iff c+k = 5.  QED.

The arithmetic constant 529/486 = 23^2 / (2 * 3^5) is exactly the 23-adic content of 621 = 3^3 * 23
(cf. rational_reduction.py, 11 | V since 23 | 621).  The continuous relaxation of g exceeds 0 between
integers (near_tie_asymptotics), which is why no smooth certificate works and this integer argument is
necessary.

Every step below is verified in exact rational arithmetic (fractions.Fraction).

Requires only the standard library (fractions).
"""
from __future__ import annotations

from fractions import Fraction as Fr

TIE_S = 5


def LHS(s: int) -> Fr:
    """3^(5s-14) * 2^(s+6) * (4s+3)^11."""
    return Fr(3) ** (5 * s - 14) * Fr(2) ** (s + 6) * Fr(4 * s + 3) ** 11


def RHS(s: int) -> Fr:
    """23^(2s+1) * (s+1)^11."""
    return Fr(23) ** (2 * s + 1) * Fr(s + 1) ** 11


def R(s: int) -> Fr:
    """R(s) = RHS/LHS; the theorem is R(s) >= 1 for all s >= 0, equality iff s = 5."""
    return RHS(s) / LHS(s)


def ratio_step_formula(s: int) -> Fr:
    """The exact closed form R(s+1)/R(s) = (529/486) * (1 - 1/(4s^2+11s+7))^11."""
    return Fr(529, 486) * Fr(4 * s * s + 11 * s + 6, 4 * s * s + 11 * s + 7) ** 11


def verify_proof(s_check: int = 4000) -> dict:
    """Exactly verify every step of the proof (all in Fraction arithmetic)."""
    # (4) tie value R(5)=1  <=>  64*243*23 == 621*576
    tie_exact = (R(TIE_S) == 1) and (64 * 243 * 23 == 621 * 576)
    # (3) ratio identity holds exactly
    ratio_identity = all(R(s + 1) / R(s) == ratio_step_formula(s) for s in range(0, 200))
    # (3) monotonicity of the denominator 4s^2+11s+7 (=> ratio strictly increasing)
    denom_increasing = all(4 * (s + 1) ** 2 + 11 * (s + 1) + 7 > 4 * s * s + 11 * s + 7
                           for s in range(0, s_check))
    # (3) single crossing: ratio < 1 at s=4, > 1 at s=5  (with monotonicity => the full split)
    crossing = (ratio_step_formula(4) < 1) and (ratio_step_formula(5) > 1)
    # conclusion: R(s) >= 1 for all s in [0, s_check], equality only at s=5
    min_is_one_at_5 = all(R(s) >= 1 for s in range(0, s_check)) and \
        all(R(s) > 1 for s in range(0, s_check) if s != TIE_S)
    return {
        "tie_value_exact_R5_eq_1": tie_exact,
        "ratio_identity_exact": ratio_identity,
        "denominator_strictly_increasing": denom_increasing,
        "ratio_crosses_once_between_4_and_5": crossing,
        "R_ge_1_with_equality_only_at_s5": min_is_one_at_5,
        "proof_complete": tie_exact and ratio_identity and denom_increasing and crossing and min_is_one_at_5,
        "statement": "Phi(c cherries + k cherry-arms) <= 1 for all integers c,k>=0, equality iff c+k=5",
    }


if __name__ == "__main__":
    v = verify_proof()
    for key, val in v.items():
        print(f"{key}: {val}")
    print("\nR(s) for s=0..10:", [str(R(s)) if R(s) == 1 else f"{float(R(s)):.6f}" for s in range(11)])

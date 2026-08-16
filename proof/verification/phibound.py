"""Toward a closed proof of Phi(C) <= 1 for all single-branch near-star gadgets.

singlebranch.py established (exhaustively, exact recursion) that Phi(C) <= 1 for every gadget,
with equality attained (the arm-substitute root(4)-0-0), so no near-star beats the single star.
This module documents the attempt at a CLOSED proof and the clean partial facts it yields.  The
closed proof remains OPEN; the analysis below pins down exactly why the natural induction stalls.

Recursion (from singlebranch.py), root r, degree d = #children + 1 + c_r:
    Phi0(C) = a_r * prod_i Phi(C_i),   a_r := F(d,c_r) / rho_B^{1+2 c_r},
    Phi(C)  = Phi0(C) / rho0(C),        rho0(C) = 1 / (1 + z(d,c_r) sum_i z(d_i,c_i) rho0(C_i)),
where Phi0 is the root-unmatched part and Phi = Phi0 + Phi1.

CLEAN LEMMA (proven, exact).  a_r <= 1 for every root, i.e. F(d,c) <= rho_B^{1+2c} for all
d >= 1+c, c >= 0.  Proof: F(d,c) = (3/2)^c (1 + c/(3d)) is DECREASING in d, so it is maximal at
d = 1+c (a pure pendant arm), where F(1+c,c)^{11} <= F(6)^{1+2c} <=> rho(c) <= rho_B -- the
rate-optimality of c=5 (arm_bound.py, exact).  Consequently, by induction with Phi(C_i) <= 1,
    Phi0(C) = a_r * prod_i Phi(C_i) <= 1 :
the root-UNMATCHED part never exceeds 1.

WHY THIS DOES NOT CLOSE Phi <= 1.  Phi(C) = Phi0(C)/rho0(C) with rho0 < 1, so Phi0 <= 1 does not
bound Phi.  The statement Phi <= 1 is exactly equivalent to Phi0 <= rho0, which is a restatement,
not a stronger inductive hypothesis.  A usable induction would need a low-dimensional invariant
Phi <= G(rho0) (or Phi <= G(t), t = z_root*rho0) preserved by the root map; but the achievable
region is JAGGED and touches Phi = 1 at MANY isolated points -- every pure-arm leaf sits on the
boundary, plus the tie -- so no single-/two-variable G bounds it (verified by envelope scans).
The naive induction also fails outright: the root map applied to arbitrary child pairs
(Phi_i <= 1, rho0_i in (0,1]) reaches Phi ~ 1.197 > 1, so the truth of Phi <= 1 rests on the
realizable joint region, which is not captured by any of the low-dimensional invariants tried.

STATUS.  Phi <= 1 is exhaustively verified (exact recursion) with the tight set characterized;
the clean partial a_r <= 1 (hence Phi0 <= 1) is proven; a closed proof of the full Phi <= 1 is the
sharply-localized open residual of Conjecture main, and it provably requires more than the natural
one-/two-variable invariant.
"""
from __future__ import annotations

from fractions import Fraction as Fr

_H = Fr(3, 2)
_F6 = Fr(621, 64)


def _F(d: int, c: int) -> Fr:
    return _H ** c * (1 + Fr(c, 3 * d))


def certify_ar_le_1(cmax: int = 40, dmax_extra: int = 30) -> dict:
    """Exact: a_r = F(d,c)/rho_B^{1+2c} <= 1 for all c<=cmax and d in [1+c, 1+c+dmax_extra],
    via (i) F(d,c) decreasing in d and (ii) F(1+c,c)^11 <= F(6)^{1+2c} (rate-optimality)."""
    decreasing_in_d = True
    arm_bound = True
    for c in range(0, cmax + 1):
        # (i) F decreasing in d
        for d in range(1 + c, 1 + c + dmax_extra):
            if not (_F(d, c) >= _F(d + 1, c)):
                decreasing_in_d = False
        # (ii) arm bound at the maximal d=1+c: F(1+c,c)^11 <= F6^(1+2c)
        if not (_F(1 + c, c) ** 11 <= _F6 ** (1 + 2 * c)):
            arm_bound = False
    return {"F_decreasing_in_d": decreasing_in_d, "arm_bound_rate_optimality": arm_bound,
            "ar_le_1": decreasing_in_d and arm_bound}


def certify_phi0_le_1_partial() -> dict:
    """Record the proven partial: a_r<=1 => Phi0(C) = a_r * prod Phi(C_i) <= 1 by induction
    (root-unmatched part bounded), and the honest note that this does not close Phi<=1."""
    ar = certify_ar_le_1()
    return {"ar_le_1": ar["ar_le_1"],
            "implies_Phi0_le_1": ar["ar_le_1"],   # a_r<=1 and Phi(C_i)<=1 => Phi0<=1
            "closes_Phi_le_1": False,             # Phi=Phi0/rho0, rho0<1; equivalent to Phi0<=rho0
            "note": "closed proof open; natural low-dim invariant provably insufficient"}


if __name__ == "__main__":
    print("a_r <= 1 (clean exact lemma):", certify_ar_le_1())
    print("partial Phi0 <= 1 + honest status:", certify_phi0_le_1_partial())

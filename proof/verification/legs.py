"""Conjecture Piece 1 -- "why cherries": among all pendant-leg lengths, length-2
(cherries) uniquely maximizes the star growth rate.

A "star of legged bundles" attaches, to a hub, arm-centers each carrying c pendant
paths ("legs") of a common length ell. Adding one such arm multiplies pi by the arm
growth base
    F_ell(1+c) = phi_ell^c  +  (c / (2(1+c) delta_ell)) * phi_{ell-1} * phi_ell^{c-1},
where phi_ell is the length-ell leg matching factor (phi_1=1, phi_2=3/2, and
phi_ell = phi_{ell-1} + (1/4) phi_{ell-2} for ell>=3), and delta_ell = deg of the
leg's first vertex (= 2 for ell>=2, = 1 for ell=1). The arm uses 1+c*ell vertices, so
the per-vertex growth rate of the best ell-legged star is
    rho_ell = sup_c F_ell(1+c)^{1/(1+c ell)}.

Theorem (cherries optimal).  rho_2 = (621/64)^{1/11} = rho_B (attained at c=5), and
rho_ell < rho_B for EVERY ell != 2.  Hence a star whose legs are not length-2 grows
strictly slower and is beaten, for all large n, by a cherry-bundle star. This is the
"length-2 legs" (cherry) necessary condition of the star-of-cherry-bundles conjecture,
proven at the growth-rate (gadget) level.

Proof (exact, machine-checked in certify_cherries_optimal):
* ell = 1:  F_1(1+c) = (1+2c)/(1+c) < 2, so F_1^{11} < 2^{11} = 2048 < (621/64)^{1+c}
  for c >= 4; c = 1,2,3 are exact rational checks.
* ell >= 3:  rho_ell(c) < beta * (3/2)^{1/(1+c ell)} with beta = 483/400, using
  F_ell(1+c) < (3/2) phi_ell^c and phi_ell <= beta^ell (induction: beta^2 >= beta+1/4,
  and phi_3 <= beta^3, phi_4 <= beta^4). Two regimes:
    - tail c*ell >= 22:  beta*(3/2)^{1/(1+c ell)} <= beta*(3/2)^{1/23} < rho_B, i.e.
      beta^{253} (3/2)^{11} < (621/64)^{23}  (exact);
    - finite c*ell <= 21 (finitely many (ell,c), 3<=ell<=21):
      F_ell(1+c)^{11} < (621/64)^{1+c ell}  (exact).

Honest scope: this is a GADGET-level (growth-rate) statement about the star-of-legs
family -- one of the three necessary conditions of the conjecture (legs are cherries).
It does NOT prove the full conjecture, which also needs "the backbone is a star among
ALL backbones" (open) and global-max rigor. See RESULT_LAPLACIAN_RATIO.md.
"""
from __future__ import annotations

from fractions import Fraction as Fr

RHO_B_11 = Fr(621, 64)     # rho_B^{11} = F_2(1+5); the cherry-star rate to beat
_BETA = Fr(483, 400)       # phi_ell <= beta^ell for ell >= 3


def phi(ell: int) -> Fr:
    """Leg matching factor: phi_1=1, phi_2=3/2, phi_ell = phi_{ell-1}+phi_{ell-2}/4."""
    if ell <= 1:
        return Fr(1)
    a, b = Fr(1), Fr(3, 2)          # phi_1, phi_2
    for _ in range(3, ell + 1):
        a, b = b, b + Fr(1, 4) * a
    return b


def arm_base(ell: int, c: int) -> Fr:
    """F_ell(1+c): factor by which pi multiplies when adding one ell-legged arm-center."""
    d = 1 + c
    delta = 1 if ell == 1 else 2
    return phi(ell) ** c + c * Fr(1, d * delta) * phi(ell - 1) * phi(ell) ** (c - 1)


def certify_cherries_optimal() -> bool:
    """Prove rho_ell < rho_B for every ell != 2 (so length-2 legs are optimal).

    Exact, root-free. Returns True iff every regime below holds.
    """
    RB = RHO_B_11
    beta = _BETA

    # ell = 2 is the reference: rho_2 = rho_B, attained at c = 5.
    if arm_base(2, 5) != RB:
        return False

    # ell = 1: c=1,2,3 exact; c>=4 via F_1(1+c) < 2 => F_1^11 < 2048 < (621/64)^{1+c}.
    ell1 = all(arm_base(1, c) ** 11 < RB ** (1 + c) for c in (1, 2, 3)) and (2 ** 11 < RB ** 5)
    if not ell1:
        return False

    # ell >= 3 induction: phi_ell <= beta^ell.
    if not (beta ** 2 >= beta + Fr(1, 4) and phi(3) <= beta ** 3 and phi(4) <= beta ** 4):
        return False

    # ell >= 3 tail (c*ell >= 22): beta*(3/2)^{1/(1+c ell)} < rho_B  <=  the fixed exact:
    if not (beta ** 253 * Fr(3, 2) ** 11 < RB ** 23):
        return False

    # ell >= 3 finite region (c*ell <= 21): exact per (ell, c).
    for ell in range(3, 22):
        for c in range(1, 21 // ell + 1):
            if arm_base(ell, c) ** 11 >= RB ** (1 + c * ell):
                return False
    return True

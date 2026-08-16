"""Probe: the cherry-bush family B(c,k,t) -- exact arithmetic form, and WHY the near-star method does not
extend to it (non-monotone in k), plus a concrete demonstration that the finite-reduction margins are
entangled (a depth bound alone does not give a per-node sign).

This records an HONEST NEGATIVE from an attempt to extend the near-star arithmetic proof
(near_star_arithmetic_proof.py) to the depth-2 branching-tail maximiser
    B(c,k,t) = root with c cherries and k children, each child a t-cherry LEAF (t,[]),
which BushBound.lean proves only CONDITIONALLY (the per-node hypothesis eroot <= -k*gVal(t)).

RESULT 1 -- the exact rational form BUSH-STAR (k>=1).  logPhi(B(c,k,t)) <= 0  <=>  (raise to the 11th,
rho_B^11 = 621/64 = 3^3*23/2^6)
    3^(11P) * 2^(6Q) * N^11  <=  2^(11P) * 3^(3Q) * 23^Q * D^11,
    P = k*t + c,   Q = 1 + 2c + k + 2kt,
    N = (4t+3)^(k-1) * ( (3k+3+4c)(4t+3) + 9k ),
    D = 3^(k+1) * (t+1)^k * (k+1+c).
This is a pure rational inequality in three integers; `bushstar_holds` checks it exactly, and
`equiv_check` confirms it is EXACTLY equivalent to logPhi(B)<=0 against the ground-truth matching-polynomial
value (general_children_crux.log_phi).  It holds everywhere tested, with max logPhi = omega = logPhi(ARM) =
-0.00770726 at the ARM B(0,1,0), and NO exact ties for k>=1 (the family is bounded away from the tie 0).

RESULT 2 -- WHY near-star's method does not extend.  The near-star proof works because logPhi(N(c,k)) = g(s)
collapses to ONE variable s=c+k and R(s)=RHS/LHS is unimodal.  The cherry-bush does NOT collapse: it is a
genuine 3-parameter family and, crucially, logPhi(B(c,k,t)) is NON-MONOTONE in k (`k_nonmonotone` exhibits
e.g. logPhi(0,1,2) = -0.1001 < logPhi(0,2,2) = -0.0822).  So neither a 1-D unimodal reduction nor a
"reduce to k=1" monotonicity argument applies; a genuinely multivariate integer argument is required.
(The t=5 tie-children slice and the near-star-children slices also overlap already-proven results.)

RESULT 3 -- the finite-reduction margins are ENTANGLED (confirms the near_zero_closure.py "degree bound is
crux-entangled" negative).  `margin_entanglement` shows the per-node increment e_root of a node with k
children all at the chain-attractor cavity 3/7 is <=0 for k=1 but OVERSHOOTS >0 for k>=2.  So a DEPTH bound
(which controls child cavities into [1/3,3/7]) does NOT by itself yield a per-node sign -- depth and width are
coupled, and no single one of the three margins (D/W/C) is closable in isolation.

CONCLUSION: the crux (Phi<=1 for general branching) remains OPEN.  This module is an honest negative + the
exact BUSH-STAR target for anyone attempting the cherry-bush with a multivariate method.  conjecture1_proved
= False.

Every check below is exact (fractions.Fraction) or against the ground-truth matching-polynomial log_phi.
Requires general_children_crux (hence rational_reduction).
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

import general_children_crux as GC

_L = math.log(621 / 64) / 11
ARM = (0, [(0, [])])


def bush(c: int, k: int, t: int):
    """B(c,k,t) = root with c cherries and k children, each a t-cherry leaf (t,[])."""
    return (c, [(t, [])] * k)


def bushstar_holds(c: int, k: int, t: int) -> tuple[bool, bool]:
    """(holds, is_equality) for the exact rational inequality BUSH-STAR (requires k>=1)."""
    assert k >= 1
    P = k * t + c
    Q = 1 + 2 * c + k + 2 * k * t
    N = (4 * t + 3) ** (k - 1) * ((3 * k + 3 + 4 * c) * (4 * t + 3) + 9 * k)
    D = 3 ** (k + 1) * (t + 1) ** k * (k + 1 + c)
    LHS = 3 ** (11 * P) * 2 ** (6 * Q) * N ** 11
    RHS = 2 ** (11 * P) * 3 ** (3 * Q) * 23 ** Q * D ** 11
    return LHS <= RHS, LHS == RHS


def equiv_check(crange: int = 15, krange: int = 15, trange: int = 15) -> dict:
    """BUSH-STAR holds AND is exactly equivalent to logPhi(B)<=0 (ground truth)."""
    bad = mism = ties = 0
    for c in range(crange):
        for k in range(1, krange):
            for t in range(trange):
                holds, eq = bushstar_holds(c, k, t)
                if not holds:
                    bad += 1
                if eq:
                    ties += 1
                if holds != (GC.log_phi(bush(c, k, t)) <= 1e-12):
                    mism += 1
    return {"bushstar_all_hold": bad == 0, "exact_ties_k>=1": ties,
            "equivalent_to_logphi_le_0": mism == 0}


def k_nonmonotone(crange: int = 30, krange: int = 30, trange: int = 30) -> dict:
    """logPhi(B) is NON-monotone in k -- the obstruction to a 1-D reduction."""
    viol = 0
    witness = None
    for c in range(crange):
        for t in range(trange):
            for k in range(1, krange):
                a, b = GC.log_phi(bush(c, k, t)), GC.log_phi(bush(c, k + 1, t))
                if b > a + 1e-15:
                    viol += 1
                    if witness is None:
                        witness = {"c": c, "t": t, "k": k,
                                   "logPhi_k": round(a, 6), "logPhi_k+1": round(b, 6)}
    omega = GC.log_phi(ARM)
    return {"k_nonmonotone_violations": viol, "witness": witness,
            "max_is_ARM_omega": round(omega, 8)}


def margin_entanglement() -> dict:
    """Per-node e_root(c=0, k children each at chain-attractor cavity 3/7): <=0 at k=1, OVERSHOOTS for k>=2.
    So a depth bound (cavity<=3/7) alone gives no per-node sign -- depth and width are coupled."""
    def eroot(c: int, child_cavs) -> float:
        nch = len(child_cavs)
        d = nch + 1 + c
        z = 3 / (3 * d + c)
        a = (1.5) ** c * (1 + c / (3 * d)) / (621 / 64) ** ((1 + 2 * c) / 11)
        return math.log(a * (1 + z * sum(child_cavs)))
    rows = {k: round(eroot(0, [Fr(3, 7)] * k), 6) for k in (1, 2, 3, 5, 10)}
    return {"eroot_c0_k_children_cav_3over7": rows,
            "depth_bound_alone_gives_per_node_sign": all(v <= 0 for v in rows.values())}


def probe() -> dict:
    return {"result1_exact_form": equiv_check(),
            "result2_k_nonmonotone": k_nonmonotone(),
            "result3_margins_entangled": margin_entanglement(),
            "conjecture1_proved": False}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), indent=2, default=str))

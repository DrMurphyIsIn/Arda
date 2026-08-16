"""Extending the near-star arithmetic proof toward the arbitrary-children crux (2026-08-07).

(Contributed by a parallel session on branch experiment/lr-fischer-decay, 2026-08-07;
verified and consolidated onto main.)

near_star_arithmetic_proof.py proved Phi(N(c,k)) <= 1 for the 1-parameter near-star family
(s = c+k), the crux's marginal slice, via an exact integer ratio.  This module pushes that arithmetic
route into the general (branching) case.  It contributes ONE proven new theorem, the structural
picture that motivates it, and an honest statement of the two ingredients still missing.

================================================================================================
A. CLEANER AMPLITUDE + THE CATERPILLAR COLLAPSE  (verified, exact)
================================================================================================
Per-vertex the log(3d+c) terms cancel, giving  log Phi = sum_v [ c_v log(3/2) - (1+2c_v) log rho_B
- log m_v - log d_v ],  m_v = 3/t_v,  t_v = 3 d_v + c_v + 3 S_v,  S_v = sum_children m.

The reason the near-star collapses to s=c+k is that a CHERRY and an ARM (=(0,[(0,[])])) are
amplitude-equivalent: each contributes exactly log(3/2) - 2 log rho_B to log Phi and exactly 4 to t.
This makes any CATERPILLAR (a spine whose nodes each carry s_i = c_i+k_i cherry/arm units plus one
spine child) collapse to a 1-D integer recursion in the s_i (verified to 1e-15):
    tip:      m_L = 3/(4 s_L + 3)
    i < L:    m_i = 3/(4 s_i + 6 + 3 m_{i+1})
    log Phi = sum_i [ s_i log(3/2) - (1+2 s_i) log rho_B - log m_i - log(s_i + 2 - [i=L]) ].
Numerically the caterpillar value function psi_cat(m) <= 0 with equality ONLY at the tip s=5
(m=3/23); every caterpillar with spine length L>=1 has log Phi <= -0.0145 (uniform slack).

================================================================================================
B. THE PROVEN NEW THEOREM: the tie-children inequality (2-variable extension of near-star)
================================================================================================
The general induction's MARGINAL worst configuration is a node carrying s = c+k cherry/arm units
and j deep children that are EXACT ties (each cavity 3/23, amplitude 0).  Its amplitude <= 0 is,
after clearing the 11th root (rho_B^11 = 621/64),

    2^(s+6) 3^(5s-14) (92 s + 69 + 78 j)^11  <=  23^(12+2s) (s + j + 1)^11        (TIE-CHILDREN)

for all integers s,j >= 0.  Note 92s+69 = 23(4s+3); at j=0 this is exactly the near-star (STAR)
inequality.  THEOREM (this module, exact-Fraction verified): (TIE-CHILDREN) holds for all s,j>=0,
with equality iff (s,j) = (5,0) (the global tie N(0,5)).

PROOF.  Let R(s,j) = RHS/LHS.  A direct computation gives the exact ratio
    R(s,j+1)/R(s,j) = ( (s+j+2)(92s+69+78j) / ((s+j+1)(92s+147+78j)) )^11,
and the inner numerator minus denominator equals  14 s - 9,  INDEPENDENT of j.  Hence:
  * s >= 1:  14s-9 > 0  =>  R strictly increasing in j  =>  R(s,j) >= R(s,0), and R(s,0) >= 1 is the
    near-star (STAR) theorem (near_star_arithmetic_proof), equality iff s=5.  So on s>=1 equality
    only at (5,0).
  * s = 0:  14s-9 = -9 < 0  =>  R(0,j) strictly DECREASING in j, with exact limit
        R(0, inf) = 23^12 * 27 / (64 * 26^11) = 2.5189... > 1   (integer fact 23^12*27 > 64*26^11),
    so R(0,j) > 1 for every j (no equality).
QED.  The pivot 14s-9 is the exact 2-variable analogue of the near-star unimodality crossing.

================================================================================================
C. STRUCTURE OF THE MAXIMIZER  (numerical, strong -- motivates the finish)
================================================================================================
A correct multi-child value iteration for the FULL tree value function Psi(m) converges in ~5 steps
to Psi <= 0 with a single maximum = 0 at m = 3/23 (the tie).  Two structural facts (numerical):
  * DEPTH GAP: every rooted tree of depth >= 4 has log Phi <= -0.0145 < 0 (nested ties cost a
    near-constant ~0.019 per extra level).  So the maximizer has depth <= 3; the cavity accumulation
    at 3/23 does NOT make log Phi accumulate at 0.
  * BRANCHING is real: at non-tie cavities the extremal tree has 2-4 deep children, so the pure 1-D
    caterpillar family is NOT extremal -- the general Psi genuinely needs the multi-child recursion.

================================================================================================
D. WHAT REMAINS OPEN (honest)
================================================================================================
(TIE-CHILDREN) is NECESSARY but not SUFFICIENT for the induction: the true worst-case deep child sits
slightly ABOVE the tie cavity (at mu* where Psi'(mu*) = -3/t, since Psi has a quadratic max at 3/23),
not exactly at it, and the off-tie correction is O(1/t^2) -- the same marginal residual (+0.0006) that
defeats every fixed-complexity certificate, now localized to this exact competition.  A full proof
needs EITHER (i) a rigorous depth gap (depth>=4 => log Phi <= -delta, numerically true) plus a finite
depth-<=3 check, OR (ii) control of the off-tie correction against the tie-children slack.  Neither is
proven here.  Phi<=1 for arbitrary children remains OPEN; this module extends the arithmetic route by
one genuine 2-variable theorem and pins the residual precisely.

Requires numpy (structure checks) and fractions (the exact theorem).
"""
from __future__ import annotations

from fractions import Fraction as Fr

import numpy as np

_rhoB = (621 / 64) ** (1 / 11)
_L = np.log(_rhoB)
ARM = (0, [(0, [])])


# ---- amplitude (matches cavity_potential.cavity_and_logphi) -----------------------------------
def amp(T):
    """(cavity m, log Phi) for rooted tree T = (cherries, [children])."""
    c, kids = T
    ch = [amp(k) for k in kids]
    S = sum(m for m, _ in ch)
    d = len(kids) + 1 + c
    t = 3 * d + c + 3 * S
    return 3 / t, c * np.log(1.5) - (1 + 2 * c) * _L + np.log(t) - np.log(3 * d) + sum(lp for _, lp in ch)


def caterpillar_closed(svals):
    """1-D collapse: log Phi of a caterpillar from its integer unit-sequence svals (tip -> root)."""
    m = None
    total = 0.0
    Ln = len(svals) - 1
    for i, s in enumerate(svals):
        if i == 0:
            t = 4 * s + 3
            deg = s + 1
        else:
            t = 4 * s + 6 + 3 * m
            deg = s + 2
        m = 3.0 / t
        total += s * np.log(1.5) - (1 + 2 * s) * _L - np.log(m) - np.log(deg)
    return total


def verify_caterpillar_collapse(trials=2000, seed=0):
    """The caterpillar amplitude depends only on the s_i (any cherry/arm split), matching amp()."""
    import random
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        sv = [rng.randint(0, 7) for _ in range(rng.randint(1, 6))]
        # build a concrete caterpillar with an arbitrary cherry/arm split at each level
        node = None
        for i, s in enumerate(sv):
            c = rng.randint(0, s)
            kids = [ARM] * (s - c) + ([node] if node is not None else [])
            node = (c, kids)
        worst = max(worst, abs(amp(node)[1] - caterpillar_closed(sv)))
    return {"max_error": worst, "collapse_holds": worst < 1e-9}


# ---- the proven theorem -----------------------------------------------------------------------
def _LHS(s, j):
    return Fr(2) ** (s + 6) * Fr(3) ** (5 * s - 14) * Fr(92 * s + 69 + 78 * j) ** 11


def _RHS(s, j):
    return Fr(23) ** (12 + 2 * s) * Fr(s + j + 1) ** 11


def R(s, j):
    """R(s,j) = RHS/LHS of (TIE-CHILDREN); theorem: R >= 1, equality iff (s,j) = (5,0)."""
    return _RHS(s, j) / _LHS(s, j)


def verify_tie_children_theorem(smax=250, jmax=250):
    """Every step of the proof, in exact rational arithmetic."""
    # ratio closed form + the pivot (14s-9), independent of j
    pivot_ok = all((s + j + 2) * (92 * s + 69 + 78 * j) - (s + j + 1) * (92 * s + 147 + 78 * j) == 14 * s - 9
                   for s in range(60) for j in range(60))
    ratio_ok = all(R(s, j + 1) / R(s, j)
                   == Fr((s + j + 2) * (92 * s + 69 + 78 * j), (s + j + 1) * (92 * s + 147 + 78 * j)) ** 11
                   for s in range(40) for j in range(40))
    # s=0 exact limit 23^12 * 27 / (64 * 26^11) > 1
    s0_limit = Fr(23) ** 12 * 27 / (Fr(64) * Fr(26) ** 11)
    s0_decreasing = all(R(0, j + 1) < R(0, j) for j in range(jmax))
    # global: R >= 1 on the box, equality only (5,0)
    eq_pts = [(s, j) for s in range(smax) for j in range(jmax) if R(s, j) == 1]
    all_ge_1 = all(R(s, j) >= 1 for s in range(smax) for j in range(jmax))
    return {
        "pivot_is_14s_minus_9": pivot_ok,
        "ratio_closed_form_exact": ratio_ok,
        "s0_limit_gt_1": s0_limit > 1,
        "s0_limit_value": float(s0_limit),
        "s0_strictly_decreasing": s0_decreasing,
        "all_ge_1_on_box": all_ge_1,
        "unique_equality_point": eq_pts,
        "theorem_verified": pivot_ok and ratio_ok and s0_limit > 1 and s0_decreasing
        and all_ge_1 and eq_pts == [(5, 0)],
    }


def certify():
    cat = verify_caterpillar_collapse()
    thm = verify_tie_children_theorem()
    return {
        "caterpillar_collapse_verified": cat["collapse_holds"],
        "tie_children_theorem_verified": thm["theorem_verified"],
        "tie_children_unique_equality": thm["unique_equality_point"],
        "s0_limit": thm["s0_limit_value"],
        "full_arbitrary_children_crux_closed": False,   # off-tie correction / depth gap unproven
    }


if __name__ == "__main__":
    import json
    print(json.dumps(certify(), indent=2, default=float))
    print("\ntie-children theorem detail:", json.dumps(verify_tie_children_theorem(), indent=2, default=float))

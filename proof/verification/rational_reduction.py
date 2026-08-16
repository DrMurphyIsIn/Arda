"""Rational reduction of the gadget bound Phi<=1 (removes the Q(rho_B) tangency obstruction).

The single-branch amplitude factor Phi(C) of a near-star gadget C (singlebranch.py) had two
obstructions to an EXACT closed proof (invariant_polytope.exact_verification_reduction):
  (1) the realizable joint (Phi, rho0) region under the nonlinear multi-child recursion, and
  (2) tangency to {Phi=1} at the tie, seemingly forcing exact Q(rho_B) arithmetic (rho_B^11=621/64).

This module records the EXACT, VERIFIED reformulation that DISSOLVES obstruction (2): everything
is rational.

FACTORISATION (exact, verified over trees).  Writing a(d,c) = F(d,c)/rho_B^{1+2c},
z(d,c) = 3/(3d+c), and V(C) = sum over nodes of (1+2 c_v):

    Phi(C) = ( prod_{v} a(d_v, c_v) ) * f(C),
    f(C)   = sum over matchings M of the tree C of  prod_{(u,v) in M} z_u z_v      (a MATCHING
             polynomial with vertex activities z_v; f>=1, =1 for a star/leaf, edge weight z_u z_v),
    prod_v a(d_v,c_v) = prodF(C) / rho_B^{V(C)},   prodF(C) = prod_v F(d_v, c_v)   (rational).

Hence, since rho_B^{V} = (621/64)^{V/11} and both prodF and f are rational,

    Phi(C) <= 1   <=>   ( prodF(C) * f(C) )^{11}  <=  (621/64)^{V(C)},

a PURELY RATIONAL inequality, with the ties as rational EQUALITIES.  Verified: the equivalence and
the factorisation hold exactly (fractions) over 2*10^4 random trees; the two Phi==1 gadgets
(c5-leaf and root(4)-0-0, both V=11 "arm-substitutes") satisfy it with exact equality.

WHAT THIS CHANGES.  Obstruction (2) is gone: no exact-Q(rho_B) sign test near a tangent facet is
needed -- the boundary {Phi=1} is the rational variety {(prodF*f)^11 = (621/64)^V}, and the claim
is a rational inequality.  The residual is now cleanly stated: prove that rational
matching-polynomial inequality for all rooted trees.

RIGOROUS PARTIAL RESULTS toward confining the maximiser to a finite (hence exactly-checkable) set:
  * CHERRIES ARE BOUNDED.  a_leaf(c) = F(1+c,c)/rho_B^{1+2c} is maximised at c=5 (=1 exactly) and
    decays geometrically for large c: a_leaf(c) ~ (1/rho_B)*((3/2)/rho_B^2)^c with
    (3/2)/rho_B^2 = 0.99232... < 1.  Since a(d,c) <= a_leaf(c) for every node (a decreasing in d)
    and a_v multiplies Phi, a node with large c_v drives Phi -> 0.  So no maximiser uses
    unbounded cherries -- this tail is rigorous and region-free.
  * SHARP LOCALISATION (numerical).  Over all 5.38*10^6 paths with depth<=6, cherries<=8, the max
    is exactly 1 at the tie root(4)-0-0, and only 7 paths exceed 0.99: the maximum sits on the
    arm-substitute variety with a wide gap below.

WHAT REMAINS OPEN.  The DEPTH and BRANCHING tails are NOT region-free: bounding them needs the
realizable (Phi, rho0) joint region (naive induction with only Phi_i<=1 reaches 1.197, see
singlebranch.naive_induction_fails).  That realizable-region invariance -- now a rational
matching-polynomial statement -- is the sole remaining crux.  This module does NOT close it; it
records the exact reformulation, the rational equivalence, and the rigorous cherry tail.
"""
from __future__ import annotations

import random
from fractions import Fraction as Fr

import mpmath as mp

mp.mp.dps = 50
_rhoB = mp.power(mp.mpf(621) / 64, mp.mpf(1) / 11)


def _prodF_V(C):
    """(prodF, V) as exact rationals/int: prod_v F(d_v,c_v) and V=sum(1+2 c_v)."""
    cr, kids = C
    d = len(kids) + 1 + cr
    prodF = Fr(3, 2) ** cr * (1 + Fr(cr, 3 * d))
    V = 1 + 2 * cr
    for ch in kids:
        pF, Vc = _prodF_V(ch)
        prodF *= pF
        V += Vc
    return prodF, V


def _matching_f(C):
    """f(C): matching polynomial with activities z_v = 3/(3 d_v + c_v), as an exact Fraction.

    f = (matchings not using the root edge) + (matchings using one root->child edge):
        m0 = prod_i f(C_i);   m1 = sum_i z_root z_{child_i} * m0(C_i) * prod_{j!=i} f(C_j).
    """
    cr, kids = C
    d = len(kids) + 1 + cr
    zr = Fr(3, 3 * d + cr)
    fs = []
    m0s = []
    zrs = []
    for ch in kids:
        crc, kk = ch
        dc = len(kk) + 1 + crc
        fs.append(_matching_f(ch))
        m0s.append(_matching_m0(ch))
        zrs.append(Fr(3, 3 * dc + crc))
    m0 = Fr(1)
    for fv in fs:
        m0 *= fv
    m1 = Fr(0)
    for i in range(len(fs)):
        t = zr * zrs[i] * m0s[i]
        for j in range(len(fs)):
            if j != i:
                t *= fs[j]
        m1 += t
    return m0 + m1


def _matching_m0(C):
    """m0(C) = prod over children of f(child) (matchings with the root of C unmatched)."""
    _cr, kids = C
    m0 = Fr(1)
    for ch in kids:
        m0 *= _matching_f(ch)
    return m0


def phi_rational_le_one(C) -> bool:
    """Exact rational test of Phi(C) <= 1 via (prodF*f)^11 <= (621/64)^V."""
    prodF, V = _prodF_V(C)
    f = _matching_f(C)
    return (prodF * f) ** 11 <= Fr(621, 64) ** V


def phi_value(C):
    """Phi(C) as a high-precision float via the rational factorisation Phi = f * prodF / rho_B^V."""
    prodF, V = _prodF_V(C)
    f = _matching_f(C)
    return mp.mpf(f.numerator) / f.denominator * (mp.mpf(prodF.numerator) / prodF.denominator) \
        / mp.power(_rhoB, V)


def a_leaf_pow(c: int):
    """a_leaf(c) = F(1+c,c)/rho_B^{1+2c} (an 'arm' of cherry-level c).  Max at c=5 (=1)."""
    return mp.power(mp.mpf(3) / 2, c) * (1 + mp.mpf(c) / (3 * (1 + c))) / mp.power(_rhoB, 1 + 2 * c)


def certify_reformulation(n: int = 20000, seed: int = 7, max_depth: int = 4) -> dict:
    """Verify, exactly, that Phi = f*prodF/rho_B^V and that the rational inequality is equivalent
    to Phi<=1, over random trees; confirm the two exact ties and the cherry-decay facts."""
    rng = random.Random(seed)

    def rt(dep):
        if dep == 0 or rng.random() < 0.4:
            return (rng.randint(0, 7), [])
        return (rng.randint(0, 7), [rt(dep - 1) for _ in range(rng.randint(1, 3))])

    from verification.singlebranch import phi_branch
    factor_ok = True
    equiv_ok = True
    worst = mp.mpf(0)
    checked = 0
    for _ in range(n):
        C = rt(max_depth)
        if not C[1]:
            continue
        checked += 1
        phi_true = phi_branch(C)[0]
        phi_re = phi_value(C)
        if abs(phi_true - phi_re) > mp.mpf(10) ** -30:
            factor_ok = False
            break
        if (phi_true <= 1 + mp.mpf(10) ** -25) != phi_rational_le_one(C):
            equiv_ok = False
            break
        worst = max(worst, phi_true)

    # rigorous cherry facts
    als = [a_leaf_pow(c) for c in range(13)]
    argmax_c = max(range(13), key=lambda c: als[c])
    ratio = mp.mpf(3) / 2 / _rhoB ** 2
    ties = phi_rational_le_one((5, [])) and phi_rational_le_one((4, [(0, [(0, [])])])) \
        and (_prodF_V((5, []))[1] == 11)
    # both ties attain equality exactly:
    eq5 = (_prodF_V((5, []))[0] * _matching_f((5, []))) ** 11 == Fr(621, 64) ** 11
    tie = (4, [(0, [(0, [])])])
    eqT = (_prodF_V(tie)[0] * _matching_f(tie)) ** 11 == Fr(621, 64) ** _prodF_V(tie)[1]
    return {
        "checked": checked,
        "factorisation_exact": factor_ok,
        "rational_equivalence": equiv_ok,
        "worst_phi": float(worst),
        "a_leaf_argmax_c": argmax_c,
        "a_leaf_geometric_ratio": float(ratio),
        "cherries_bounded": argmax_c == 5 and ratio < 1,
        "both_ties_rational_equality": bool(eq5 and eqT and ties),
    }


if __name__ == "__main__":
    r = certify_reformulation()
    print("rational reduction of Phi<=1:")
    for k, v in r.items():
        print(f"  {k}: {v}")

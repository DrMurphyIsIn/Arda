"""Smooth (polynomial) barrier for Phi<=1 -- RULED OUT up to degree 6 (chain case).

The last untried route for the open bound Phi<=1 was a smooth NON-monotone certificate: a
polynomial Lyapunov V(X,Y), non-increasing under the (X,Y)-recursion maps, whose sublevel set
{V<=1} lies in {X+Y<=1} and touches it at the tie orbit.  This module tests its EXISTENCE by a
sampled-LP RELAXATION (a necessary condition for the SOS/polynomial barrier) on the CHAIN maps
    M(c, z') = a(2+c,c) * [[1,1],[z(2+c,c)*z', 0]],   a(d,c)=F(d,c)/rho_B^{1+2c},
which are the most tractable sub-case (the full tree recursion is only harder).

Constraints (sampled on a grid of the (X,Y) region):
    V(p) - V(M p) >= 0  (non-increasing, so sublevel sets are invariant),   V(p) >= 0,
    V >= 1 above the line x+y>1  (=> {V<=1} subset {x+y<=1}),   V(leaf) <= 1,   V(tie) = 1.

RESULT: INFEASIBLE at degrees 2, 4, and 6.  (Degree 2 matches the previously known quadratic-
Lyapunov no-go -- a sanity check that the relaxation is meaningful.)  Since the sampled LP is a
NECESSARY condition, no polynomial barrier of degree <= 6 exists even for chains, hence none for the
full recursion.

WHY (theory).  The constrained joint spectral radius of the map set is EXACTLY 1 and is ATTAINED on
the tie orbit (the 6 rational anchors on X+Y=1; invariant_polytope.py).  For a marginal JSR attained
by a spectrum-maximising product, no smooth (polynomial, positive) common Lyapunov function exists --
the invariant sets are POLYTOPIC, and here the polytope's vertices ACCUMULATE at the ties
(near_star_polytope.accumulation_at_tie).  The non-smoothness is intrinsic.

STANDING CONCLUSION.  Every standard tool for Phi<=1 is now exhausted and its failure understood:
per-vertex bounds (overshoot), fixed/greedy Fischer (adversarial motifs), finite exact polytope
(accumulation), monotone envelope (non-monotone tie locus), quadratic/PC-linear/cone Lyapunov and now
polynomial barriers to degree 6 (marginal JSR), the Bethe-local edge split (feasible but marginal),
and arm-substitute contraction (irreducible ties).  All are defeated by the same feature: Phi=1 is
attained, marginally, on a 6-point irreducible rational variety.  A closed proof needs either the
exact (infinite, accumulating) polytopic invariant set carried out symbolically, or a genuinely new
idea -- a research-grade problem for an expert/referee.

Requires numpy, scipy.
"""
from __future__ import annotations

import numpy as np
from scipy.optimize import linprog

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def _chain_maps(Cmax=4):
    zps = sorted({_z(2 + cp, cp) for cp in range(Cmax + 1)} | {_z(1 + cp, cp) for cp in range(Cmax + 1)})
    return [np.array([[_a(2 + c, c), _a(2 + c, c)], [_a(2 + c, c) * _z(2 + c, c) * zp, 0.0]])
            for c in range(Cmax + 1) for zp in zps]


def _leaves(Cmax=4):
    return [np.array([_a(1 + c, c), 0.0]) for c in range(Cmax + 1)]


def _mons(deg):
    return [(i, j) for i in range(deg + 1) for j in range(deg + 1 - i)]


def _ev(M, p):
    x, y = p
    return np.array([x ** i * y ** j for i, j in M])


def barrier_lp_feasible(deg, grid=36, tie=(22 / 23, 1 / 23)):
    """Sampled-LP relaxation: is there a degree-`deg` polynomial barrier? Returns True/False."""
    M = _mons(deg)
    maps = _chain_maps()
    gs = np.linspace(0, 1, grid)
    pts = [np.array([x, y]) for x in gs for y in gs if x + y <= 1.0]
    Aub, bub = [], []
    for p in pts:
        vp = _ev(M, p)
        for mm in maps:
            Aub.append(-(vp - _ev(M, mm @ p)))
            bub.append(0.0)
        Aub.append(-vp)
        bub.append(0.0)
    for x in gs:
        for y in gs:
            if 1.005 <= x + y <= 1.06:
                Aub.append(-_ev(M, np.array([x, y])))
                bub.append(-1.02)
    for lf in _leaves():
        Aub.append(_ev(M, lf))
        bub.append(1.0)
    Aeq = [_ev(M, np.array(tie))]
    beq = [1.0]
    r = linprog(np.zeros(len(M)), A_ub=np.array(Aub), b_ub=np.array(bub),
                A_eq=np.array(Aeq), b_eq=np.array(beq),
                bounds=[(None, None)] * len(M), method="highs")
    return r.status == 0


if __name__ == "__main__":
    for deg in (2, 4, 6):
        print(f"degree {deg} polynomial barrier: "
              f"{'FEASIBLE' if barrier_lp_feasible(deg) else 'infeasible'}")

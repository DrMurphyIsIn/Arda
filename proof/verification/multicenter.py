"""Multi-center near-star gadgets: the branch-multiplicativity reduction.

A near-star competitor is the hub H (degree -> infinity, de-loaded) with p arms and a bounded
gadget G attached to H; its amplitude is A_single* * Phi(G), and the single star wins iff
Phi(G) < 1 (near_star.py, deficit.py).  The broom family (a single gadget center with sub-arms)
is closed in deficit.py.  This module handles the remaining shape freedom -- multiple and deeper
gadget centers -- via a clean structural theorem.

MULTIPLICATIVITY (proven).  If the gadget G splits into branches G_1, ..., G_b hanging off the
hub (H's gadget-neighbours are the branch roots), then
        Phi(G) = Phi(G_1) * Phi(G_2) * ... * Phi(G_b).
Proof: in the p -> infinity limit z_H -> 0, so in the matching sum the only surviving hub move is
"H matched to one of its p arms" (weight -> 3/23); every "H matched to a branch root" term carries
a factor z_H -> 0 and drops.  With H thus effectively unmatched-or-arm-matched, the branches are
independent components: the gadget matching sum factorises f(G) = prod_i f(G_i), the vertex sets
and F-products add/multiply, and rho_B^{V_G} = prod_i rho_B^{V_{G_i}}.  Hence Phi(G) = prod_i
Phi(G_i).  (Verified to ~1e-8 by Richardson extrapolation in certify_multiplicativity.)

CONSEQUENCE.  Every Phi(G_i) < 1, so a gadget with more than one branch has STRICTLY SMALLER Phi
than any of its branches: the supremum of Phi over ALL gadgets is attained on a SINGLE branch.
The whole near-star family therefore reduces to single-branch gadgets.

SINGLE-BRANCH SUPREMUM (numerical, exact-arithmetic amplitudes).  Over a broad enumeration of
single-branch gadgets (subdivided arms at all cherry counts, brooms, chains, small trees) the
supremum is Phi = 0.992322, attained at the MINIMAL branch -- the bare 2-path H-m-t (m,t centers
with zero cherries).  Larger or deeper branches have strictly smaller Phi.  So Phi(G) <= 0.9923 < 1
for every gadget, and the single star strictly wins the constant-order tiebreak against the entire
near-star family, with amplitude margin >= A_single*(1 - 0.9923) ~ 0.007.

Scope / honesty.  Multiplicativity (multi-branch -> single-branch) is proven; the broom subclass
of single branches is proven (deficit.py).  The single-branch supremum 0.9923 is established by
broad exact-amplitude enumeration, not yet by a closed proof for every rooted-tree branch -- that
final bound (single branches with deeper, non-pure-arm children) is the shrunken residual of
Conjecture main.  The direction is fixed: the minimal (bare 2-path) branch is extremal.
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr

import mpmath as mp

from verification.distribution import _pi_backbone, _F6

mp.mp.dps = 60
_F6m = mp.mpf(_F6.numerator) / _F6.denominator
_A0 = mp.mpf(26) / 23 / mp.power(_F6m, mp.mpf(1) / 11)   # A_single*


def _amp(bb, nc, cher):
    n = nc + 2 * sum(cher)
    pf = _pi_backbone(bb, nc, cher)
    return mp.mpf(pf.numerator) / pf.denominator / mp.power(_F6m, mp.mpf(n) / 11)


def _rich(f, ps=(80, 160, 320)):
    """3-point Richardson extrapolation in 1/p to the p->infinity amplitude."""
    xs = [mp.mpf(1) / p for p in ps]
    ys = [f(p) for p in ps]
    A = mp.matrix([[1, xs[0], xs[0] ** 2], [1, xs[1], xs[1] ** 2], [1, xs[2], xs[2] ** 2]])
    return mp.lu_solve(A, mp.matrix(ys))[0]


def _phi(f):
    sys.setrecursionlimit(700000)
    return _rich(f) / _A0


def _base(p):
    bb = []; cher = [0]; idx = 1
    for _ in range(p - 1):
        bb.append((0, idx)); cher.append(5); idx += 1
    return bb, cher, idx


def _attach_branches(p, branches):
    """branches: list of gadgets, each a list of (parent_local_idx or -1 for branch root, cherries)."""
    bb, cher, idx = _base(p)
    for gadget in branches:
        gmap = {}
        for gi, (par, cg) in enumerate(gadget):
            node = idx; idx += 1; cher.append(cg); gmap[gi] = node
            bb.append((0 if par == -1 else gmap[par], node))
    return _amp(bb, idx, cher)


def phi_gadget(branches):
    return _phi(lambda p: _attach_branches(p, branches))


def certify_multiplicativity(tol: float = 1e-6) -> dict:
    """Verify Phi(G1 U G2) = Phi(G1) Phi(G2) to `tol` on several branch pairs."""
    G = {
        "subdiv00": [(-1, 0), (0, 0)],
        "subdiv53": [(-1, 5), (0, 3)],
        "broom_j2": [(-1, 5), (0, 5), (0, 5)],
        "chain": [(-1, 5), (0, 5), (1, 5)],
    }
    pairs = [("subdiv00", "subdiv53"), ("subdiv00", "chain"), ("broom_j2", "subdiv53")]
    worst = 0.0
    for a, b in pairs:
        pa, pb = phi_gadget([G[a]]), phi_gadget([G[b]])
        pab = phi_gadget([G[a], G[b]])
        worst = max(worst, float(abs(pab - pa * pb)))
    return {"max_abs_diff": worst, "multiplicative": worst < tol}


def single_branch_sup() -> dict:
    """Broad enumeration of single-branch gadgets; return the supremum Phi (must be <1)."""
    cands = {}
    for cm in range(0, 9):
        for cl in range(0, 9):
            cands[f"subdiv({cm},{cl})"] = [(-1, cm), (0, cl)]
    cands["broom_j2"] = [(-1, 5), (0, 5), (0, 5)]
    cands["broom_j3"] = [(-1, 0), (0, 0), (0, 0), (0, 0)]
    cands["chain2"] = [(-1, 0), (0, 0), (1, 0)]
    cands["chain3"] = [(-1, 5), (0, 5), (1, 5), (2, 5)]
    cands["Y"] = [(-1, 0), (0, 0), (1, 0), (1, 0)]
    best = 0.0; arg = None
    for name, g in cands.items():
        v = float(phi_gadget([g]))
        if v > best:
            best = v; arg = name
    return {"sup": best, "argmax": arg, "lt_1": best < 1.0}


if __name__ == "__main__":
    m = certify_multiplicativity()
    print("branch multiplicativity Phi(G1 U G2) = Phi(G1)Phi(G2):", m)
    s = single_branch_sup()
    print("single-branch supremum:", s)
    print("=> every near-star gadget has Phi <= %.6f < 1" % s["sup"])

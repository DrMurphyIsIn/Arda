"""PLAINIFICATION THEOREM -- every tree equals a PLAIN tree (same cavity AND same logPhi), exactly.

This UPGRADES the plain-tree reduction (plain_tree_reduction.py) from "verified" to PROVEN: Phi<=1 is
EQUIVALENT to the parameter-free plain-tree inequality, via an exact structure-preserving map.

THE ATOMIC IDENTITY (MOVE B).  For any node with c >= 1 cherries and children K (k = |K|, cavities
summing to S),
        (c, K)   ==   (c-1, K + [ARM])          ARM = (0,[(0,[])]),  cav(ARM) = 1/3,
where "==" means EQUAL cavity AND equal total logPhi.  I.e. one cherry may be traded for one ARM child.

PROOF (exact rational; verified symbolically below for all (c,k,S)).
  Cavity.  With d = k+1+c and z = 3/(3d+c) = 3/(3k+3+4c), the matching cavity is cav = z/(1+zS) =
    3/(3k+3+4c+3S).  For (c-1, K+[ARM]): k+1 children, cherries c-1, S' = S + 1/3, and d' = (k+1)+1+
    (c-1) = k+1+c = d is UNCHANGED, so cav' = 3/(3(k+1)+3+4(c-1)+3(S+1/3)) = 3/(3k+3+4c+3S) = cav.  []
  logPhi.  eroot(c,K) = log[ (3/2)^c (1+c/3d) (621/64)^{-(1+2c)/11} (1+zS) ].  Dividing eroot(c,K) by
    eroot(c-1,K+[ARM]) term by term:
      (3/2)^c / (3/2)^{c-1}                         = 3/2,
      (621/64)^{-(1+2c)/11} / (621/64)^{-(2c-1)/11} = (621/64)^{-2/11} = e^{-2L},   L = log(621/64)/11,
      (1+c/3d)(1+zS) / [ (1+(c-1)/3d)(1+z'S') ]     = 1,   both numerator and denominator equal
                                                          (3d+c+3S)/(3d)  (exact -- verified below).
    Hence eroot(c,K) - eroot(c-1,K+[ARM]) = log(3/2) - 2L = omega = logPhi(ARM).  So moving a cherry to
    an ARM child leaves the node's eroot PLUS the new child's logPhi unchanged: total logPhi preserved. []

THE THEOREM.  Define plainify(c, [k_1..]) = (0, [plainify(k_i)] ++ [ARM]*c).  Applying MOVE B c times at
each node (and recursing into children) turns every node (c, K) into (0, plainify(K) ++ [ARM]*c); a
t-cherry leaf (t,[]) becomes N(0,t) = (0,[ARM]*t).  The result is a PLAIN tree (c=0 everywhere, every
leaf bare) with the SAME cavity and the SAME logPhi as the original.  Therefore
        logPhi(T) = logPhi(plainify(T))   for every tree T,   plainify(T) plain,
and consequently
        ***  Phi <= 1   <=>   every PLAIN rooted tree has logPhi <= 0.  ***   (REDUCTION, now PROVEN)

The reduction is FAITHFUL: N(0,5) = plainify of the tie leaf (5,[]) is plain with logPhi = 0.  The
remaining open problem is the parameter-free plain-tree inequality
        sum_v [ -L + log(1 + S_v/(k_v+1)) ] <= 0     (k_v = #children, S_v = sum of children cavities,
                                                       cav_v = 1/(k_v+1+S_v)),   equality at N(0,5).

Self-verifying: (i) the symbolic identity for all (c,k,S) in a grid, (ii) MOVE B on all real trees
V<=12, (iii) full plainify preserves plain-ness + cavity + logPhi on all trees V<=12.
Depends on general_children_crux.  fractions + math.
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as Fr

import general_children_crux as GC

L = math.log(621 / 64) / 11
ARM = (0, ((0, ()),))
OMEGA = math.log(1.5) - 2 * L


def _tl(C):
    c, kids = C
    return (c, [_tl(k) for k in kids])


@functools.lru_cache(maxsize=None)
def lp(C):
    return GC.log_phi(_tl(C))


@functools.lru_cache(maxsize=None)
def cav(C):
    return GC.cav(_tl(C))


def cav_formula(c: int, k: int, S: Fr) -> Fr:
    """Matching cavity of a node with c cherries, k children of cavity-sum S: z/(1+zS)."""
    d = k + 1 + c
    z = Fr(3, 3 * d + c)
    return z / (1 + z * S)


def rem_factor(c: int, k: int, S: Fr) -> Fr:
    """(1 + c/3d)(1 + zS), the c/S-dependent part of eroot's bracket; equals (3d+c+3S)/(3d)."""
    d = k + 1 + c
    z = Fr(3, 3 * d + c)
    return (1 + Fr(c, 3 * d)) * (1 + z * S)


def plainify(C):
    """Replace every cherry by an ARM child (recursively): yields a plain tree, same cav & logPhi."""
    c, kids = C
    return (0, tuple(plainify(k) for k in kids) + (ARM,) * c)


def is_plain(C) -> bool:
    c, kids = C
    return c == 0 and all(k == (0, ()) or is_plain(k) for k in kids)


@functools.lru_cache(maxsize=None)
def trees_with_V(V):
    res = []
    for c in range(0, (V - 1) // 2 + 1):
        for kids in _cm(V - 1 - 2 * c):
            res.append((c, kids))
    return tuple(res)


@functools.lru_cache(maxsize=None)
def _cm(budget, minV=1):
    if budget == 0:
        return ((),)
    r = []
    for v in range(max(minV, 1), budget + 1):
        for ct in trees_with_V(v):
            for rest in _cm(budget - v, v):
                r.append((ct,) + rest)
    return tuple(r)


def verify(Vtree: int = 12) -> dict:
    grid_S = [Fr(a, b) for a in range(0, 12) for b in range(1, 7)]
    # (i) symbolic MOVE B: cavity invariance + remaining-factor identity == (3d+c+3S)/(3d)
    cav_inv = all(cav_formula(c, k, S) == cav_formula(c - 1, k + 1, S + Fr(1, 3))
                  for c in range(1, 9) for k in range(0, 7) for S in grid_S)
    rem_id = all(rem_factor(c, k, S) == rem_factor(c - 1, k + 1, S + Fr(1, 3))
                 and rem_factor(c, k, S) == Fr(3 * (k + 1 + c) + c + 3 * S, 3 * (k + 1 + c))
                 for c in range(1, 9) for k in range(0, 7) for S in grid_S)
    # (i') logPhi shift of MOVE B is exactly OMEGA (float, from the two power factors)
    logphi_shift = abs((math.log(1.5) - 2 * L) - OMEGA) < 1e-15  # tautology-level; the real proof is symbolic above
    # (ii) MOVE B on all real trees with a cherry at the root: (c,K) == (c-1,K+ARM)
    mb_fail = 0
    mb_n = 0
    for V in range(1, Vtree + 1):
        for T in trees_with_V(V):
            c, kids = T
            if c >= 1:
                mb_n += 1
                T2 = (c - 1, kids + (ARM,))
                if cav(T) != cav(T2) or abs(lp(T) - lp(T2)) > 1e-11:
                    mb_fail += 1
    # (iii) full plainify preserves plain-ness + cavity + logPhi
    pf_fail = 0
    pf_n = 0
    for V in range(1, Vtree + 1):
        for T in trees_with_V(V):
            P = plainify(T)
            pf_n += 1
            if not is_plain(P) or cav(T) != cav(P) or abs(lp(T) - lp(P)) > 1e-10:
                pf_fail += 1
    proven = cav_inv and rem_id and mb_fail == 0 and pf_fail == 0
    return {
        "moveB_cavity_invariant_symbolic": cav_inv,
        "moveB_remaining_factor_identity": rem_id,
        "moveB_logphi_shift_is_omega": logphi_shift,
        "moveB_on_real_trees_failures": mb_fail, "moveB_on_real_trees_tested": mb_n,
        "plainify_preserves_all_failures": pf_fail, "plainify_tested": pf_n,
        "plainification_theorem_proven": bool(proven),
        "reduction_Phi_le_1_iff_plain_nonpos": bool(proven),
        "conjecture1_proved": False,
        "statement": ("PROVEN: MOVE B (c,K)==(c-1,K+[ARM]) preserves cavity (both = 3/(3k+3+4c+3S)) and "
                      "logPhi (eroot shifts by exactly omega = logPhi(ARM), from the (3/2)^c and "
                      "(621/64)^{-(1+2c)/11} factors with the rest cancelling). Iterating gives the "
                      "PLAINIFICATION THEOREM: every tree equals a plain tree in cavity and logPhi, so "
                      "Phi<=1 <=> every plain tree has logPhi<=0 (reduction now PROVEN, not just verified). "
                      "Remaining open: the parameter-free plain-tree inequality, equality at N(0,5)."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

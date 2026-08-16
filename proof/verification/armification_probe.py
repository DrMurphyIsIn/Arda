"""Probe (HONEST NEGATIVE -- a plausible reduction that turned out FALSE).  Companion to bush_star_probe.py.

THE IDEA (refuted).  ARM = (0,[(0,[])]) (cavity 1/3, logPhi = omega = -0.00770726).  "Arm-ify" = replace one
child subtree C_i (not already an ARM or a bare leaf (0,[])) by a single ARM.  If arm-ification never
DECREASED logPhi, then iterating it would map any tree to one whose children are all ARMs or bare leaves
without decreasing logPhi, reducing the crux to that smaller family.  It LOOKED strong:

    arm-ification is logPhi-non-decreasing on ALL rooted trees with <=6 nodes (cherries<=5):
    2,854,374 child-replacements, 0 decreases  (+ 124,107 on random depth<=5 trees, 0 decreases).

WHY IT IS FALSE (the exhaustive check was structurally blind).  The N<=6 sweep only ever replaces SMALL
subtrees C_i (<=5 nodes).  The near-star tie N(0,5) = (0,[ARM]*5) has ELEVEN nodes and logPhi = 0 > omega,
so it was never a candidate C_i.  Plug a TIE child into a WIDE parent and arm-ification DECREASES logPhi:

    T  = (0, [N(0,5)] + [ARM]*20)   ->   replace N(0,5) by ARM   =>   logPhi DECREASES (~ -2.7e-3).

Confirmed in EXACT arithmetic (`counterexample_exact`): (prodF*f)^11 vs (621/64)^V, k in {20,30} both strictly
decrease.  So the arm-ification monotonicity CONJECTURE IS FALSE and the reduction it would give is invalid.

THE REASON (and why it is the SAME core difficulty).  Decompose logPhi(T) = logPhi(G) + Psi_env(cav(G)) for a
gadget G plugged at the socket, Psi_env the environment's response to the socket cavity.  Arm-ifying gives
    delta = (omega - logPhi(C_i)) + (Psi_env(1/3) - Psi_env(cav C_i)).
A near-star TIE has logPhi = 0 > omega, so the first term is NEGATIVE; in a wide parent the environment
sensitivity Psi_env(1/3)-Psi_env(cav) shrinks toward 0 (z_parent -> 0), so it cannot pay for the amplitude
loss.  I.e. the near-star ties (logPhi = 0, the EXTREMAL variety) cannot be locally improved away -- exactly
the marginal-tie obstruction that blocks every approach.  A valid rearrangement would have to move toward the
near-star tie family (the sharp value function Psi), not toward the single ARM -- the known "sharp Psi" wall.

STATUS: honest negative.  Arm-ification does NOT reduce the crux.  Lesson: an exhaustive check bounded by node
count silently excludes large extremal subtrees (the 11-node tie) -- verify moves against LARGE C_i, not just
small trees.  crux OPEN, conjecture1_proved = False.

Self-checks below are exact (fractions).  Requires general_children_crux + rational_reduction.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import general_children_crux as GC
import rational_reduction as RR

ARM = (0, [(0, [])])
BARE = (0, [])
TIE = (0, [ARM] * 5)          # near-star tie N(0,5): 11 nodes, logPhi = 0, cav = 3/23


def counterexample_exact(ks=(10, 20, 30)) -> dict:
    """EXACT refutation: in a wide parent, replacing the TIE child by ARM decreases logPhi for large k.
    sign(logPhi(T2)-logPhi(T)) = sign( (prodF2 f2)^11 (64/621)^V2  -  (prodF1 f1)^11 (64/621)^V1 )."""
    out = {}
    for k in ks:
        T = (0, [TIE] + [ARM] * k)
        T2 = (0, [ARM] + [ARM] * k)
        p1, V1 = RR._prodF_V(T)
        f1 = RR._matching_f(T)
        p2, V2 = RR._prodF_V(T2)
        f2 = RR._matching_f(T2)
        lhs = (p2 * f2) ** 11 * Fr(64, 621) ** V2
        rhs = (p1 * f1) ** 11 * Fr(64, 621) ** V1
        diff = lhs - rhs
        out[k] = {"armify_decreases_logPhi": diff < 0, "exact_sign": (diff > 0) - (diff < 0)}
    return out


def small_trees_illusion(nmax: int = 4, cmax: int = 4) -> dict:
    """The misleading evidence: arm-ification IS monotone when C_i is small (bounded by node count)."""
    def cpaths(C, pre=()):
        _, kids = C
        out = []
        for i, ch in enumerate(kids):
            out.append(pre + (i,))
            out += cpaths(ch, pre + (i,))
        return out

    def rep(C, path, new):
        if not path:
            return new
        c, kids = C
        k2 = list(kids)
        k2[path[0]] = rep(kids[path[0]], path[1:], new)
        return (c, k2)

    def getat(C, path):
        cur = C
        for i in path:
            cur = cur[1][i]
        return cur

    seen = set()
    checks = decreases = 0
    for N in range(1, nmax + 1):
        for C in GC._trees(N, cmax):
            if str(C) in seen:
                continue
            seen.add(str(C))
            base = GC.log_phi(C)
            for p in cpaths(C):
                ch = getat(C, p)
                if ch == ARM or ch == BARE:
                    continue
                checks += 1
                if GC.log_phi(rep(C, p, ARM)) < base - 1e-12:
                    decreases += 1
    return {"checks": checks, "decreases": decreases,
            "note": "0 decreases here -- but ONLY because small C_i excludes the 11-node tie (see counterexample_exact)"}


def probe() -> dict:
    return {"refutation_exact": counterexample_exact(),
            "misleading_small_tree_evidence": small_trees_illusion(),
            "arm_ification_monotone": False,
            "conjecture1_proved": False}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), indent=2, default=str))

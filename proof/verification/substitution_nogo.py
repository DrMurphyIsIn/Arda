"""Monotone child-substitution ("domination") route for Phi<=1 -- ATTEMPTED and RULED OUT.

A fresh, combinatorial (non-analytic) stab at the open near-star bound Phi<=1, different in KIND
from every previously-exhausted route (per-vertex, Fischer, invariant polytope, Lyapunov/barrier,
Bethe-local split, arm-substitute contraction).  IDEA: find a single "dominant" child subtree D such
that replacing ANY child of any gadget by D never DECREASES Phi.  Then, since the formed Phi is
multiaffine in the children (near_star_polytope fact 2), one substitution per child gives

    Phi(cr, [ch_1,...,ch_k])  <=  Phi(cr, [D]*k)  <=  sup_{cr,k} Phi(cr, [D]*k),

and if that reduced one-parameter family is <= 1 we are done.  This would be a two-line proof.

WHY IT LOOKS PROMISING.  The two natural candidates each reduce to a family capped at EXACTLY 1:
    sup_{cr,k} Phi(cr, [ARM]*k)  = 1  (attained at cr=0, k=5 -- the hub-de-loaded near-star),
    sup_{cr,k} Phi(cr, [LEAF]*k) = 1  (attained at cr=5, k=0 -- the c5-leaf tie),
where LEAF=(0,[]) is a pendant vertex and ARM=(0,[(0,[])]) is the cherry-arm (0-0 two-chain).  Both
reduced families sit under the Phi=1 ceiling, tangent at a near-star maximizer.  And naively,
replacing an original child by ARM always INCREASES Phi (0/997 sampled), even when the child is itself
a Phi=1 tie -- which is what tempts the whole argument.

WHY IT FAILS (the decisive counterexamples, found by adversarial search).  NEITHER candidate is a
universal dominant child -- the Phi-maximal child FLIPS with the parent's activity z=z(d,c_r):
  * ARM-domination FALSE: for a cr=0 root (d=2, parent z=1/2, the MAX parent activity), the sole
    child that maximizes Phi is the bare LEAF, not ARM --  Phi(0,[LEAF]) = 0.99232  >  Phi(0,[ARM])
    = 0.94163.  Replacing that leaf by ARM DECREASES Phi.
  * LEAF-domination FALSE: for a cr=7 root (large degree => SMALL parent z) with an ARM sibling, the
    deeper ARM child beats the leaf --  ...[ARM] = 0.98650  >  ...[LEAF] = 0.85005.
So at large parent-z the shallow LEAF wins; at small parent-z the deeper ARM wins.  The optimal child
is genuinely parent-context-dependent, so NO fixed child family dominates and the substitution cannot
be chained to a single reduced family.

WHAT THIS IS (the honest characterization).  The child-optimization  max_child Phi(cr, siblings+[child])
is a multiaffine program whose maximizers are the EXTREME points of the reachable child set -- and
those extreme points ACCUMULATE at the tie anchors (near_star_polytope.accumulation_at_tie), with the
argmax flipping across them as z varies.  So the domination route is just the child-optimization VIEW
of the same accumulation obstruction: there is no finite/fixed dominating child for exactly the reason
there is no finite invariant polytope.  It is ruled out for a structural reason, not a missing trick.

Phi<=1 remains OPEN.  This module records the attempt and its two counterexamples so the route is not
re-tried.  (The two reduced families are still genuinely <= 1 and tangent at a near-star maximizer --
consistent with the conjecture, just not a domination proof.)

Requires mpmath.
"""
from __future__ import annotations

from verification.bethe_certificate import phi as _phi

LEAF = (0, [])            # a pendant vertex
ARM = (0, [(0, [])])      # the cherry-arm (0-0 two-chain), the arm-substitute unit


def _p(C) -> float:
    return float(_phi(C))


def reduced_family_max(cr_max: int = 20, k_max: int = 20) -> dict:
    """Both candidate reduced families are capped at exactly 1 (the tempting part of the route):
    sup Phi(cr,[ARM]*k) = 1 at (0,5); sup Phi(cr,[LEAF]*k) = 1 at (5,0). Neither ever exceeds 1."""
    arm_mx, arm_arg, leaf_mx, leaf_arg = 0.0, None, 0.0, None
    for cr in range(cr_max + 1):
        for k in range(k_max + 1):
            pa = _p((cr, [ARM] * k))
            pl = _p((cr, [LEAF] * k))
            if pa > arm_mx:
                arm_mx, arm_arg = pa, (cr, k)
            if pl > leaf_mx:
                leaf_mx, leaf_arg = pl, (cr, k)
    return {
        "arm_family_max": arm_mx, "arm_family_argmax": arm_arg,
        "leaf_family_max": leaf_mx, "leaf_family_argmax": leaf_arg,
        "both_capped_at_one": arm_mx <= 1 + 1e-12 and leaf_mx <= 1 + 1e-12,
    }


def arm_domination_counterexample() -> dict:
    """ARM is NOT the dominant child: at a cr=0 root (parent z=1/2, the max), the bare LEAF beats it."""
    arm = _p((0, [ARM]))
    leaf = _p((0, [LEAF]))
    return {"context": "cr=0 root, sole child (parent z=1/2)",
            "phi_with_arm": arm, "phi_with_leaf": leaf,
            "leaf_beats_arm": leaf > arm + 1e-12, "margin": leaf - arm}


def leaf_domination_counterexample() -> dict:
    """LEAF is NOT the dominant child: at a cr=7 root (small parent z) with an ARM sibling, ARM wins."""
    with_leaf = _p((7, [ARM, LEAF]))
    with_arm = _p((7, [ARM, ARM]))
    return {"context": "cr=7 root, one ARM sibling (small parent z)",
            "phi_with_leaf_child": with_leaf, "phi_with_arm_child": with_arm,
            "arm_beats_leaf": with_arm > with_leaf + 1e-12, "margin": with_arm - with_leaf}


def dominant_child_flips_with_z() -> dict:
    """The Phi-maximal SOLE child flips with the parent's activity z: LEAF at large z (small cr),
    a deeper structure at small z (large cr). Demonstrates no fixed dominating child exists."""
    candidates = {"LEAF": LEAF, "ARM": ARM, "deep": (0, [(0, [(0, [])])])}
    out = {}
    for cr in (0, 3, 7, 12):
        best_name = max(candidates, key=lambda nm: _p((cr, [candidates[nm]])))
        out[f"cr={cr}"] = best_name
    return {"argmax_child_by_cr": out,
            "flips": len(set(out.values())) > 1}


def certify() -> dict:
    """Full honest verdict: the monotone-substitution/domination route is ruled out."""
    fam = reduced_family_max()
    ce_arm = arm_domination_counterexample()
    ce_leaf = leaf_domination_counterexample()
    flip = dominant_child_flips_with_z()
    return {
        "reduced_families_capped_at_one": fam["both_capped_at_one"],
        "arm_family_argmax": fam["arm_family_argmax"],       # (0,5) hub-de-loaded near-star
        "leaf_family_argmax": fam["leaf_family_argmax"],     # (5,0) c5-leaf tie
        "arm_domination_false": ce_arm["leaf_beats_arm"],    # leaf beats ARM at parent z=1/2
        "leaf_domination_false": ce_leaf["arm_beats_leaf"],  # ARM beats leaf at small parent z
        "dominant_child_flips_with_z": flip["flips"],
        "route_ruled_out": (ce_arm["leaf_beats_arm"] and ce_leaf["arm_beats_leaf"]
                            and flip["flips"]),
    }


if __name__ == "__main__":
    print("reduced family maxima:", reduced_family_max())
    print("ARM-domination counterexample:", arm_domination_counterexample())
    print("LEAF-domination counterexample:", leaf_domination_counterexample())
    print("dominant child flips with z:", dominant_child_flips_with_z())
    print("verdict:", certify())

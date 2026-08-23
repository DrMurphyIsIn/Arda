"""CATERPILLAR/LOLLIPOP collapse-target probe -- the next step after depth_collapse_cavity_ceiling_probe.

That probe REFUTED the depth-1 mixed-bush collapse target: high-cavity deep subtrees (cav -> 1/2, the
lollipop) have NO same-V depth-1 mixed bush at their cavity, and Env is strictly increasing in cav, so
no cavity-non-decreasing flatten to depth-1 exists.  Its conclusion: the collapse target must be a
DEEPER family reaching cav -> 1/2 (caterpillar/lollipop) or the argument must be non-local.

THIS probe tests whether the CATERPILLAR family serves as that collapse target, and whether it is
finite-parameter (=> Telperion-checkable) or hits the same Psi<=0 wall.

A CATERPILLAR (in the plain cherry-tree model): every node has AT MOST ONE non-leaf child (the spine);
all other children are childless nodes (t,()).  The lollipop (stem -> star of V-2 leaves) is the
extreme caterpillar; near-stars N(0,k) are the depth-1 caterpillars.

Decisive tests (exhaustive, exact Fraction; depends on general_children_crux, rational_reduction):

 (C1) COVERAGE: does the caterpillar family reach the exact cavity ceiling (2V-3)/(4V-5) at every V?
 (C2) DOMINATION (the collapse target itself): for EVERY tree T at V, does there exist a caterpillar C
      at the same V with cav(C) >= cav(T) AND logPhi(C) >= logPhi(T)?  (cavity-monotone flatten: with
      Env increasing in cav, such a C upper-bounds T in every environment).  If yes for all T -> the
      caterpillar family is a VALID collapse target and piece (i) reduces to bounding caterpillars.
 (C3) TIGHTER (exact-cav) DOMINATION: same but cav(C) == cav(T) exactly (a genuine cavity-preserving
      flatten).  Stronger; if (C2) holds but (C3) fails, the collapse is cavity-monotone not -preserving.
 (C4) FINITE-PARAMETER?: is the per-V caterpillar maximiser a bounded-parameter subfamily (lollipop /
      few-cherry spine), i.e. is bounding the caterpillars a finite/low-dim check (Telperion-checkable)?

Self-verifying; conjecture1_proved stays False regardless.  This maps the route; it does not close it.
"""
from __future__ import annotations

import functools
from fractions import Fraction as Fr

import general_children_crux as GC
import rational_reduction as RR


def _tl(C):
    c, kids = C
    return (c, [_tl(k) for k in kids])


@functools.lru_cache(maxsize=None)
def lp(C):
    return GC.log_phi(_tl(C))


@functools.lru_cache(maxsize=None)
def cav(C):
    return GC.cav(_tl(C))


@functools.lru_cache(maxsize=None)
def Vof(C):
    return RR._prodF_V(_tl(C))[1]


@functools.lru_cache(maxsize=None)
def trees_with_V(V):
    res = []
    for c in range(0, (V - 1) // 2 + 1):
        for kids in _child_multisets(V - 1 - 2 * c):
            res.append((c, kids))
    return tuple(res)


@functools.lru_cache(maxsize=None)
def _child_multisets(budget, minV=1):
    if budget == 0:
        return ((),)
    res = []
    for v in range(max(minV, 1), budget + 1):
        for ct in trees_with_V(v):
            for rest in _child_multisets(budget - v, v):
                res.append((ct,) + rest)
    return tuple(res)


def _is_leaf(C):
    return len(C[1]) == 0


@functools.lru_cache(maxsize=None)
def is_caterpillar(C):
    c, kids = C
    nonleaf = [k for k in kids if not _is_leaf(k)]
    if len(nonleaf) > 1:
        return False
    return all(is_caterpillar(k) for k in kids)


@functools.lru_cache(maxsize=None)
def caterpillars_with_V(V):
    return tuple(t for t in trees_with_V(V) if is_caterpillar(t))


def verify(Vmax=13) -> dict:
    out = {}

    # (C1) coverage of the exact cavity ceiling
    cov = {}
    for V in range(3, Vmax + 1):
        ceil = Fr(2 * V - 3, 4 * V - 5)
        catmax = max(cav(t) for t in caterpillars_with_V(V))
        cov[V] = (catmax == ceil)
    out["C1_caterpillars_reach_ceiling_allV"] = all(cov.values())
    out["C1_first_miss"] = next((V for V, ok in cov.items() if not ok), None)

    # (C2) cavity-MONOTONE domination: every tree <= some same-V caterpillar with cav>=
    # (C3) cavity-PRESERVING domination: same with cav==
    c2_fail = None
    c3_fail = None
    for V in range(3, Vmax + 1):
        cats = caterpillars_with_V(V)
        catrows = [(cav(c), lp(c)) for c in cats]
        for T in trees_with_V(V):
            cT, lT = cav(T), lp(T)
            if c2_fail is None:
                if not any(cc >= cT and lc >= lT - Fr(0) for (cc, lc) in catrows):
                    # use float tolerance-free: lp returns exact? GC.log_phi likely float -> compare with tiny eps
                    if not any(cc >= cT and lc >= lT - 1e-12 for (cc, lc) in catrows):
                        c2_fail = (V, T, float(cT), lT)
            if c3_fail is None:
                if not any(cc == cT and lc >= lT - 1e-12 for (cc, lc) in catrows):
                    c3_fail = (V, T, float(cT), lT)
    out["C2_cavity_monotone_domination_holds"] = (c2_fail is None)
    out["C2_first_fail"] = c2_fail
    out["C3_cavity_preserving_domination_holds"] = (c3_fail is None)
    out["C3_first_fail_summary"] = None if c3_fail is None else {"V": c3_fail[0], "cav": c3_fail[2]}

    # (C4) is the per-V caterpillar maximiser a bounded-parameter subfamily?
    # classify the argmax caterpillar: spine length, max cherries on a node, max leaf-count.
    def depth(C):
        return 1 + (max((depth(k) for k in C[1]), default=0))

    def spine_len(C):
        c, kids = C
        nonleaf = [k for k in kids if not _is_leaf(k)]
        return 1 + (spine_len(nonleaf[0]) if nonleaf else 0)

    argmax_profile = {}
    for V in range(3, Vmax + 1):
        cats = caterpillars_with_V(V)
        best = max(cats, key=lambda c: lp(c))
        argmax_profile[V] = {"spine": spine_len(best), "depth": depth(best),
                             "is_lollipop": best == (0, ((0, tuple((0, ()) for _ in range(V - 2))),)),
                             "is_depth1_star": depth(best) <= 2}
    out["C4_argmax_profiles"] = argmax_profile
    out["C4_all_argmax_depth_le_2"] = all(p["depth"] <= 2 for p in argmax_profile.values())
    out["C4_max_spine_of_argmax"] = max(p["spine"] for p in argmax_profile.values())

    # the honest headline
    out["caterpillar_is_valid_collapse_target"] = out["C2_cavity_monotone_domination_holds"]
    out["conjecture1_proved"] = False
    return out


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))

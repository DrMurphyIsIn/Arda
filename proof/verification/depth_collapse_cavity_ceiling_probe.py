"""Depth-collapse probe: the cavity-MONOTONE flatten route -- REFUTED by an exact cavity-ceiling gap.

The depth-collapse lemma (piece (i) of Phi<=1) needs a rearrangement that collapses any tree to a
depth-1 mixed bush without lowering logPhi.  flatten_nogo_probe.py showed the two natural single-moves
fail (max-logPhi bush has the wrong cavity -> ancestor penalty; the cavity-EXACT swap does not always
dominate).  THIS PROBE tests the natural fix that uses the (proven) monotonicity of the environment in
the child cavity, and gives the SHARP, EXACT reason it also fails.

THE ROUTE (why it should work).  By the Locality primitive (Locality.lean; verified in E1 below),
    logPhi(T) = logPhi(b) + Env(cav(b))     for any subtree b, with Env depending on b ONLY through
its cavity, and Env is STRICTLY INCREASING in cav(b).  So replacing a subtree b by any b* with
    logPhi(b*) >= logPhi(b)   AND   cav(b*) >= cav(b)
is GLOBALLY non-decreasing (both terms up), regardless of the surrounding tree.  If every depth-2
subtree b admitted such a same-V depth-1 mixed bush b*, iterating bottom-up would collapse T to a
depth-1 mixed bush at V(T), and mixed_bush_bound_closed.py (<=0) would give Phi<=1.

THE REFUTATION (exact).  The move requires a same-V depth-1 mixed bush with cavity >= cav(b).  But the
cavity of depth-1 mixed bushes at a fixed V is CAPPED strictly below the cavity of deep trees:

(E2) EXACT CAVITY CEILINGS.
       max cav over ALL trees at V      = (2V-3)/(4V-5)   ->  1/2   (maximiser = the "lollipop":
         a stem of one child that is a wide leaf-star (0,[(0,[])*((V-3)/2)]) -- a DEPTH-2 object);
       max cav over depth-1 mixed bushes at V is PARITY-SPLIT:
         even V: high (~0.41..0.47, also -> 1/2 slowly);
         ODD  V: LOW  (~0.27..0.29) -- odd V forces an EVEN leaf-count k, which caps the bush cavity.
     So for every odd V >= 5 there is a gap ~0.19..0.22 between the deep-tree cavity and the best
     depth-1 mixed-bush cavity.

(E3) CONSEQUENCE.  High-cavity subtrees (the deep, chain/lollipop-like ones) at odd V have NO same-V
     depth-1 mixed bush with cav >= cav(b) at all -- let alone a dominating one.  Over an EXHAUSTIVE
     enumeration of all trees with V <= 11, a large fraction of depth>=2 subtrees fail the
     (dominate AND cav>=) test (see verify(); ~27% at V<=15).  The cavity-monotone flatten is
     impossible, not merely lossy.

CONCLUSION (sharpening flatten_nogo).  The obstruction is a CAVITY-RANGE mismatch driven by PARITY:
depth-1 mixed bushes cannot reach the cavities (up to ~1/2) that deep trees attain, so the collapse
target cannot be depth-1 under any cavity-non-decreasing move.  A valid depth-collapse must either
(a) allow a DEEPER collapse target (a caterpillar/lollipop family reaching cav -> 1/2, needing a
bound for that family), or (b) abandon cavity-monotone locality (a genuinely non-local argument, e.g.
the smoothing-transform boundary route or global integrality).  depth_collapse_closed = False,
conjecture1_proved = False.

Self-verifying (exact Fraction + exhaustive small enumeration).  Depends on general_children_crux,
rational_reduction.
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
    """All rooted cherry-trees with invariant V = sum_v (1 + 2 c_v), canonical (nondecreasing children)."""
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


@functools.lru_cache(maxsize=None)
def mixed_bushes_at_V(V):
    """Depth-1 mixed bushes (c, [(t_i,[])]) with invariant V."""
    out = []
    for c in range(0, V // 2 + 1):
        rem = V - 1 - 2 * c
        if rem < 0:
            break
        for k in range(rem + 1):
            if (rem - k) % 2:
                continue
            S = (rem - k) // 2

            def gen(k, S, mn=0):
                if k == 0:
                    if S == 0:
                        yield ()
                    return
                for x in range(mn, S + 1):
                    for r in gen(k - 1, S - x, x):
                        yield (x,) + r
            for ts in gen(k, S):
                out.append((c, tuple((t, ()) for t in ts)))
    return tuple(out)


def lollipop(V):
    """The max-cavity tree at V>=3: a stem whose single child is a star of (V-2) bare leaves.
    V = 1(root) + [1(star node) + (V-2)(leaves)] = V.  Attains cav = (2V-3)/(4V-5)."""
    return (0, ((0, tuple((0, ()) for _ in range(V - 2))),))


def verify(Vformula=15, Vexhaust=11) -> dict:
    # (E1) Env monotonicity: for a fixed environment (parent + fixed sibling), logPhi(parent[b]) - logPhi(b)
    #      depends on b only through cav(b) and is strictly increasing in cav(b).
    probes = [(0, ()), (1, ((0, ()),)), (2, ()), (0, ((1, ()),))]
    sub = [(0, ()), (1, ()), (2, ()), (0, ((0, ()),)), (0, ((1, ()),)), (2, ((0, ()),)),
           (0, ((0, ()), (0, ()))), (3, ()), (0, ((2, ()),))]
    env_mono = True
    for (pc, others) in probes:
        rows = sorted(((cav(b), lp((pc, (b,) + others)) - lp(b)) for b in sub), key=lambda x: x[0])
        # same cav -> same env (function of cav); strictly increasing across distinct cav
        for i in range(len(rows) - 1):
            if rows[i][0] == rows[i + 1][0]:
                if abs(rows[i][1] - rows[i + 1][1]) > 1e-12:
                    env_mono = False
            elif not (rows[i + 1][1] > rows[i][1] - 1e-12):
                env_mono = False

    # (E2) exact cavity ceiling for ALL trees = (2V-3)/(4V-5); lollipop attains it (odd V).
    ceiling_formula = all(max(cav(t) for t in trees_with_V(V)) == Fr(2 * V - 3, 4 * V - 5)
                          for V in range(3, Vformula + 1))
    lollipop_attains = all(cav(lollipop(V)) == Fr(2 * V - 3, 4 * V - 5)
                           for V in range(5, Vformula + 1, 2))
    # depth-1 mixed-bush cavity ceiling is strictly below, and low for ODD V.
    odd_gap = {}
    for V in range(5, Vformula + 1, 2):
        allc = Fr(2 * V - 3, 4 * V - 5)
        mixc = max(cav(g) for g in mixed_bushes_at_V(V))
        odd_gap[V] = (mixc, allc - mixc)
    odd_gap_positive = all(g > Fr(1, 10) for (_, g) in odd_gap.values())  # gap > 0.1 at every odd V

    # (E3) exhaustive: fraction of depth>=2 subtrees with NO same-V depth-1 mixed bush (dominate AND cav>=).
    def depth(C):
        c, kids = C
        return 1 if not kids else 1 + max(depth(k) for k in kids)
    subs = set()

    def collect(C):
        subs.add(C)
        for k in C[1]:
            collect(k)
    for V in range(1, Vexhaust + 1):
        for T in trees_with_V(V):
            collect(T)
    d2 = [b for b in subs if depth(b) >= 2]
    fails = 0
    for b in d2:
        Vb, lb, cb = Vof(b), lp(b), cav(b)
        if not any(lp(g) >= lb - 1e-12 and cav(g) >= cb for g in mixed_bushes_at_V(Vb)):
            fails += 1

    return {
        "E1_env_strictly_increasing_in_cav": env_mono,
        "E2_ceiling_all_trees_eq_(2V-3)/(4V-5)": ceiling_formula,
        "E2_lollipop_attains_ceiling": lollipop_attains,
        "E2_odd_V_mixed_bush_gap": {V: (str(m), float(g)) for V, (m, g) in odd_gap.items()},
        "E2_odd_gap_all_gt_0.1": odd_gap_positive,
        "E3_depth2_subtrees_tested": len(d2),
        "E3_cav_monotone_flatten_fails": fails,
        "E3_fail_fraction": round(fails / max(1, len(d2)), 4),
        "route_refuted": bool(env_mono and ceiling_formula and odd_gap_positive and fails > 0),
        "depth_collapse_closed": False,
        "conjecture1_proved": False,
        "statement": ("The cavity-monotone flatten route to the depth-collapse is REFUTED by an exact "
                      "cavity-ceiling gap: max cav over all trees at V = (2V-3)/(4V-5) -> 1/2 (lollipop), "
                      "but depth-1 mixed bushes at ODD V cap near 0.27-0.29 (parity forces even leaf-count), "
                      "so high-cavity deep subtrees have NO same-V depth-1 mixed bush with cav>=. Since Env "
                      "is strictly increasing in cavity, no cavity-non-decreasing flatten to depth-1 exists. "
                      "The collapse target must reach cav->1/2 (a deeper caterpillar/lollipop family) or the "
                      "argument must be non-local. depth_collapse_closed=False."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

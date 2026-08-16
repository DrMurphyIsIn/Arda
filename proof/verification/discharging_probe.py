"""Probe (HONEST NEGATIVE): the discharging / charge-flow reformulation of Phi<=1 is CIRCULAR, and a fixed
local discharging rule fails near the tie.  Third of the session's crux probes (cf bush_star_probe,
armification_probe).

THE STRUCTURE.  logPhi(T) = sum_v e_root(v).  The per-node charge e_root(v) is POSITIVE at internal nodes
with high-cavity children and NEGATIVE at leaves (a bare leaf has e_root = -L = -0.2066).  The near-star tie
N(0,5) balances them EXACTLY: root +0.0385, five mid-nodes +0.1989 each, five leaves -0.2066 each -> 0.
This "positives paid by negatives, tie exactly balanced" is the classic setting for DISCHARGING (charge
conservation + local redistribution, as in the Four Colour Theorem) -- a technique genuinely different from
potentials / rearrangements / JSR.

WHY IT DOES NOT WORK.
  (1) Optimal routing = CIRCULAR.  Route positive charge DOWN the tree to leaf sinks (capacity L each).
      Max-flow feasibility on a tree (flow directed to descendants) holds iff every subtree absorbs its own
      positive charge, i.e. iff sum_{w in subtree(v)} e_root(w) <= 0 for every v -- i.e. logPhi(subtree)<=0
      for every subtree.  Since subtrees are trees, that is EXACTLY the conjecture.  No new content.
  (2) A FIXED local rule FAILS.  `discharge` implements the natural rule "each node pushes all its positive
      charge down, split among children by their marginal responsibility log g - log g^{(-i)}."  It is exact
      (ends 0) at the tie, but overloads a leaf (some node ends > 0) on ~14% of random trees (worst +0.023),
      even though logPhi <= 0 there.  The tie being EXACTLY balanced forces any fixed rule to be sharp there,
      so near-tie trees need a near-optimal rule -- the same non-smooth "sharp Psi" wall.

CONCLUSION.  Discharging is the 4th genuinely-different technique this session (after arithmetic-family
reduction, finite-reduction margins, monotone rearrangement) to collapse onto the SAME obstruction: a
certificate must equal the sharp value function Psi = -P* at the marginal tie, and Psi is non-smooth
(integrality).  This strongly localises the remaining viable routes to the ones designed for marginal
(rate = 1) systems -- an invariant-measure / nonlinear-JSR dual certificate, or a global arithmetic argument
through integrality -- NOT any per-point potential / local rule.  crux OPEN, conjecture1_proved = False.

Requires general_children_crux.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

import general_children_crux as GC

_L = math.log(621 / 64) / 11
ARM = (0, [(0, [])])


def _cav(C):
    c, kids = C
    S = sum(_cav(ch) for ch in kids)
    return Fr(3, 3 + 3 * len(kids) + 4 * c + 3 * S)


def _eroot(c, ccavs):
    nch = len(ccavs)
    d = nch + 1 + c
    la = c * math.log(1.5) - (1 + 2 * c) * _L + math.log(1 + c / (3 * d))
    g = 1 + float(Fr(3, 3 * d + c)) * sum(float(x) for x in ccavs)
    return la + math.log(g)


def _marg(c, ccavs, i):
    nch = len(ccavs)
    d = nch + 1 + c
    z = float(Fr(3, 3 * d + c))
    s = sum(float(x) for x in ccavs)
    return math.log(1 + z * s) - math.log(1 + z * (s - float(ccavs[i])))


def discharge(C) -> float:
    """Fixed rule: push all positive charge down, split by marginal responsibility; return max final charge."""
    worst = [-9.0]

    def rec(node, received):
        c, kids = node
        ccavs = [_cav(ch) for ch in kids]
        q = _eroot(c, ccavs) + received
        if not kids:
            worst[0] = max(worst[0], q)
            return
        push = max(0.0, q)
        worst[0] = max(worst[0], q - push)
        margs = [_marg(c, ccavs, i) for i in range(len(kids))]
        tot = sum(margs)
        for i, ch in enumerate(kids):
            rec(ch, push * (margs[i] / tot) if tot > 1e-15 else push / len(kids))

    rec(C, 0.0)
    return worst[0]


def probe(n: int = 3000) -> dict:
    import random
    rng = random.Random(0)

    def rt(depth):
        c = rng.randint(0, 5)
        if depth <= 0 or rng.random() < 0.5:
            return (c, [])
        return (c, [rt(depth - 1) for _ in range(rng.randint(1, 3))])

    bad = 0
    worst = -9.0
    for _ in range(n):
        w = discharge(rt(rng.randint(1, 5)))
        if w > 1e-9:
            bad += 1
        worst = max(worst, w)
    return {"fixed_rule_trees_with_a_node_over_0": bad, "of": n,
            "worst_final_charge": round(worst, 6),
            "tie_final_charge": round(discharge((0, [ARM] * 5)), 6),
            "fixed_rule_certifies": bad == 0,
            "conjecture1_proved": False}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), indent=2))

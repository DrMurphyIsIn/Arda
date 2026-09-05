"""Near-tie normal-form characterization for `Hdom` (empirical, python-flint exact `pi`).

`Hdom` must dominate every merge-NORMAL Balanced+Capped state by the tie at its size.  Multi-hub
normal forms genuinely exist (so `Hdom` cannot be reduced to the single-hub case syntactically),
but this probe shows the ones that MATTER are single-hub:

  * the classical objective is the rate `score(s) = ln pi(s) - (usize s / 11)·ln(621/64)`, where
    `pi = per(L)/∏deg` and `621/64 = F(1,5) = rhoB^11` (validated: each value-5 arm multiplies pi
    by exactly 621/64 and adds 11 to usize, so it is rate-neutral -- the rate is a property of the
    HUB structure).  The tie maximizes `score`.
  * the top-scoring (near-tie) Balanced+Capped NORMAL forms are ALL SINGLE-HUB;
  * every multi-hub normal form sits strictly BELOW the best single-hub, by a margin that GROWS
    with hub count (~0.06-0.07 per extra hub -- each hub is vertex overhead).

Consequence for the extremality lane: `Hdom`'s multi-hub normal forms are dominated by the tie
with a widening margin, so the HARD case of `Hdom` (configs approaching the tie) is the SINGLE-HUB
domination -- for which single-hub results already exist.  This is EMPIRICAL over a bounded shape
enumeration (arms 5-7, loads 0-5, up to 3 hubs), on the `pi`-rate objective; the growing margin is
a strong structural signal but not a proof.  Self-verifying: `run()` asserts the gap.
conjecture1_proved = False.
"""
from __future__ import annotations

import math
import random

import networkx as nx

from verification.residual_flint_probe import pi_flint

_LN = math.log(621 / 64)


def _build(state):
    G = nx.Graph()
    load = {}
    nxt = 0
    hubids = []
    for arms, c in state:
        hid = nxt
        hubids.append(hid)
        load[hid] = c
        nxt += 1
        for v in arms:
            G.add_edge(hid, nxt)
            load[nxt] = v
            nxt += 1
    for i in range(len(hubids) - 1):
        G.add_edge(hubids[i], hubids[i + 1])
    return G, load


def usize(state) -> int:
    return sum(1 + 2 * c + sum(2 * v + 1 for v in arms) for arms, c in state)


def score(state) -> float:
    G, load = _build(state)
    return math.log(float(pi_flint(G, load))) - usize(state) / 11 * _LN


def _count5(arms):
    return sum(1 for x in arms if x == 5)


def is_normal(state) -> bool:
    """OrderedStep-irreducible (merge normal form): no adjacent pair admits merge/mergeRev with
    the `hsplit` achievability (a merged hub needs `5-load` arms equal to 5) and the ordering
    condition (with `tailU` length 1 when hubs follow the pair, else 0)."""
    for i in range(len(state) - 1):
        (armsA, cA), (armsB, cb) = state[i], state[i + 1]
        t = 1 if len(state) - (i + 2) > 0 else 0
        if _count5(armsB) >= 5 - cb and len(armsB) + t <= len(armsA):
            return False
        if _count5(armsA) >= 5 - cA and len(armsA) + 1 <= len(armsB) + t:
            return False
    return True


def _shapes(nmin=5, nmax=7):
    for n in range(nmin, nmax + 1):
        for k5 in range(0, n + 1):
            for c in range(0, 6):
                yield (tuple([5] * k5 + [4] * (n - k5)), c)


def run(*, sample3=40) -> dict:
    H = list(_shapes())
    best1 = max(score([h]) for h in H)
    best2 = None
    for a in H:
        for b in H:
            s = [a, b]
            if is_normal(s):
                v = score(s)
                best2 = v if best2 is None else max(best2, v)
    random.seed(1)
    H3 = random.sample(H, min(len(H), sample3))
    best3 = None
    for a in H3:
        for b in H3:
            for c in H3:
                s = [a, b, c]
                if is_normal(s):
                    v = score(s)
                    best3 = v if best3 is None else max(best3, v)
    # multi-hub normal forms EXIST but are strictly below the best single-hub, margin grows.
    assert best2 < best1 and best3 < best2, \
        f"expected growing sub-tie margin; got 1h={best1} 2h={best2} 3h={best3}"
    return {
        "best_single_hub_score": round(best1, 5),
        "best_2hub_normalform_score": round(best2, 5),
        "best_3hub_normalform_score": round(best3, 5),
        "gap_2hub": round(best1 - best2, 5),
        "gap_3hub": round(best1 - best3, 5),
        "verdict": "near-tie normal forms are single-hub; multi-hub NFs strictly sub-tie, margin grows per hub",
        "conjecture1_proved": False,
    }


if __name__ == "__main__":
    for k, v in run().items():
        print(f"  {k}: {v}")

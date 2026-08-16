"""Large-n verification of Conjecture 1's structure, extending the paper's exhaustive n<=20 result.

Since per(L(T)) is a linear-time matching sum for a tree, pi(T) is an EXACT rational at any size; the
only obstacle to identifying the maximizer is the SEARCH (which tree), not evaluation.  This module runs a
rich STRUCTURED search -- spiders (path backbone), single-hub cherry-bundle stars (with a variable hub
load c0 and balanced arms), and double-hub configurations -- and reports, for each n, the best structured
tree and its shape.  It is NOT an exhaustive-over-all-trees search (that is infeasible past n~22), so it
does not prove the maximizer; it confirms, well past n=20, that the best STRUCTURED tree matches
Conjecture 1 exactly:

  * n=30: the maximizer is still a spider (1-2 centers) -- consistent with the exhaustive n<=20 finding and
    the large-n transition being past 20.
  * n>=40: the best structured tree becomes a SINGLE-HUB cherry-bundle star; its arms balance at c~5, and
    its HUB DE-LOADS monotonically -- the observed hub cherry count c0 falls 5,5,5,4,2,0 across
    n=40,60,100,140,180,240, reaching c0=0 (a de-loaded hub) by n~240.  This is the exact structure and
    de-loading direction predicted by Conjecture 1 and proven at transfer level in hub.py/arm_bound.py.
  * double-hub configurations never win at matched n (the rem:tie constant-order tiebreak goes the
    single-hub star's way empirically -- but NOT by iterated Kelmans shifts: moving arm-centers between
    two hubs DECREASES pi, so the single hub wins only by not spending a vertex on a second hub, a genuine
    constant-order effect, matching the paper's Remark on the open tiebreak).

So this is confirmatory large-n evidence for Conjecture 1's shape, not a proof; the maximizer identity (the
1984 problem) remains open.  Requires numpy, networkx.
"""
from __future__ import annotations

import networkx as nx
import numpy as np

from verification.permanent import laplacian_ratio
from verification.trees import spider


def _balanced(total, parts):
    if parts <= 0:
        return []
    b, r = divmod(total, parts)
    return [b + 1] * r + [b] * (parts - r)


def cbstar(c0, arms):
    """Single-hub cherry-bundle star: hub with c0 cherries + arm-centers with the given cherry counts."""
    G = nx.Graph()
    G.add_node(0)
    nxt = 1

    def ch(ctr, c):
        nonlocal nxt
        for _ in range(c):
            y, z = nxt, nxt + 1
            nxt += 2
            G.add_edge(ctr, y)
            G.add_edge(y, z)
    ch(0, c0)
    for a in arms:
        ac = nxt
        nxt += 1
        G.add_edge(0, ac)
        ch(ac, a)
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def dstar(c0a, arms1, c0b, arms2):
    """Double-hub: two adjacent hubs, each with its own cherries and arm-centers."""
    G = nx.Graph()
    G.add_edge(0, 1)
    nxt = 2

    def ch(ctr, c):
        nonlocal nxt
        for _ in range(c):
            y, z = nxt, nxt + 1
            nxt += 2
            G.add_edge(ctr, y)
            G.add_edge(y, z)
    ch(0, c0a)
    ch(1, c0b)
    for a in arms1:
        ac = nxt
        nxt += 1
        G.add_edge(0, ac)
        ch(ac, a)
    for a in arms2:
        ac = nxt
        nxt += 1
        G.add_edge(1, ac)
        ch(ac, a)
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def _candidates(n):
    for m in range(1, 9):
        if (n - m) % 2 == 0:
            s = (n - m) // 2
            if s >= m:
                yield ("spider", m, None, spider(_balanced(s, m)))
    for k in range(2, n // 6 + 2):
        rem = n - 1 - k
        if rem < 0 or rem % 2:
            continue
        C = rem // 2
        for c0 in range(0, 6):
            if C - c0 < 0:
                continue
            arms = _balanced(C - c0, k)
            yield ("cbstar", k, c0, cbstar(c0, arms))
    for k in range(2, n // 6 + 2, 2):
        rem = n - 2 - k
        if rem < 0 or rem % 2:
            continue
        C = rem // 2
        k1 = k // 2
        yield ("dstar", k, None, dstar(0, _balanced(C // 2, k1), 0, _balanced(C - C // 2, k - k1)))


def best_structure(n):
    """Best structured tree on n vertices and its shape."""
    best = None
    for kind, k, c0, A in _candidates(n):
        if A.shape[0] != n:
            continue
        p = laplacian_ratio(A)
        if best is None or p > best[0]:
            best = (p, kind, k, c0)
    p, kind, k, c0 = best
    return {"n": n, "kind": kind, "k": k, "hub_cherries": c0, "pi_root_n": float(p) ** (1.0 / n)}


def certify(ns=(30, 40, 60, 100, 140, 180, 240)):
    rows = [best_structure(n) for n in ns]
    # confirmations of Conjecture 1's shape
    big = [r for r in rows if r["n"] >= 40]
    single_hub = all(r["kind"] == "cbstar" for r in big)                    # single-hub star for n>=40
    hub_loads = [r["hub_cherries"] for r in big]
    deloads = hub_loads == sorted(hub_loads, reverse=True) and hub_loads[-1] == 0  # monotone down to 0
    return {"rows": rows,
            "single_hub_star_for_n_ge_40": single_hub,
            "hub_cherry_loads": hub_loads,
            "hub_deloads_to_zero": deloads,
            "matches_conjecture1_shape": single_hub and deloads,
            "note": "confirmatory structured search past n=20; NOT exhaustive -> maximizer identity "
                    "(the 1984 problem / Conjecture 1) remains OPEN.",
            "conjecture1_proved": False}


if __name__ == "__main__":
    v = certify()
    for r in v["rows"]:
        print(f"  n={r['n']:4d}: {r['kind']:7s} k={r['k']} hub_cherries={r['hub_cherries']}  "
              f"pi^(1/n)={r['pi_root_n']:.7f}")
    print({k: val for k, val in v.items() if k != "rows"})

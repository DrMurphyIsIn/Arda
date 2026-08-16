"""RIGOROUS branch-and-bound for the finite-reduction crux: is the set of near-zero trees FINITE?

logPhi(node) = sum_i logPhi_i + e_root, with every child logPhi_i <= 0 and e_root bounded ABOVE by
    e_max = log(2) - L = log(2) - log(rhoB) = +0.4855...
(since e_root = log a(d,cr) + log(1 + z S); a(d,cr) <= a(.,0)-ish and 1+zS < 2; verified numerically
that sup e_root = e_max is not exceeded on reachable configs -- see e_root_upper_bound()).

CONSEQUENCE (lossless pruning).  Any tree T with logPhi(T) >= T0 has EVERY child subtree C_i with
    logPhi(C_i) >= T0 - e_max        (because sum_{j != i} logPhi_j <= 0).
So to enumerate ALL trees with logPhi >= T0 it SUFFICES to build them only from subtrees with
logPhi >= T0 - e_max.  We take T0 = gVal(4) - 1e-12 (the empirical non-tie sup) and prune subtrees
below PRUNE = T0 - e_max.  If the set of subtrees with logPhi >= PRUNE is FINITE (closes -- a bottom-up
fixpoint adds nothing new at some node-size), then the near-zero tree set is finite and the
finite-reduction proof skeleton is viable; we then read off sup{logPhi : non-tie} directly.

This is a rigorous search (exact Fraction cavities; the ONLY float is the final log for reporting),
NOT a proof, but it certifies finiteness/closure empirically up to the size where the fixpoint stops
growing -- much further than brute enumeration (which explodes) can reach.

HONEST OUTCOME (2026-08-11).  The LOSSLESS version explodes: E_MAX = log2 - L = +0.4855 is a LOOSE
per-node ceiling, so the retained set {logPhi >= T0 - E_MAX} ~ {logPhi >= -0.487} is large and the
forest fixpoint does NOT visibly close at reachable sizes -- the multiset-of-subtrees enumeration blows
up.  The reason is exactly the crux entanglement: e_root is near E_MAX ONLY when the children are
high-cavity (bare-leaf-like, cavity ~1), and those children have logPhi ~ -L, i.e. NOT near 0; whereas
children near 0 (ties, cavity 3/23) make e_root ~ log(26/23) = +0.123, not +0.486.  So the per-node
bound can never be simultaneously tight in e_root AND in child-nearness-to-0 -- a lossless degree bound
would need the JOINT (value-function) bound, which IS the crux.  With an explicit DEGREE CAP `deg_cap`
(a NON-lossless restriction: only trees of max out-degree <= deg_cap) the fixpoint DOES close and one
reads off sup{logPhi:non-tie} = gVal(4) over that class -- a bounded-degree confirmation of the uniform
margin, not a finiteness proof.  So: finite-reduction stays plausible but its degree bound is entangled
with the crux; the honest open target remains the three quantitative margins (D),(W),(C).
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

import general_children_crux as GC

_L = math.log(621 / 64) / 11
_rhoB = (621 / 64) ** (1 / 11)
E_MAX = math.log(2) - _L               # +0.4855..., the sup of e_root


def _cav_of(C) -> Fr:
    return GC.cav(C)


def e_root_upper_bound(nmax_children=200, cmax=40) -> dict:
    """Certify e_root <= E_MAX = log2 - L over a wide sweep, and that it is approached but not exceeded.
    e_root(cr,k,S) = log a(d,cr) + log(1 + z S), d=k+1+cr, z=3/(3d+cr); S <= k (each child cavity <=1)."""
    worst = -9.0
    for cr in range(0, cmax + 1):
        for k in range(0, nmax_children + 1):
            d = k + 1 + cr
            z = 3 / (3 * d + cr)
            S = k * 1.0                                  # cavity <= 1, extremal
            a = (1.5 ** cr * (1 + cr / (3 * d))) / _rhoB ** (1 + 2 * cr)
            e = math.log(a * z) - math.log(z / (1 + z * S))   # = log a + log(1+zS)
            worst = max(worst, e)
    return {"E_MAX": E_MAX, "sup_e_root_observed": worst, "within_bound": worst <= E_MAX + 1e-9}


def closure(T0: float | None = None, node_cap: int = 40, cher_cap: int = 8,
            deg_cap: int | None = None) -> dict:
    """Bottom-up fixpoint over subtrees with logPhi >= PRUNE = T0 - E_MAX.  Returns whether the set
    CLOSES (stops growing) and the sup of logPhi over non-tie retained trees.  `deg_cap` (optional,
    NON-lossless) restricts to trees of max out-degree <= deg_cap so the fixpoint terminates."""
    if T0 is None:
        T0 = GC.g_Val(4) - 1e-12
    PRUNE = T0 - E_MAX
    # retained[n] = list of (canonicalStr, cavity Fr, logPhi float, tree) with exactly n nodes, logPhi>=PRUNE
    retained: dict[int, list] = {}
    seen: set[str] = set()

    def add(C, n):
        s = str(C)
        if s in seen:
            return
        lp = GC.log_phi(C)
        if lp < PRUNE:
            return
        seen.add(s)
        retained.setdefault(n, []).append((s, _cav_of(C), lp, C))

    # size-1 subtrees: bare cherries (c,[]) with c<=cher_cap
    for c in range(0, cher_cap + 1):
        add((c, []), 1)

    last_growth = 1
    for n in range(2, node_cap + 1):
        # build n-node trees: root with cr cherries + a forest of retained subtrees summing to n-1 nodes
        # forests are multisets of retained subtrees (canonical: nondecreasing by key) with total nodes n-1
        # enumerate forests via DP over available retained subtree pool
        pool = [(sz, item) for sz in retained for item in retained[sz]]
        # forests of total size m as sorted tuples of pool indices; use recursion with size budget
        def forests(budget, start, depth):
            if budget == 0:
                yield []
                return
            if deg_cap is not None and depth >= deg_cap:
                return
            for idx in range(start, len(pool)):
                sz, _ = pool[idx]
                if sz <= budget:
                    for rest in forests(budget - sz, idx, depth + 1):
                        yield [idx] + rest
        for cr in range(0, cher_cap + 1):
            for fo in forests(n - 1, 0, 0):
                kids = [pool[i][1][3] for i in fo]
                add((cr, kids), n)
        if n in retained and retained[n]:
            last_growth = n
    # did it close? (no retained trees beyond last_growth up to node_cap)
    closed = last_growth < node_cap
    # sup over non-tie retained
    nontie = [(lp, s) for lst in retained.values() for (s, m, lp, C) in lst if abs(lp) > 1e-9]
    ties = [(lp, s) for lst in retained.values() for (s, m, lp, C) in lst if abs(lp) <= 1e-9]
    nontie.sort(reverse=True)
    total = sum(len(v) for v in retained.values())
    return {
        "T0": T0, "PRUNE_threshold": PRUNE, "E_MAX": E_MAX,
        "retained_total": total,
        "retained_by_size": {n: len(v) for n, v in sorted(retained.items())},
        "last_size_with_retained": last_growth,
        "node_cap": node_cap,
        "CLOSED_finite": closed,
        "n_tie_retained": len(ties),
        "sup_nontie_logPhi": (nontie[0][0] if nontie else None),
        "argsup_nontie": (nontie[0][1] if nontie else None),
        "gVal4": GC.g_Val(4),
    }


def certify() -> dict:
    eb = e_root_upper_bound()
    cl = closure()
    return {
        "e_root_bound": eb,
        "closure": cl,
        "near_zero_set_finite": cl["CLOSED_finite"],
        "sup_nontie_equals_gVal4": (cl["sup_nontie_logPhi"] is not None
                                    and abs(cl["sup_nontie_logPhi"] - cl["gVal4"]) < 1e-9),
    }


if __name__ == "__main__":
    import json, sys
    ncap = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    ccap = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    out = {"e_root_bound": e_root_upper_bound(), "closure": closure(node_cap=ncap, cher_cap=ccap)}
    out["near_zero_set_finite"] = out["closure"]["CLOSED_finite"]
    print(json.dumps(out, indent=2, default=str))

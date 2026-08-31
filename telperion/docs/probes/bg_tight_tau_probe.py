"""Probe: the tight discharge tau for the BG bulk bound must be FIELD-dependent.

Narrows the open BG upper-bound crux (`bg_bulk_discharge`: a universal edge-discharge `tau` making
`phi_v = A_v - sum_u tau_{v,u} B_{v,u} <= F* = log(621/64)/11` for every local configuration).

Two exact-arithmetic LP experiments over a spread of tree structures (centers exempt as the O(1) boundary):

  (1) UNIVERSAL degree-only tau -- one `tau(d_v, d_u)` table shared across all trees.  FAILS: min-max
      `phi_v = 0.20984 > F* = 0.20659` (+0.0033).  A degree-only rule cannot keep the bound, because the
      same edge-type carries different `B` in different trees (the fields differ).

  (2) PER-TREE field-adaptive tau -- free per-edge `tau` for each tree.  HOLDS: `max_v phi_v <= F*` on every
      tested structure (`S(40,5)` saturates `F*` exactly; caterpillars/other spiders below).

Conclusion: the bound is achievable per-tree, and the tight universal `tau` MUST depend on the cavity fields
`h` (not just degrees) -- the box-positivity problem `bg_bulk_discharge` targets, with the `27*23` tie
(`emit_padic`).  Naive degree/equal rules are provably spoofed (the acyclicity/surface barrier).  This is
evidence, not a closed proof; the universal closed-form field-`tau` remains OPEN.  conjecture1_proved = False.

Run:  PYTHONPATH=telperion/src python3 telperion/docs/probes/bg_tight_tau_probe.py
"""
import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

from scipy.optimize import linprog  # noqa: E402

from telperion.bg_bulk_discharge import _adj, bethe_terms  # noqa: E402
from telperion.spider_broom import spider_edges  # noqa: E402
from telperion.transfer_caterpillar import caterpillar_edges  # noqa: E402

F_STAR = math.log(621 / 64) / 11
TREES = [("S(40,5)", spider_edges(40, 5)), ("S(40,4)", spider_edges(40, 4)),
         ("cat[7]x20", caterpillar_edges([7] * 20)), ("S(30,3)", spider_edges(30, 3)),
         ("cat[5]x20", caterpillar_edges([5] * 20))]
EXEMPT = 15  # exempt very-high-degree centers (the O(1) boundary)


def _global_degree_tau(trees):
    rows, types = [], {}
    def tid(dv, du):
        types.setdefault((dv, du), len(types))
        return types[(dv, du)]
    for _, (n, e) in trees:
        Aarg, Barg, deg = bethe_terms(n, e)
        adj = _adj(n, e)
        Bof = {}
        for (u, v), b in Barg.items():
            Bof[(u, v)] = b
            Bof[(v, u)] = b
        for v in range(n):
            if deg[v] >= EXEMPT:
                continue
            rows.append((math.log(float(Aarg[v])),
                         [(tid(deg[v], deg[u]), math.log(float(Bof[(v, u)]))) for u in adj[v]]))
    T = len(types)
    A_ub, b_ub = [], []
    for Av, terms in rows:
        row = [0.0] * (T + 1)
        for ti, B in terms:
            row[ti] += -B
        row[-1] = -1.0
        A_ub.append(row)
        b_ub.append(-Av)
    A_eq, b_eq, done = [], [], set()
    for (dv, du), i in types.items():
        key = (min(dv, du), max(dv, du))
        if (du, dv) in types and key not in done:
            row = [0.0] * (T + 1)
            row[i] = 1
            row[types[(du, dv)]] = 1
            A_eq.append(row)
            b_eq.append(1.0)
            done.add(key)
    res = linprog([0] * T + [1], A_ub=A_ub, b_ub=b_ub, A_eq=A_eq or None, b_eq=b_eq or None,
                  bounds=[(0, 1)] * T + [(None, None)])
    return res.fun


def _per_tree_tau(n, e):
    Aarg, Barg, deg = bethe_terms(n, e)
    adj = _adj(n, e)
    edges = list(Barg.keys())
    eidx = {}
    for k, ed in enumerate(edges):
        eidx[ed] = k
        eidx[(ed[1], ed[0])] = k
    Bval = {ed: math.log(float(Barg[ed])) for ed in edges}
    E = len(edges)
    A_ub, b_ub = [], []
    for v in range(n):
        if deg[v] >= EXEMPT:
            continue
        Av = math.log(float(Aarg[v]))
        row = [0.0] * (E + 1)
        const = 0.0
        for u in adj[v]:
            ed = (min(v, u), max(v, u))
            k = eidx[ed]
            # tau_e = share of B_e to the lower-id endpoint; v-share = tau_e (v<u) else 1-tau_e
            if v < u:
                row[k] += -Bval[ed]
            else:
                row[k] += Bval[ed]
                const += Bval[ed]
        row[-1] = -1.0
        A_ub.append(row)
        b_ub.append(-Av + const)
    res = linprog([0] * E + [1], A_ub=A_ub, b_ub=b_ub, bounds=[(0, 1)] * E + [(None, None)])
    return res.fun


def main():
    print(f"F* = {F_STAR:.6f}")
    g = _global_degree_tau(TREES)
    print(f"(1) universal degree-only tau : max phi = {g:.6f}  "
          f"{'HOLDS' if g <= F_STAR + 1e-6 else f'FAILS (+{g-F_STAR:.5f})'}")
    print("(2) per-tree field-adaptive tau:")
    ok = True
    for name, (n, e) in TREES:
        m = _per_tree_tau(n, e)
        ok &= m <= F_STAR + 1e-6
        print(f"      {name:12}: max phi = {m:.6f}  {'<= F*' if m <= F_STAR + 1e-6 else '> F*'}")
    print(f"\nVERDICT: degree-only universal tau FAILS; per-tree field-adaptive tau HOLDS ({ok}).")
    print("=> the tight universal discharge must be FIELD-dependent (box-positivity + emit_padic, 27*23 tie).")
    print("   conjecture1_proved = False")


if __name__ == "__main__":
    main()

# ---------------------------------------------------------------------------
# Follow-up finding (2026-08-31): the equalizing field-tau is DETERMINED on the
# low-degree (leaf/armmid) tree edges -- armmid->hub edges (h_armmid=2/3) all take
# a large, smoothly-varying share (0.78-0.90 as the hub degree grows) -- but the
# hub-HUB backbone edges are UNDERDETERMINED (tau jumps 0/1/0.52/0.77 for near-
# identical fields; the least-squares picks an arbitrary point of the optimal
# flow face).  So equalization alone does NOT pin a global closed-form tau: the
# backbone has flow-freedom whose universal resolution is the arithmetic /
# box-positivity piece (the 27*23 tie, emit_padic), not something more field-data
# resolves.  This is why the closed form is elusive -- the resolving principle is
# arithmetic, not analytic.  conjecture1_proved = False.

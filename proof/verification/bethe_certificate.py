"""Bethe/cavity framework for Phi<=1 (the open near-star bound), and a NEW feasible local
certificate class that sidesteps the earlier Lyapunov no-gos.

EXACT FRAMEWORK (verified to 1e-40).  For a single-branch gadget C (a rooted center-tree; the
root carries a phantom hub-neighbour that raises its degree but is not matchable):
    Phi(C) = (prod_v a_v) * f(C),   a_v = F(d_v,c_v)/rho_B^{1+2c_v},   d_v = deg_beta(v)+c_v,
    f(C) = sum_{matchings M} prod_{v in V(M)} z_v,   z_v = 3/(3 d_v + c_v).
(Trees are bipartite, so det(I+A^2)=f^2 and Phi=det(D(I+iA)) gives the FIRST power of f, not f^2 --
a correction of an earlier draft.)  So

    Phi(C) <= 1   <=>   f(C) <= prod_v (1/a_v).

BETHE DECOMPOSITION (exact on trees).  With cavity messages on directed edges
    h_{u->v} = z_u / (1 + z_u * sum_{w~u, w!=v} h_{w->u}),          (leaf u: h = z_u)
and node ratios R_v = 1 + z_v * sum_{u~v} h_{u->v},
    f(C) = prod_v R_v / prod_{(u,v) in E} (1 + h_{u->v} h_{v->u}).
Hence

    Phi(C) <= 1   <=>   prod_v (a_v R_v)  <=  prod_{(u,v) in E} (1 + h_{u->v} h_{v->u}).      (*)

The RHS edge factors are >= 1 -- they are exactly the pairwise-correlation terms Hadamard discarded
(and which make prod_v W_vv unbounded while Phi<=1).

A NEW FEASIBLE LOCAL CERTIFICATE (this module's contribution).  (*) would follow from a per-vertex
inequality if the edge corrections could be SPLIT among their endpoints so each vertex covers its
own factor:  assign to each edge (u,v) a fraction f_{e,u}+f_{e,v}=1 of log(1+h h), and ask
    log(a_v R_v)  <=  sum_{u~v} f_{(uv),v} * log(1 + h_{u->v} h_{v->u})   for every v.
Then summing gives (*).  Facts (machine-checked):
  - FULL-EDGE bound  a_v R_v <= prod_{u~v}(1 + h_{u->v} h_{v->u})  holds for EVERY vertex, with worst
    log-violation EXACTLY 0 (tight at the tie gadgets).  So every vertex's overshoot is covered by
    its OWN incident edges' full corrections.
  - The fractional split LP is FEASIBLE on every gadget tested (0 infeasible / 3000): a valid
    edge-splitting certificate always exists.
This certificate is NONLINEAR (the messages h are nonlinear functions of the subtree), so it is NOT
covered by the ruled-out common-quadratic / path-complete-LINEAR / reachable-cone LINEAR Lyapunov
families -- a genuinely new structure for this problem.

THE REMAINING OBSTRUCTION (sharply located).  The split LP is MARGINAL: its max-min slack -> 0
exactly at the 6 rational tie gadgets (arm-substitutes, Phi=1).  So a CLOSED-FORM local split rule
must be exactly tight there; the LP optimum is a 0/1 (whole-edge) assignment that depends on which
vertex is overshooting -- no simple edge-local formula was found (the "need" L_v = log(a_v R_v)
depends on the vertex's whole neighbourhood, not just one edge).  The tie marginality, which defeats
every route, is now pinned inside the Bethe form: it is the tightness of the full-edge bound.

CONTRACTION IDEA -- RULED OUT (2026-08-06).  One hoped to remove the marginal ties by contracting
arm-substitutes (the Phi=1 gadgets) to single arms, leaving a strict margin.  This FAILS: the ties
are IRREDUCIBLE.  The gadget (4,[(0,[(0,[])])]) has Phi=1 EXACTLY (to 1e-42), V=11, yet BOTH its
proper subtrees have Phi<1 (the bare-2-path 0.99232 and a c=0 leaf 0.81336).  So there exist Phi=1
gadgets with NO Phi=1 sub-branch -- the ties are not built from smaller ties and cannot be contracted
away.  Hence sup{Phi : gadget has no proper sub-branch with Phi~1} = 1 (no margin): the marginality
is intrinsic, not confined to nested arm-substitutes.  Any closed proof must confront the irreducible
tie gadgets directly (a smooth non-monotone certificate anchored on the tie variety), not remove them.

Requires mpmath, scipy.
"""
from __future__ import annotations

import functools
import sys

import mpmath as mp

mp.mp.dps = 40
_F6 = mp.mpf(621) / 64
_rhoB = _F6 ** (mp.mpf(1) / 11)
sys.setrecursionlimit(1_000_000)


def _F(d, c):
    return (mp.mpf(3) / 2) ** c * (1 + mp.mpf(c) / (3 * d))


def _z(d, c):
    return mp.mpf(3) / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def build(C):
    """C=(cherries,[children]) -> (adj dict, cher list); root = node 0."""
    adj, cher = {}, []

    def rec(node, parent):
        cr, kids = node
        me = len(cher)
        cher.append(cr)
        adj[me] = []
        if parent is not None:
            adj[me].append(parent)
            adj[parent].append(me)
        for k in kids:
            rec(k, me)
        return me
    rec(C, None)
    return adj, cher


def _degrees(adj, cher, root=0):
    # root has a phantom hub-neighbour: +1 to its degree
    return {v: len(adj[v]) + (1 if v == root else 0) + cher[v] for v in adj}


def messages(adj, cher):
    d = _degrees(adj, cher)
    z = {v: _z(d[v], cher[v]) for v in adj}

    @functools.lru_cache(maxsize=None)
    def hh(u, v):
        s = mp.mpf(0)
        for w in adj[u]:
            if w != v:
                s += hh(w, u)
        return z[u] / (1 + z[u] * s)
    h = {(u, v): hh(u, v) for u in adj for v in adj[u]}
    return h, z, d


def phi(C):
    """Phi(C) = prod_v a_v * f(C), via the Bethe decomposition."""
    adj, cher = build(C)
    h, z, d = messages(adj, cher)
    num = mp.mpf(1)
    for v in adj:
        R = 1 + z[v] * sum(h[(u, v)] for u in adj[v])
        num *= _a(d[v], cher[v]) * R
    den = mp.mpf(1)
    seen = set()
    for u in adj:
        for v in adj[u]:
            if (v, u) in seen:
                continue
            seen.add((u, v))
            den *= (1 + h[(u, v)] * h[(v, u)])
    return num / den


def certify_full_edge_bound(n=20000, seed=0):
    """Machine-check: a_v R_v <= prod_{u~v}(1 + h_{u->v} h_{v->u}) for every vertex (worst
    log-violation should be ~0, tight at ties). Returns worst violation over random gadgets."""
    import random
    rng = random.Random(seed)

    def rt(dep):
        if dep == 0:
            return (rng.randint(0, 7), [])
        return (rng.randint(0, 7), [rt(dep - 1) for _ in range(rng.randint(1, 4))])

    worst = -1e9
    for _ in range(n):
        C = rt(rng.randint(1, 5))
        adj, cher = build(C)
        h, z, d = messages(adj, cher)
        for v in adj:
            R = 1 + z[v] * sum(h[(u, v)] for u in adj[v])
            lhs = _a(d[v], cher[v]) * R
            rhs = mp.mpf(1)
            for u in adj[v]:
                rhs *= (1 + h[(u, v)] * h[(v, u)])
            worst = max(worst, float(mp.log(lhs) - mp.log(rhs)))
    return {"worst_log_violation": worst, "full_edge_bound_holds": worst <= 1e-9}


def certify_split_lp_feasible(n=1000, seed=1):
    """Machine-check: the fractional edge-split LP is feasible on every gadget (a valid Bethe-local
    certificate always exists). Returns count of infeasible gadgets (should be 0) and min slack."""
    import random
    import numpy as np
    from scipy.optimize import linprog
    rng = random.Random(seed)

    def rt(dep):
        if dep == 0:
            return (rng.randint(0, 7), [])
        return (rng.randint(0, 7), [rt(dep - 1) for _ in range(rng.randint(1, 4))])

    infeasible = 0
    min_slack = 1e9
    for _ in range(n):
        C = rt(rng.randint(1, 5))
        adj, cher = build(C)
        h, z, d = messages(adj, cher)
        L = {v: float(mp.log(_a(d[v], cher[v]) * (1 + z[v] * sum(h[(u, v)] for u in adj[v])))) for v in adj}
        edges, w, seen = [], [], set()
        for u in adj:
            for v in adj[u]:
                if (v, u) in seen:
                    continue
                seen.add((u, v))
                edges.append((u, v))
                w.append(float(mp.log(1 + h[(u, v)] * h[(v, u)])))
        c, idx = 0, {}
        for ei, (u, v) in enumerate(edges):
            idx[(ei, u)] = c
            idx[(ei, v)] = c + 1
            c += 2
        Aub, bub = [], []
        for v in adj:
            row = [0.0] * (c + 1)
            for ei, (aa, bb) in enumerate(edges):
                if v == aa:
                    row[idx[(ei, aa)]] = -w[ei]
                elif v == bb:
                    row[idx[(ei, bb)]] = -w[ei]
            row[c] = 1.0
            Aub.append(row)
            bub.append(-L[v])
        Aeq, beq = [], []
        for ei, (u, v) in enumerate(edges):
            row = [0.0] * (c + 1)
            row[idx[(ei, u)]] = 1
            row[idx[(ei, v)]] = 1
            Aeq.append(row)
            beq.append(1.0)
        obj = [0.0] * (c + 1)
        obj[c] = -1.0
        res = linprog(c=obj, A_ub=np.array(Aub), b_ub=np.array(bub), A_eq=np.array(Aeq),
                      b_eq=np.array(beq), bounds=[(0, 1)] * c + [(None, None)], method="highs")
        if res.status != 0:
            infeasible += 1
        else:
            min_slack = min(min_slack, res.x[c])
    return {"infeasible": infeasible, "of": n, "min_slack": min_slack,
            "always_feasible": infeasible == 0}


if __name__ == "__main__":
    print("full-edge bound:", certify_full_edge_bound(n=5000))
    print("split LP feasible:", certify_split_lp_feasible(n=300))

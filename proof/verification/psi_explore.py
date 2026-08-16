"""Exploration: controlling the degree-activity change in Psi under a hubward
(Kelmans / generalized-tree-shift) step.

Setup (from the paper's factorization):
    pi(beta[c]) = prod_v F(D_v) * Psi(beta),
    Psi(beta)   = sum_{matchings M of beta} prod_{v in V(M)} z_v,
    z_v = 3 / (3*deg_beta(v) + 4c)          (activity, DECREASING in degree)

A hubward step beta -> beta' moves mass toward a higher-degree vertex (toward the
star). We KNOW prod_F increases (Schur/log-convexity, proven). Psi is the
degree-weighted matching polynomial; the step changes two degrees (hub +1, donor
-1), so activities move: z_hub DOWN, z_donor UP.

We need   prod_F(beta') / prod_F(beta)  >=  Psi(beta) / Psi(beta')   (both >= 1).

This script decomposes the Psi change through an intermediate with FROZEN
activities to separate the topology effect (where Csikvari's machinery is native)
from the activity-coupling effect (the open part):

    Psi(beta; z^beta)  --topology-->  Psi(beta'; z^beta)  --activity-->  Psi(beta'; z^beta')

where z^beta uses beta's degrees and z^beta' uses beta''s degrees, under the
natural vertex identification (only hub & donor change degree in a Kelmans step).
"""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr

import networkx as nx


# ---------------------------------------------------------------- activities
def activity(deg: int, cc) -> Fr:
    """z_v = 3 / (3*deg + 4c)  with cc an integer (exact rational)."""
    return Fr(3, 3 * deg + 4 * cc)


def activities_from_graph(G: nx.Graph, cc) -> dict:
    return {v: activity(G.degree(v), cc) for v in G.nodes()}


# ---------------------------------------------------------- weighted matching
def psi_weighted(G: nx.Graph, z: dict) -> Fr:
    """Degree-weighted matching polynomial: sum over matchings M of
    prod_{v matched} z[v].  Exact rational.  Edge-recursion."""
    edges = list(G.edges())

    def rec(i: int, used: frozenset) -> Fr:
        if i == len(edges):
            return Fr(1)
        s = rec(i + 1, used)
        u, v = edges[i]
        if u in used or v in used:
            return s
        return s + z[u] * z[v] * rec(i + 1, used | {u, v})

    return rec(0, frozenset())


def F_factor(deg: int, cc) -> Fr:
    """F(D) with D = deg + c;  F(D) = (3/2)^c + (c/(2D))*(3/2)^(c-1)."""
    D = deg + cc
    return Fr(3, 2) ** cc + Fr(cc, 2 * D) * Fr(3, 2) ** (cc - 1)


def prod_F(G: nx.Graph, cc) -> Fr:
    p = Fr(1)
    for v in G.nodes():
        p *= F_factor(G.degree(v), cc)
    return p


def pi_of(G: nx.Graph, cc) -> Fr:
    return prod_F(G, cc) * psi_weighted(G, activities_from_graph(G, cc))


# --------------------------------------------------------------- Kelmans step
def kelmans_step(G: nx.Graph, a, b):
    """Kelmans transformation toward hub `a`: every neighbour w of b with
    w != a and w not on the a-side is detached from b and attached to a.
    Concretely: along the tree, root at a; for the child subtree hanging off b
    (away from a), move b's *other* branches onto a.  Returns a NEW graph, or
    None if the move is degenerate (no branch to move / disconnects)."""
    if not G.has_edge(a, b):
        # only handle the adjacent (k=2 Kelmans / covering) case here
        return None
    H = G.copy()
    # neighbours of b other than a become neighbours of a
    movers = [w for w in list(G.neighbors(b)) if w != a]
    if not movers:
        return None
    for w in movers:
        H.remove_edge(b, w)
        H.add_edge(a, w)
    if not nx.is_tree(H):
        return None
    return H


def all_trees(n: int):
    """All non-isomorphic trees on n nodes."""
    return list(nx.nonisomorphic_trees(n))


# ------------------------------------------------------------------ explore
def explore(n: int, cc: int, verbose: bool = True):
    """For every tree beta on n nodes and every adjacent Kelmans step that
    STRICTLY increases pi, report the F-gain, the Psi-loss, and the
    topology/activity decomposition of the Psi change."""
    rows = []
    for beta in all_trees(n):
        for a, b in itertools.permutations(beta.nodes(), 2):
            bp = kelmans_step(beta, a, b)
            if bp is None:
                continue
            pi0, pi1 = pi_of(beta, cc), pi_of(bp, cc)
            if pi1 <= pi0:
                continue  # only hubward (pi-increasing) steps
            # activities
            zb = activities_from_graph(beta, cc)     # z^beta
            zbp = activities_from_graph(bp, cc)       # z^beta'
            Psi_b = psi_weighted(beta, zb)
            Psi_bp = psi_weighted(bp, zbp)
            # intermediate: beta' topology, beta activities (need identification)
            # vertices are the SAME labels (kelmans_step preserved labels), so
            # z^beta is directly usable on bp for the frozen-activity value.
            Psi_mid = psi_weighted(bp, zb)
            gainF = prod_F(bp, cc) / prod_F(beta, cc)
            lossPsi = Psi_b / Psi_bp
            topo_ratio = Psi_b / Psi_mid       # topology part of the loss
            act_ratio = Psi_mid / Psi_bp       # activity part of the loss
            rows.append(
                dict(
                    n=n,
                    beta=tuple(sorted((beta.degree(v) for v in beta.nodes()), reverse=True)),
                    bp=tuple(sorted((bp.degree(v) for v in bp.nodes()), reverse=True)),
                    gainF=gainF,
                    lossPsi=lossPsi,
                    topo=topo_ratio,
                    act=act_ratio,
                )
            )
    if verbose:
        print(f"=== n={n}, c={cc}: {len(rows)} pi-increasing adjacent Kelmans steps ===")
        print(f"{'beta deg':>18} -> {'bp deg':>18} | {'gainF':>8} {'lossPsi':>8} "
              f"{'topo':>8} {'act':>8}  {'act>1?':>6}")
        act_ge1 = act_le1 = 0
        for r in rows:
            ag = r["act"] >= 1
            act_ge1 += int(ag)
            act_le1 += int(r["act"] <= 1)
            print(f"{str(r['beta']):>18} -> {str(r['bp']):>18} | "
                  f"{float(r['gainF']):8.4f} {float(r['lossPsi']):8.4f} "
                  f"{float(r['topo']):8.4f} {float(r['act']):8.4f}  {str(ag):>6}")
        print(f"\nactivity part >= 1 (reinforces loss, HARDER): {act_ge1}/{len(rows)}")
        print(f"activity part <= 1 (opposes loss, HELPS):     {act_le1}/{len(rows)}")
        # the crux inequality check
        allok = all(r["gainF"] >= r["lossPsi"] for r in rows)
        print(f"gainF >= lossPsi on every step: {allok}")
    return rows


def summarize(n: int, cc: int):
    """Quiet: aggregate sign-definiteness of both decomposition orders + the
    goal inequality.  Order A: topology-then-activity.  Order B: activity-then-
    topology (freeze topology at beta, change activities first)."""
    tot = goal_ok = 0
    topoA_ge1 = actA_ge1 = actB_ge1 = topoB_ge1 = 0
    lossPsi_ge1 = 0
    for beta in all_trees(n):
        for a, b in itertools.permutations(beta.nodes(), 2):
            bp = kelmans_step(beta, a, b)
            if bp is None:
                continue
            if pi_of(bp, cc) <= pi_of(beta, cc):
                continue
            tot += 1
            zb = activities_from_graph(beta, cc)
            zbp = activities_from_graph(bp, cc)
            Psi_b = psi_weighted(beta, zb)
            Psi_bp = psi_weighted(bp, zbp)
            gainF = prod_F(bp, cc) / prod_F(beta, cc)
            lossPsi = Psi_b / Psi_bp
            goal_ok += int(gainF >= lossPsi)
            lossPsi_ge1 += int(lossPsi >= 1)
            # order A: beta(zb) -> bp(zb) -> bp(zbp)
            mid_A = psi_weighted(bp, zb)
            topoA_ge1 += int(Psi_b / mid_A >= 1)
            actA_ge1 += int(mid_A / Psi_bp >= 1)
            # order B: beta(zb) -> beta(zbp) -> bp(zbp)
            mid_B = psi_weighted(beta, zbp)
            actB_ge1 += int(Psi_b / mid_B >= 1)
            topoB_ge1 += int(mid_B / Psi_bp >= 1)
    print(f"n={n} c={cc}: steps={tot:3d} | goal(gainF>=lossPsi)={goal_ok}/{tot} "
          f"| lossPsi>=1={lossPsi_ge1}/{tot} "
          f"|| A[topo>=1={topoA_ge1}/{tot} act>=1={actA_ge1}/{tot}] "
          f"B[act>=1={actB_ge1}/{tot} topo>=1={topoB_ge1}/{tot}]")


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "detail":
        for n in (4, 5, 6, 7):
            explore(n, cc=3)
            print()
    else:
        print("=== sign-definiteness of each decomposition half ===")
        for cc in (3, 5, 10):
            for n in (4, 5, 6, 7, 8):
                summarize(n, cc)
            print()

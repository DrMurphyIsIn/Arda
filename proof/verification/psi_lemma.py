"""Degree-activity control in the matching factor Psi -- proven pieces.

Context.  pi(beta[c]) = prod_v F(D_v) * Psi(beta), with
    Psi(beta) = sum_{matchings M of beta} prod_{v in V(M)} z_v,
    z_v = 3 / (3*deg_beta(v) + 4c)      (activity, DECREASING in degree).
The prod_F factor is provably star-maximal (Schur / log-convexity).  The open
step is that the whole ratio pi increases under a hubward (Kelmans / GTS) move.

This module records what the exploration in psi_explore.py / psi_fixedweight.py
established RIGOROUSLY (exact rationals, checked over all trees up to a size):

(1) TOPOLOGY LEMMA (proven).  For the adjacent Kelmans step beta -> beta'
    (a ~ b; every neighbour of b except a is moved to a, so a becomes the hub
    and b a leaf), and ANY fixed nonnegative vertex weights w,

        Psi(beta; w) - Psi(beta'; w) = MS * ( FQ*(w_b - w_a) + w_a*w_b*MQ ),

    where FQ, MQ (resp. FS, MS) are the matching quantities of a's non-b
    subtrees (resp. b's non-a subtrees), all >= 0.  Hence w_a <= w_b implies
    Psi(beta; w) >= Psi(beta'; w).  The TARGET activities z^{beta'} satisfy
    w_a <= w_b (the hub a carries the smallest activity, the leaf b a large
    one), so with the target activities Psi is star-minimal under the step.

    Sharpness: for weights NOT nonincreasing in the target degree the
    conclusion fails (psi_fixedweight.py: >5000 counterexamples).  So this is
    a genuinely degree-COUPLED monotonicity, not a weight-free corollary of
    Csikvari's GTS theory.

(2) PI-LEVEL BILINEAR FORM (proven identity; obstruction localized, NOT closed).
    Because only a, b change degree, the environment quantities FQ,MQ,FS,MS are
    identical in beta and beta'.  The full ratio difference is the bilinear form

        pi(beta') - pi(beta) = P * [ c1*FS*FQ + c2*MQ*FS + c3*MS*FQ + c4*MQ*MS ]

    with P > 0 and coefficients explicit in (deg_a, deg_b, c).  Empirically over
    all trees up to 8 nodes: c1 >= 0 (leading), c2 < 0, c4 < 0 always, c3 mixed.
    The step's positivity is therefore a genuine multi-term balance controlled by
    tree-realizability relations among FQ,MQ,FS,MS -- it does not reduce to
    coefficientwise nonnegativity.  This is the precise, still-open residual.

Everything below is exact-rational and self-checking.
"""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr

import networkx as nx

try:  # dual-mode: runnable as a script from this dir, importable as a package module
    from psi_explore import (
        activities_from_graph,
        all_trees,
        kelmans_step,
        psi_weighted,
        pi_of,
        F_factor,
    )
except ImportError:  # pragma: no cover
    from verification.psi_explore import (
        activities_from_graph,
        all_trees,
        kelmans_step,
        psi_weighted,
        pi_of,
        F_factor,
    )


def _environment_quantities(beta: nx.Graph, a, b, w: dict):
    """Return (FQ, MQ, FS, MS) for the adjacent Kelmans step a<-b, computed with
    weights w.  a's non-b side = Q; b's non-a side = S (movers)."""
    others = [x for x in beta.nodes() if x != a]
    comp_b = nx.node_connected_component(beta.subgraph(others), b)
    Ra = [x for x in beta.nodes() if x != a and x not in comp_b]   # Q forest
    movers = [x for x in comp_b if x != b]                         # S forest
    FQ = psi_weighted(beta.subgraph(Ra), w)
    FS = psi_weighted(beta.subgraph(movers), w)
    MQ = (psi_weighted(beta.subgraph([a] + Ra), w) - FQ) / w[a]
    MS = (psi_weighted(beta.subgraph([b] + movers), w) - FS) / w[b]
    return FQ, MQ, FS, MS


def certify_topology_lemma(n_max: int = 8, weight_trials: int = 6, seed: int = 0) -> bool:
    """Verify the exact TOPOLOGY-LEMMA identity for every adjacent Kelmans step on
    every tree with <= n_max nodes, over degree-activities AND random weights."""
    import random

    rng = random.Random(seed)
    for n in range(4, n_max + 1):
        for beta in all_trees(n):
            for a, b in itertools.permutations(beta.nodes(), 2):
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                weight_sets = [activities_from_graph(beta, 3)]
                for _ in range(weight_trials):
                    weight_sets.append(
                        {v: Fr(rng.randint(1, 15), rng.randint(1, 15)) for v in beta.nodes()}
                    )
                for w in weight_sets:
                    FQ, MQ, FS, MS = _environment_quantities(beta, a, b, w)
                    lhs = psi_weighted(beta, w) - psi_weighted(bp, w)
                    rhs = MS * (FQ * (w[b] - w[a]) + w[a] * w[b] * MQ)
                    if lhs != rhs:
                        return False
                    # sufficient condition: w_a <= w_b => Psi(beta) >= Psi(beta')
                    if w[a] <= w[b] and lhs < 0:
                        return False
    return True


def certify_pi_bilinear_form(n_max: int = 8, cc: int = 3) -> dict:
    """Verify the exact PI-LEVEL bilinear identity for every adjacent Kelmans step,
    and return the observed coefficient-sign census.  Returns a dict with keys
    'exact' (all identities held), and 'c1neg','c2neg','c3neg','c4neg','steps'."""
    census = dict(exact=True, steps=0, c1neg=0, c2neg=0, c3neg=0, c4neg=0,
                  pi_increasing=0)
    for n in range(4, n_max + 1):
        for beta in all_trees(n):
            for a, b in itertools.permutations(beta.nodes(), 2):
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                zb, zbp = activities_from_graph(beta, cc), activities_from_graph(bp, cc)
                za_b, zb_b, za_p, zb_p = zb[a], zb[b], zbp[a], zbp[b]
                w = {v: zb[v] for v in beta.nodes()}   # env activities (a,b terms handled explicitly)
                FQ, MQ, FS, MS = _environment_quantities(beta, a, b, w)
                Fa_b, Fb_b = F_factor(beta.degree(a), cc), F_factor(beta.degree(b), cc)
                Fa_p, Fb_p = F_factor(bp.degree(a), cc), F_factor(bp.degree(b), cc)
                P = Fr(1)
                for v in beta.nodes():
                    if v not in (a, b):
                        P *= F_factor(beta.degree(v), cc)
                c1 = Fa_p * Fb_p * (1 + za_p * zb_p) - Fa_b * Fb_b * (1 + za_b * zb_b)
                c2 = Fa_p * Fb_p * za_p - Fa_b * Fb_b * za_b
                c3 = Fa_p * Fb_p * za_p - Fa_b * Fb_b * zb_b
                c4 = -Fa_b * Fb_b * za_b * zb_b
                rhs = P * (c1 * FS * FQ + c2 * MQ * FS + c3 * MS * FQ + c4 * MQ * MS)
                lhs = pi_of(bp, cc) - pi_of(beta, cc)
                census["steps"] += 1
                census["exact"] = census["exact"] and (lhs == rhs)
                census["c1neg"] += int(c1 < 0)
                census["c2neg"] += int(c2 < 0)
                census["c3neg"] += int(c3 < 0)
                census["c4neg"] += int(c4 < 0)
                census["pi_increasing"] += int(lhs >= 0)
    return census


if __name__ == "__main__":
    print("topology lemma exact identity + sufficient condition:",
          certify_topology_lemma())
    cen = certify_pi_bilinear_form()
    print("pi bilinear form:", cen)
    assert cen["exact"]
    assert cen["pi_increasing"] == cen["steps"], "pi should increase on every Kelmans step"

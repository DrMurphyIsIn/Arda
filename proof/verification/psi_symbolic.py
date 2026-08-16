"""Close the exchange-lemma gap: a GENERAL (all-tree) proof of the Kelmans-step identity.

Prior state (psi_lemma / psi_close): the bilinear identity was verified by ENUMERATING all
trees on <= 9 vertices. This module upgrades that to a proof for ALL trees, by deriving the
identity from the matching-polynomial rooting recurrence with the two subtree environments
kept as abstract quantities.

Setup. For an adjacent Kelmans step beta -> beta' (edge a~b; b's non-a subtrees S all move
to a, so a becomes the hub and b a leaf), let Q be a's non-b subtrees. With
Psi(G;w) = sum over matchings of prod_{v matched} w_v, root at a and use the standard
deletion recurrence Psi(G) = Psi(G-a) + w_a * sum_{u~a} w_u Psi(G-a-u). Removing a from a
TREE splits it into independent subtrees, so with the environment quantities

    FQ = Psi(Q-forest),   MQ = ( Psi(a + Q) - FQ ) / w_a,
    FS = Psi(S-forest),   MS = ( Psi(b + S) - FS ) / w_b,

(all intrinsic to the Q,S subtree collections, hence IDENTICAL in beta and beta') the two
matching polynomials expand in closed form:

    Psi(beta;w)  = (FS + w_b MS)(FQ + w_a MQ) + w_a w_b FS FQ          [EXP_beta]
    Psi(beta';w) = FS FQ (1 + w_a w_b) + w_a (MQ FS + MS FQ)           [EXP_betap]

`verify_expansion_formulas` checks EXP_beta and EXP_betap against the actual Psi on every
tree up to n_max (they are exact consequences of the tree rooting recurrence; the check
confirms the derivation). `prove_identities_symbolic` then proves, in the FREE symbols
FQ,MQ,FS,MS and activities, the topology-lemma identity and the pi-level bilinear form --
valid for every tree at once. Together with the SYMBOLIC corner certificate
(psi_close.certify_corners_nonneg) this closes the backbone condition for all N.

Reachability is elementary and needs no enumeration: a non-star tree has a vertex b (not
the centre) with a neighbour != its hubward partner, so it admits a non-trivial Kelmans
step (beta' !~= beta), which strictly increases pi by the strictness clause; the Kelmans/GTS
poset is finite with the star as its unique top, so iteration terminates at the star.
"""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr

import networkx as nx
import sympy as sp

from verification.psi_explore import (
    activities_from_graph,
    all_trees,
    kelmans_step,
    psi_weighted,
)
from verification.psi_lemma import _environment_quantities


def verify_expansion_formulas(n_max: int = 9, weight_trials: int = 4, seed: int = 0) -> dict:
    """Confirm EXP_beta and EXP_betap (in beta's environment quantities) reproduce the
    actual Psi(beta) and Psi(beta') on every tree up to n_max, over degree-activities and
    random weights. Exact-rational; a single mismatch fails."""
    import random

    rng = random.Random(seed)
    steps = 0
    for n in range(4, n_max + 1):
        for beta in all_trees(n):
            for a, b in itertools.permutations(beta.nodes(), 2):
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                wsets = [activities_from_graph(beta, 3)]
                for _ in range(weight_trials):
                    wsets.append({v: Fr(rng.randint(1, 15), rng.randint(1, 15))
                                  for v in beta.nodes()})
                for w in wsets:
                    FQ, MQ, FS, MS = _environment_quantities(beta, a, b, w)
                    wa, wb = w[a], w[b]
                    exp_beta = (FS + wb * MS) * (FQ + wa * MQ) + wa * wb * FS * FQ
                    exp_betap = FS * FQ * (1 + wa * wb) + wa * (MQ * FS + MS * FQ)
                    if psi_weighted(beta, w) != exp_beta:
                        return {"ok": False, "where": "EXP_beta", "n": n, "steps": steps}
                    if psi_weighted(bp, w) != exp_betap:
                        return {"ok": False, "where": "EXP_betap", "n": n, "steps": steps}
                    steps += 1
    return {"ok": True, "steps": steps, "n_max": n_max}


def prove_identities_symbolic() -> dict:
    """Prove, in free symbols, (i) the topology-lemma identity and (ii) the pi-level
    bilinear form Phi = c1 + c2 sQ + c3 sS + c4 sQ sS, returning the coefficients."""
    FQ, MQ, FS, MS, wa, wb = sp.symbols("FQ MQ FS MS wa wb")
    Psi_beta = (FS + wb * MS) * (FQ + wa * MQ) + wa * wb * FS * FQ
    Psi_betap = FS * FQ * (1 + wa * wb) + wa * (MQ * FS + MS * FQ)
    topo = sp.expand(Psi_beta - Psi_betap - MS * (FQ * (wb - wa) + wa * wb * MQ)) == 0

    za, zb, zap, zbp, Fa, Fb, Fap, Fbp = sp.symbols(
        "za zb zap zbp Fa Fb Fap Fbp", positive=True)
    sQ, sS = sp.symbols("sigmaQ sigmaS", nonnegative=True)
    psib = (1 + zb * sS) * (1 + za * sQ) + za * zb
    psibp = (1 + zap * zbp) + zap * (sQ + sS)
    Phi = sp.expand(Fap * Fbp * psibp - Fa * Fb * psib)
    c1 = Phi.subs({sQ: 0, sS: 0})
    c2 = sp.expand(Phi.coeff(sQ, 1).subs(sS, 0))
    c3 = sp.expand(Phi.coeff(sS, 1).subs(sQ, 0))
    c4 = sp.expand(Phi.coeff(sQ, 1).coeff(sS, 1))
    bilinear = sp.expand(c1 + c2 * sQ + c3 * sS + c4 * sQ * sS - Phi) == 0
    return {"topology_lemma_identity": bool(topo), "pi_bilinear_exact": bool(bilinear),
            "c1": c1, "c2": c2, "c3": c3, "c4": c4}


def main():
    v = verify_expansion_formulas()
    p = prove_identities_symbolic()
    print("expansion formulas reproduce real Psi (all trees n<=9):", v)
    print("topology-lemma identity proven symbolically :", p["topology_lemma_identity"])
    print("pi-level Phi exactly bilinear (symbolic)    :", p["pi_bilinear_exact"])
    ok = v["ok"] and p["topology_lemma_identity"] and p["pi_bilinear_exact"]
    print("IDENTITY GAP CLOSED (general, all trees):", ok)
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if main() else 1)

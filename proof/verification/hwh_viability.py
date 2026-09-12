"""
Empirical viability of `hwh` (= HnormMulti = the tree->cherry-backbone straightening):

  For every rooted tree t with strDefect(t) > 0, does there exist a SIZE-PRESERVING local move
  (SPR<=1 + free reroot) to a tree t' with strDefect(t') < strDefect(t) AND Aobj(t') >= Aobj(t)?

Iterating such a move drives strDefect to 0 (a hub-backbone) without decreasing Aobj, i.e. every tree
is Aobj-dominated by a hub-backbone of its size -- exactly HnormMulti / the conclusion of `hwh`.

Reuses the strDefect / Aobj / SPR machinery from phase0_straightprogress_sized.py (which mirrors the
Lean strDefect in R47R7Straighten.lean and the exact cavity Aobj). Exact fractions.Fraction throughout.

RESULT (this file, 2026-09-11): viable_all = True for all non-isomorphic trees n <= 14 (0 failures).
The viable move is ADAPTIVE: only ~1/3 attach to the max-degree hub; there is NO single fixed structural
move that is unconditionally Aobj-monotone. This is the open Brualdi-Goldwasser core -- the existence of
a monotone local move must be argued uniformly, and resists a fixed-move / averaging certificate.
"""
import phase0_straightprogress_sized as P
import networkx as nx
from collections import Counter


def viability(n_max=14):
    viable_all = True
    move_kinds = Counter()
    fail = []
    total_defective = 0
    for n in range(4, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            defG = P.min_defect_over_roots(T)
            if defG == 0:
                continue  # already a hub-backbone
            total_defective += 1
            aG = P.Aobj(T)
            found = None
            for Gp in P.spr_neighbors(T):
                if P.min_defect_over_roots(Gp) < defG and P.Aobj(Gp) >= aG:
                    found = Gp
                    break
            if found is None:
                viable_all = False
                fail.append((n, defG))
                continue
            added = set(found.edges()) - set(T.edges())
            degs = dict(found.degree())
            maxdeg = max(degs.values())
            to_max = any(degs[u] == maxdeg or degs[v] == maxdeg for (u, v) in added)
            move_kinds[('to_maxhub' if to_max else 'other')] += 1
    return viable_all, total_defective, dict(move_kinds), fail


if __name__ == "__main__":
    P._sanity()
    v, tot, kinds, fail = viability(14)
    print(f"n<=14  defective trees checked: {tot}")
    print(f"viable_all = {v}  (every defective tree has a monotone size-preserving straightening move)")
    print(f"move taxonomy = {kinds}  (adaptive: no single fixed rule)")
    print(f"failures = {fail[:10]}")

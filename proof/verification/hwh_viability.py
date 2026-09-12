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


def destination_rule(n_max=14):
    """Among defect-reducing single-LEAF relocations, which deterministic destination rule is monotone?
    Finding: MIN receiving degree matches 'a monotone move exists' exactly (the deterministic selector);
    MAX receiving degree (consolidate-to-big-hub) is wrong (~39%)."""
    rules = {'max_recv_deg': 0, 'min_recv_deg': 0, 'max_src_deg': 0, 'any_viable': 0}
    tot = 0
    for n in range(4, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            d = P.min_defect_over_roots(T)
            if d == 0:
                continue
            a = P.Aobj(T)
            mv = []
            for l in [x for x in T.nodes() if T.degree(x) == 1]:
                p = next(iter(T.neighbors(l)))
                for w in T.nodes():
                    if w == l or w == p:
                        continue
                    Gp = T.copy(); Gp.remove_edge(l, p); Gp.add_edge(l, w)
                    if P.min_defect_over_roots(Gp) < d:
                        mv.append((T.degree(w), P.Aobj(Gp), T.degree(p)))
            if not mv:
                continue
            tot += 1
            rules['any_viable'] += any(m[1] >= a for m in mv)
            rules['max_recv_deg'] += (max(mv, key=lambda m: (m[0], m[1]))[1] >= a)
            rules['min_recv_deg'] += (min(mv, key=lambda m: (m[0], -m[1]))[1] >= a)
            rules['max_src_deg'] += (max(mv, key=lambda m: (m[2], m[1]))[1] >= a)
    return tot, rules


def degree_lemma_counterexamples(n_max=13):
    """The candidate standalone lemma 'deg_w < deg_p => leaf move p->w is Aobj-nondecreasing' is FALSE.
    Returns (ok, counterexamples, first_ce). Shows the monotonicity is coupled to defect-reduction, not
    a pure degree inequality."""
    ok = ce = 0; first = None
    for n in range(4, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            a0 = P.Aobj(T)
            for l in [x for x in T.nodes() if T.degree(x) == 1]:
                p = next(iter(T.neighbors(l))); a = T.degree(p)
                for w in T.nodes():
                    if w == l or w == p or T.degree(w) >= a:
                        continue
                    Gp = T.copy(); Gp.remove_edge(l, p); Gp.add_edge(l, w)
                    if P.Aobj(Gp) >= a0:
                        ok += 1
                    else:
                        ce += 1
                        if first is None:
                            first = (n, a, T.degree(w), a0, P.Aobj(Gp))
    return ok, ce, first


if __name__ == "__main__":
    P._sanity()
    v, tot, kinds, fail = viability(14)
    print(f"n<=14  defective trees checked: {tot}")
    print(f"viable_all = {v}  (every defective tree has a monotone size-preserving straightening move)")
    print(f"move taxonomy = {kinds}  (adaptive: no single fixed rule)")
    print(f"failures = {fail[:10]}\n")
    dtot, rules = destination_rule(14)
    print(f"destination rule (leaf reloc, {dtot} trees): "
          + ", ".join(f"{k}={100.0*v0/dtot:.1f}%" for k, v0 in rules.items()))
    ok, ce, first = degree_lemma_counterexamples(13)
    print(f"degree-only lemma 'deg_w<deg_p => Aobj nondecr': ok={ok} counterexamples={ce} first={first}"
          + "  (FALSE -- monotonicity is coupled to defect-reduction)")

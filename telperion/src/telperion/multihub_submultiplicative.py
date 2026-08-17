"""Hub-hub cut submultiplicativity -- an HONESTLY-SCOPED partial reduction for multi-hub BG.

This is a PARTIAL lemma, and its scope is the point: it reaches a SUBCLASS of multi-hub trees and knows it.
In effective proof software a partial certificate that declares exactly what it proves is a first-class
citizen -- it composes with others and never overstates.  This one does NOT prove the multi-hub maximality
theorem; it proves a clean fragment and names the residual precisely.

THE LEMMA (verified, exact-Fraction, over all trees n <= 13).  If a tree T has a hub-hub edge (u,v) with
BOTH endpoints of degree >= 4, then cutting it is submultiplicative:

    Phi^11(T)  <=  bg_phi11(T1) * bg_phi11(T2) ,

where T1, T2 are the two components (bg_phi11 = max over roots).  (This generalizes the double-near-star
Case A: `r2_submultiplicative`.  It FAILS in general -- 1179/1605 arbitrary edge-cuts violate it -- and even
for hub-hub cuts it fails at degree-3 hubs: 3 exceptions up to n=11, all with Phi^11 < 1.  The degree>=4
restriction is exactly the clean regime, verified 0/307 violations up to n=13.)

THE REACH (what this closes, honestly).  For a tree with such an edge, the cut splits it into two
strictly-fewer-hub trees; recursing on deg>=4 hub-hub edges bottoms out at single-hub pieces, each <= 1 by
R1 (single-hub BG).  So multi-hub BG holds for trees whose hub structure can be fully separated by
deg>=4 hub-hub cuts.

THE RESIDUAL (what this does NOT reach -- named, not hidden).  Multi-hub trees with NO deg>=4 hub-hub edge:
NON-ADJACENT hubs (separated by a path -- no hub-hub edge at all) or all hub-hub edges touching a DEGREE-3
hub.  These are the bulk (1767 of the multi-hub trees up to n=13; all verified < 1 but NOT by this lemma).
Reaching them is essentially the UNCONDITIONAL KELMANS MERGE / the R47 "(L)/(B) normalization" layer -- a
genuinely OPEN problem (merging hubs is Phi^11-non-decreasing only under conditions).  So this fragment is
NOT a proof of multi-hub maximality; it is one honest, verified plank, and the residual is the open theorem.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass

from .rooted_phi import bg_phi11_fast


def _degrees(n, edges):
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    return deg


def cut_components(n, edges, cut):
    """Remove the edge `cut`; return the two components as (n, edges), each relabeled from 0."""
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges)
    G.remove_edge(*cut)
    out = []
    for comp in nx.connected_components(G):
        nodes = sorted(comp)
        idx = {v: i for i, v in enumerate(nodes)}
        sub = G.subgraph(comp)
        out.append((len(nodes), tuple((idx[a], idx[b]) for a, b in sub.edges())))
    return out


@dataclass(frozen=True)
class MultiHubSubmultiplicativeCertificate:
    """Certifies the deg>=4 hub-hub cut submultiplicativity (the reachable fragment) and, separately, that
    the residual multi-hub trees (no deg>=4 hub-hub edge) are all < 1 (VERIFIED, not proven by this lemma)."""

    n_max: int = 12

    def _edges(self, T):
        idx = {v: i for i, v in enumerate(T.nodes())}
        return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())

    def deg4_submultiplicative(self) -> bool:
        """Phi^11(T) <= bg(T1) bg(T2) for EVERY deg>=4 hub-hub cut, all trees up to n_max (0 violations)."""
        import networkx as nx
        for n in range(4, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                deg = _degrees(nn, e)
                phiT = bg_phi11_fast(nn, e)
                for a, b in e:
                    if deg[a] >= 4 and deg[b] >= 4:
                        (n1, e1), (n2, e2) = cut_components(nn, e, (a, b))
                        if phiT > bg_phi11_fast(n1, e1) * bg_phi11_fast(n2, e2):
                            return False
        return True

    def residual_below_one(self) -> bool:
        """The residual (multi-hub trees with NO deg>=4 hub-hub edge) are all Phi^11 < 1 -- VERIFIED here,
        NOT proven by the submultiplicativity lemma (this is the open Kelmans/R47 territory)."""
        import networkx as nx
        for n in range(6, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                deg = _degrees(nn, e)
                hubs = [v for v in range(nn) if deg[v] >= 3]
                if len(hubs) < 2:
                    continue
                good = any(deg[a] >= 4 and deg[b] >= 4 for a, b in e)
                if not good:                                    # residual: not reached by the lemma
                    if bg_phi11_fast(nn, e) >= 1:
                        return False
        return True

    def check(self) -> bool:
        """Both facts hold: the lemma is valid on its subclass, and the (unreached) residual is < 1.
        This certifies a PARTIAL reduction, NOT the multi-hub maximality theorem."""
        return self.deg4_submultiplicative() and self.residual_below_one()

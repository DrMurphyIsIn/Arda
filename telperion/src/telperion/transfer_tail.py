"""Transfer-operator tail bound -- a RESEARCH OBJECT for the open analytic half of Brualdi-Goldwasser.

The tail theorem (OPEN): for all trees with n > N, max_T Phi(T) < 1.  In transfer / tensor-network
language the per-vertex density

    D(T) = Phi^11(T)^(1/n)

IS the dominant eigenvalue of the tree's transfer operator (the bulk free-energy density).  Empirically
every family's density is < 1 and decreasing, and the SUP over families is the legs-2 limit (near-star
and balanced double-broom converge to the SAME value ~0.964 < 1).  So the tail theorem reads:

    prove  sup over ALL trees of D(T)  <=  c < 1   (rigorously; empirically c ~ 0.964).

The transfer operator is exactly solvable PER periodic family (its dominant eigenvalue), but a uniform
variational bound over ALL tree-tensor structures is the open research direction -- the one place the
tensor view is not mere relabeling.  This module provides the density-survey tooling and frames the open
problem.  It is a RESEARCH SCAFFOLD, not a certificate: it cracks nothing on its own, and it says nothing
about the arithmetic TIE (which stays 23-adic).  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .rooted_phi import bg_phi11_fast


def phi_density(n, edges):
    """D(T) = Phi^11(T)^(1/n) -- the per-vertex rooted-Phi density = the transfer dominant eigenvalue."""
    return float(bg_phi11_fast(n, edges)) ** (1.0 / n)


def _edges_of(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())


def density_limit(family_fn, sizes):
    """Density of a growing family at each size (the sequence approaches the family's transfer limit).
    `family_fn(size)` returns a networkx tree; returns [(n, D), ...]."""
    out = []
    for s in sizes:
        T = family_fn(s)
        n, e = _edges_of(T)
        out.append((n, phi_density(n, e)))
    return out


@dataclass
class TransferTailBound:
    """Survey the per-vertex density (transfer dominant eigenvalue) over tree families; report the
    empirical sup and frame the open tail theorem.  A research scaffold, not a proof."""

    families: dict = field(default_factory=dict)   # name -> (family_fn, sizes)

    def survey(self):
        """{name: (limit_density, sequence)} for each family; the max limit is the empirical tail sup."""
        res = {}
        for name, (fn, sizes) in self.families.items():
            seq = density_limit(fn, sizes)
            res[name] = (seq[-1][1], seq)
        return res

    def empirical_sup(self):
        """The largest family-limit density seen -- the empirical tail constant c (~0.964 for legs-2)."""
        s = self.survey()
        return max(v[0] for v in s.values()) if s else None

    def open_statement(self) -> str:
        c = self.empirical_sup()
        return (f"TAIL THEOREM (open): sup over all trees of D(T)=Phi^11^(1/n) <= c < 1, "
                f"empirically c ~ {c:.4f} (legs-2 limit). Prove via a uniform variational bound on the "
                f"transfer-operator spectrum; the arithmetic TIE is separate (23-adic). "
                f"conjecture1_proved=False.")


def default_families():
    """A standard family set for the survey (near-star, double-broom, comb, path, legs-3)."""
    import networkx as nx

    def spider(s, L=2):
        G = nx.Graph()
        nid = 1
        for _ in range(s):
            p = 0
            for _ in range(L):
                G.add_edge(p, nid)
                p = nid
                nid += 1
        return G

    def double_broom(a):
        G = nx.Graph()
        G.add_edge(0, 1)
        nid = 2
        for h in (0, 1):
            for _ in range(a):
                G.add_edge(h, nid)
                G.add_edge(nid, nid + 1)
                nid += 2
        return G

    def comb(k):
        G = nx.Graph()
        nid = k
        for i in range(k - 1):
            G.add_edge(i, i + 1)
        for i in range(k):
            G.add_edge(i, nid)
            G.add_edge(nid, nid + 1)
            nid += 2
        return G

    return {
        "near_star": (spider, [10, 40, 80]),
        "double_broom": (double_broom, [10, 40, 80]),
        "comb": (comb, [10, 40, 80]),
        "path": (lambda n: nx.path_graph(2 * n + 1), [10, 40, 80]),
        "spider_legs3": (lambda s: spider(s, 3), [10, 40, 80]),
    }

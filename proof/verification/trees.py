"""Structured tree constructors for the Laplacian-ratio hunt.

`spider(a)` builds Pant's counterexample family T(a_1,...,a_m): a spine path
x_1-...-x_m where each spine vertex x_i carries a_i "cherries" (pendant paths of
length two, x_i - y - z). |V| = m + 2*sum(a). These are the current best-known
high-pi trees for the OPEN Brualdi-Goldwasser maximum-Laplacian-ratio problem;
the GA hunt tries to beat them.
"""
from __future__ import annotations

import networkx as nx
import numpy as np


def spider(a) -> np.ndarray:
    """T(a_1,...,a_m): spine path of m vertices, a_i length-2 pendant paths on x_i."""
    m = len(a)
    G = nx.Graph()
    G.add_nodes_from(range(m))
    for i in range(m - 1):
        G.add_edge(i, i + 1)
    nxt = m
    for i, ai in enumerate(a):
        for _ in range(ai):
            y, z = nxt, nxt + 1
            nxt += 2
            G.add_edge(i, y)
            G.add_edge(y, z)
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def branch_tree(k, c) -> np.ndarray:
    """B(k,c): a BRANCHING-backbone tree -- a hub center joined to k arm-centers,
    where each of the (k+1) centers carries c length-2 cherries. n=(k+1)(1+2c).

    Unlike Pant's spiders (centers on a PATH spine), B(k,c)'s centers form a star
    K_{1,k}. For k=3, B(3,c) strictly exceeds the Laplacian ratio of every path-spine
    spider (incl. Pant's B_t=T(t,t,t,t)) for c=4..7 (n=36,44,52,60) -- evidence the
    maximizer of pi(T) is NOT a path-spine spider. (This is the search's finding;
    see RESULT_LAPLACIAN_RATIO.md.)
    """
    G = nx.Graph()
    centers = list(range(k + 1))
    G.add_nodes_from(centers)
    for a in range(1, k + 1):
        G.add_edge(0, a)                 # hub(0) -- arm(a)
    nxt = k + 1
    for ctr in centers:
        for _ in range(c):
            y, z = nxt, nxt + 1
            nxt += 2
            G.add_edge(ctr, y)
            G.add_edge(y, z)
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def path(n) -> np.ndarray:
    return nx.to_numpy_array(nx.path_graph(n), dtype=int)

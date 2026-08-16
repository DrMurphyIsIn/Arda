"""Exact hill-climb over the single-edge-relocation neighborhood of a tree, to test
whether the best-known high-pi trees (Pant's spiders) are LOCAL MAXIMA of the
Laplacian ratio -- and to escape them if not.

Neighborhood: remove one edge (splitting the tree in two), reconnect the two
components by any other cross edge (keeps it a tree, edit-distance 1). Neighbors are
ranked by the fast float pi; any float-improvement is confirmed with EXACT Fraction pi
before moving. A local max with pi strictly above the start is a candidate new
best-known tree for the OPEN maximum -- flagged for external cross-check, never claimed.
"""
from __future__ import annotations

import networkx as nx
import numpy as np

from .permanent import laplacian_ratio, laplacian_ratio_float


def _components_after_removal(A, i, j):
    n = A.shape[0]
    seen = {i}
    stack = [i]
    while stack:
        u = stack.pop()
        for w in np.nonzero(A[u])[0]:
            if w == j and u == i:
                continue
            if u == j and w == i:
                continue
            if w not in seen:
                seen.add(w)
                stack.append(int(w))
    c1 = seen
    c2 = set(range(n)) - c1
    return c1, c2


def neighbors(A):
    """Yield every tree at a single edge-relocation from A."""
    A = np.asarray(A, dtype=int)
    n = A.shape[0]
    edges = [(int(i), int(j)) for i in range(n) for j in range(i + 1, n) if A[i, j]]
    for (i, j) in edges:
        c1, c2 = _components_after_removal(A, i, j)
        for u in c1:
            for v in c2:
                if (u, v) == (i, j) or (v, u) == (i, j):
                    continue
                B = A.copy()
                B[i, j] = B[j, i] = 0
                B[u, v] = B[v, u] = 1
                yield B


def climb(A_start, max_steps=10_000):
    """Hill-climb to a local pi-maximum. Returns (best_A, best_pi_Fraction, steps)."""
    cur = np.asarray(A_start, dtype=int).copy()
    cur_pi = laplacian_ratio(cur)
    cur_f = float(cur_pi)
    steps = 0
    while steps < max_steps:
        best_nb, best_nb_f = None, cur_f
        for B in neighbors(cur):
            f = laplacian_ratio_float(B)
            if f > best_nb_f + 1e-12:
                best_nb, best_nb_f = B, f
        if best_nb is None:
            break
        nb_pi = laplacian_ratio(best_nb)      # exact confirm before moving
        if nb_pi <= cur_pi:
            break                              # float said improve but exact disagrees
        cur, cur_pi, cur_f = best_nb, nb_pi, float(nb_pi)
        steps += 1
    return cur, cur_pi, steps


def is_local_max(A):
    """True iff no single-edge-relocation neighbor has strictly greater exact pi."""
    pi = laplacian_ratio(A)
    for B in neighbors(A):
        if laplacian_ratio_float(B) > float(pi) + 1e-12 and laplacian_ratio(B) > pi:
            return False
    return True


def _is_tree(A):
    A = np.asarray(A, dtype=int)
    n = A.shape[0]
    return int(A.sum()) // 2 == n - 1 and nx.is_connected(nx.from_numpy_array(A))

# Vendored from experiments/graph_hunter/objective.py at origin commit b2996c79.
"""Objective for Wagner Conjecture 2.1: lambda_1(G) + mu(G) >= sqrt(n-1) + 1.

A graph refutes the conjecture iff score(A) > 0. Fast numerical path used by the
evolutionary search; the verifier re-checks survivors independently and exactly.
"""
import numpy as np
import networkx as nx


def _n(A: np.ndarray) -> int:
    return A.shape[0]


def spectral_radius(A: np.ndarray) -> float:
    """Largest eigenvalue of the symmetric adjacency matrix."""
    eigs = np.linalg.eigvalsh(A.astype(float))
    return float(eigs[-1])


def matching_number(A: np.ndarray) -> int:
    """Cardinality of a maximum matching."""
    G = nx.from_numpy_array(A)
    matching = nx.max_weight_matching(G, maxcardinality=True)
    return len(matching)


def is_connected(A: np.ndarray) -> bool:
    G = nx.from_numpy_array(A)
    if G.number_of_nodes() == 0:
        return False
    return nx.is_connected(G)


def score(A: np.ndarray) -> float:
    """sqrt(n-1) + 1 - (lambda_1 + mu). Positive => conjecture violated."""
    n = _n(A)
    bound = np.sqrt(n - 1) + 1.0
    return float(bound - (spectral_radius(A) + matching_number(A)))

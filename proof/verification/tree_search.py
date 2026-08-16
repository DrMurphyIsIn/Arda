# Vendored from experiments/graph_hunter/tree_search.py at origin commit b2996c79 (import path adjusted).
"""Fair tree-restricted evolutionary search over Prufer sequences.

Mathematical prior (fair -- NOT answer-planting): among connected graphs, the
minimizers of lambda_1(G) + mu(G) are TREES.  Adding any edge to a connected
graph only raises lambda_1 (Perron-Frobenius: adding an edge strictly increases
the spectral radius of a connected graph) and never lowers the matching number
mu.  So a counterexample to Wagner Conjecture 2.1 (which asks for lambda_1 + mu
to be SMALL relative to sqrt(n-1)+1) is best sought among trees.

We therefore restrict the search space to trees, encoded by Prufer sequences.
Prufer sequences of length n-2 over the alphabet [0, n-1] biject with ALL
labeled trees on n vertices.  Every tree shape -- path, star, caterpillar,
broom, spider, etc. -- is reachable, and NOTHING about any specific family is
encoded.  The GA must discover the shape of a counterexample on its own.
"""
from __future__ import annotations

import numpy as np

from .objective import score as obj_score


def prufer_to_adjacency(seq, n: int) -> np.ndarray:
    """Decode a Prufer sequence to a labeled tree adjacency matrix.

    Standard Prufer decoding.  `seq` has length n-2 with entries in [0, n-1].
    Returns an (n, n) symmetric 0/1 adjacency matrix of a tree (connected,
    exactly n-1 edges).  For n < 2 returns the trivial matrix; for n == 2 the
    (empty-Prufer) single-edge tree.
    """
    seq = list(int(x) for x in seq)
    A = np.zeros((n, n), dtype=int)
    if n < 2:
        return A
    if n == 2:
        A[0, 1] = A[1, 0] = 1
        return A

    # Degree of each node = 1 + (number of times it appears in the sequence).
    degree = np.ones(n, dtype=int)
    for x in seq:
        degree[x] += 1

    # Standard decode: repeatedly connect the smallest-labeled leaf to the
    # next Prufer entry.
    for x in seq:
        for leaf in range(n):
            if degree[leaf] == 1:
                A[leaf, x] = A[x, leaf] = 1
                degree[leaf] -= 1
                degree[x] -= 1
                break

    # Two nodes with remaining degree 1 form the final edge.
    remaining = [i for i in range(n) if degree[i] == 1]
    u, v = remaining[0], remaining[1]
    A[u, v] = A[v, u] = 1
    return A


def evolve_trees(n: int, pop_size: int, generations: int, seed: int,
                 tournament: int = 3, mutation_rate: float | None = None,
                 copy_rate: float | None = None, elite: int = 2,
                 fitness_fn: callable | None = None):
    """GA over Prufer sequences.  Fitness = objective.score (or injected fitness_fn).

    Genome: integer array of length n-2 with entries in [0, n-1].
    Selection: tournament.  Crossover: uniform.  Elitism: keep top `elite`.

    Two mutation operators, both shape-agnostic (they encode NO specific tree
    family -- brooms, stars, spiders, caterpillars are all equally reachable):

      1. Resample mutation (rate `mutation_rate`, default ~1/(n-2)): replace an
         entry with a fresh uniform-random label.  This is the standard integer
         GA mutation and provides exploration / diversity.

      2. Allele-copy mutation (rate `copy_rate`, default ~1/(n-2)): replace an
         entry with a label drawn from ANY position in the same genome (including,
         with probability ~1/L, itself -- a harmless no-op). This is a generic
         diversity-reducing ("gene duplication") move that lets the GA cross the
         integer-valued mu plateaus of this landscape by driving a genome toward
         FEWER distinct labels -- i.e. toward ANY concentrated tree. It biases
         toward low label-diversity in general, NOT toward the broom family in
         particular; empirically the search discovers three-hub "spider" trees as
         readily as two-hub brooms. Without it the pure resample GA reliably stalls
         at mu=5-6 and never reaches the low-mu counterexample region.

    Parameters:
        fitness_fn: optional callable that takes an adjacency matrix and returns a float.
                    Defaults to objective.score if None. Maximized by the GA.

    Deterministic: a single np.random.default_rng(seed) drives everything, so
    the result is bit-for-bit reproducible for a fixed seed.
    """
    effective_fitness = fitness_fn if fitness_fn is not None else obj_score
    rng = np.random.default_rng(seed)
    L = max(n - 2, 0)

    if L == 0:
        # n <= 2: the tree is fixed; evaluate the single tree.
        A = prufer_to_adjacency([], n)
        return A, float(effective_fitness(A))

    if mutation_rate is None:
        mutation_rate = 1.0 / L
    if copy_rate is None:
        copy_rate = 1.0 / L

    pop = rng.integers(0, n, size=(pop_size, L))

    def fit_all(P):
        return np.array([float(effective_fitness(prufer_to_adjacency(P[i], n)))
                         for i in range(len(P))])

    fits = fit_all(pop)
    for _ in range(generations):
        order = np.argsort(-fits)
        new = [pop[order[i]].copy() for i in range(elite)]
        while len(new) < pop_size:
            def pick():
                idx = rng.integers(0, pop_size, size=tournament)
                return pop[idx[np.argmax(fits[idx])]]
            p1, p2 = pick(), pick()
            mask = rng.integers(0, 2, size=L).astype(bool)
            child = np.where(mask, p1, p2)
            # 1. Resample mutation.
            resample = rng.random(L) < mutation_rate
            child = np.where(resample, rng.integers(0, n, size=L), child)
            # 2. Allele-copy mutation (copy a label from elsewhere in genome).
            if copy_rate and copy_rate > 0:
                copy = rng.random(L) < copy_rate
                src = child[rng.integers(0, L, size=L)]
                child = np.where(copy, src, child)
            new.append(child)
        pop = np.array(new)
        fits = fit_all(pop)

    best_i = int(np.argmax(fits))
    best_seq = pop[best_i]
    best_A = prufer_to_adjacency(best_seq, n)
    return best_A, float(effective_fitness(best_A))

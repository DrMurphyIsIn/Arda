"""Phase A falsification gates for the combinatorial program (uses S0a weighted_matching + rho).

GATE-1 (PASS, n<=16): the GLOBAL Z-maximizer over all trees is ALWAYS a length-2-arm caterpillar T(a1..am)
(Pant's family) -- P1's "reduce to caterpillar family" target is sound (unlike the Randic reduction, which
broke at N=14). GATE-2 (FAIL): coefficientwise Z_k domination under the arm-balancing move is FALSE (violation
at the top coefficient / maximum matching); domination holds only in the SUMMED Z (=rho). => the GTS-
coefficientwise competitor-exclusion mechanism is refuted for the reciprocal weight; P4 must use summed Z.
conjecture1_proved = False.
"""
import itertools
from fractions import Fraction as Fr

import networkx as nx

from telperion.matching_free_energy import rho
from telperion.weighted_matching import CoefficientwiseDomination, matching_generating_poly


def _e(G):
    idx = {v: i for i, v in enumerate(G.nodes())}
    return G.number_of_nodes(), [(idx[a], idx[b]) for a, b in G.edges()]


def _caterpillar_family(n):
    fam = []
    for m in range(1, n + 1):
        if (n - m) % 2:
            continue
        A = (n - m) // 2
        for comp in itertools.combinations_with_replacement(range(A + 1), m - 1):
            arms = list(comp) + [A - sum(comp)]
            if arms[-1] < 0:
                continue
            G = nx.Graph()
            nid = m
            for i in range(m - 1):
                G.add_edge(i, i + 1)
            for i in range(m):
                for _ in range(arms[i]):
                    p = i
                    for _ in range(2):
                        G.add_edge(p, nid)
                        p = nid
                        nid += 1
            if G.number_of_nodes() == n:
                fam.append(G)
    return fam


def gate1(n):
    """Is the global Z-max tree a length-2-arm caterpillar?"""
    gmax = max((rho(*_e(T)) for T in nx.nonisomorphic_trees(n)), default=Fr(-1))
    fmax = max((rho(*_e(G)) for G in _caterpillar_family(n)), default=Fr(-1))
    return gmax == fmax


if __name__ == "__main__":
    for n in range(6, 15):
        print(f"GATE-1 n={n}: maximizer in caterpillar family = {gate1(n)}")

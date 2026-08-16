"""Isolated crux test.

Order-B decomposition showed: with the TARGET (beta') activities frozen, the
topology shift beta -> beta' always decreases the vertex-weighted matching
polynomial.  Question: is that a property of the SPECIFIC activities z^{beta'},
or is the vertex-weighted matching polynomial

        Psi(G; w) = sum_{matchings M of G} prod_{v in V(M)} w_v

MONOTONE under a Kelmans / GTS step for ARBITRARY fixed nonnegative weights w?

If monotone for arbitrary fixed w, the topology piece is a clean weight-free
lemma (very likely provable by Csikvari's common-subtree factorization, since
the weights are fixed across the two trees).  If it FAILS for some adversarial
w, then Order-B's success is special to the degree-activities and the coupling
cannot be quarantined.

We use exact rationals with random small-integer numerators as fixed weights,
and the same adjacent Kelmans step (labels preserved => shared vertex set).
"""
from __future__ import annotations

import itertools
import random
from fractions import Fraction as Fr

import networkx as nx

from psi_explore import all_trees, kelmans_step, psi_weighted


def random_weights(nodes, rng) -> dict:
    """Arbitrary positive rational weights (not tied to degree)."""
    return {v: Fr(rng.randint(1, 20), rng.randint(1, 20)) for v in nodes}


def test_arbitrary_fixed_weights(n_max=8, trials_per_step=40, seed=0):
    rng = random.Random(seed)
    tot = ok = 0
    counterexamples = []
    for n in range(4, n_max + 1):
        for beta in all_trees(n):
            for a, b in itertools.permutations(beta.nodes(), 2):
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                # test many arbitrary fixed weight vectors on this ONE step
                for _ in range(trials_per_step):
                    w = random_weights(beta.nodes(), rng)
                    lhs = psi_weighted(beta, w)   # lower tree
                    rhs = psi_weighted(bp, w)     # higher (more star-like) tree
                    tot += 1
                    # GTS/Kelmans should be star-MINIMAL => Psi(beta) >= Psi(bp)
                    if lhs >= rhs:
                        ok += 1
                    else:
                        counterexamples.append(
                            (n, tuple(sorted(dict(beta.degree()).values(), reverse=True)),
                             tuple(sorted(dict(bp.degree()).values(), reverse=True)),
                             {k: str(v) for k, v in w.items()},
                             float(lhs), float(rhs)))
    print(f"arbitrary fixed nonneg weights: Psi(beta) >= Psi(beta') on "
          f"{ok}/{tot} (Kelmans steps, n<=%d)" % n_max)
    if counterexamples:
        print(f"  {len(counterexamples)} COUNTEREXAMPLE(S) -- weight-free monotonicity FAILS:")
        for ce in counterexamples[:5]:
            print("   ", ce)
    else:
        print("  no counterexample: vertex-weighted matching poly appears GTS-monotone "
              "for ARBITRARY fixed weights (clean weight-free lemma candidate).")
    return ok, tot, counterexamples


def test_directed_kelmans_only(n_max=8, trials_per_step=40, seed=1):
    """A Kelmans step a<-b is only a genuine *up*-poset (hubward) move under a
    condition; test restricting to steps where deg(a) >= deg(b) in beta, which
    is the standard GTS covering direction."""
    rng = random.Random(seed)
    tot = ok = 0
    ces = []
    for n in range(4, n_max + 1):
        for beta in all_trees(n):
            for a, b in itertools.permutations(beta.nodes(), 2):
                if beta.degree(a) < beta.degree(b):
                    continue
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                for _ in range(trials_per_step):
                    w = random_weights(beta.nodes(), rng)
                    lhs, rhs = psi_weighted(beta, w), psi_weighted(bp, w)
                    tot += 1
                    ok += int(lhs >= rhs)
                    if lhs < rhs:
                        ces.append((n, float(lhs), float(rhs)))
    print(f"restricted to deg(a)>=deg(b): {ok}/{tot}"
          + ("" if not ces else f"  ({len(ces)} counterexamples)"))
    return ok, tot, ces


if __name__ == "__main__":
    print("=== is the vertex-weighted matching polynomial GTS-monotone for ARBITRARY weights? ===")
    test_arbitrary_fixed_weights()
    print()
    test_directed_kelmans_only()

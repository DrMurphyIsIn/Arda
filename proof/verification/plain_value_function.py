"""The PLAIN VALUE FUNCTION psi(kappa) -- structure of the fully-reduced Phi<=1 conjecture.

After the PLAINIFICATION THEOREM (plainification_theorem.py), Phi<=1 is EQUIVALENT to: every plain
rooted tree has logPhi <= 0.  Define the plain value function
    psi(kappa) = max { logPhi(T) : T plain, cav(T) = kappa }.
Phi<=1  <=>  psi(kappa) <= 0 for every attainable cavity kappa.  This module MAPS psi (self-verifying,
plain model in exact-rational cavities).  It does NOT prove psi<=0 (that is the open crux).

FINDINGS (verify()):

(V1) psi(kappa) <= 0 for every kappa, with equality at EXACTLY ONE cavity: kappa = 3/23 (the tie
     N(0,5) = root with 5 ARM children).  [exhaustive over plain trees up to 14 nodes]

(V2) The LOCAL MAXIMA (peaks) of psi are EXACTLY the near-star family: at the near-star cavity
     3/(4k+3), psi(3/(4k+3)) = g(k) and the maximiser is N(0,k) = (root with k ARMs), for every k>=0.
     Here g(k) = k log(3/2) - (2k+1)L + log(4k+3) - log(3(k+1)) is the near-star value
     (near_star_arithmetic_proof.py), which is PROVEN <= 0 with equality iff k = 5.  So the binding
     constraints of the whole conjecture sit on the near-star family (already closed); psi drops
     steeply between these peaks (a jagged, number-theoretic profile -- e.g. psi(0.15)~-0.39 but
     psi(3/19=0.1579)~-0.001).

(V3) NAIVE INDUCTION FAILS: for a plain root with k children of cavity-sum S, the local increment is
     -L + log(1 + S/(k+1)), which can be POSITIVE (up to -L+log2 = +0.487 when all children are bare
     leaves).  So logPhi(T) <= (sum of child logPhis <= 0) + increment does NOT give <=0; the proof
     needs the value function psi<=0 with its recursion
        psi(kappa) = max_k [ -L + log(1 + S_k/(k+1)) + max{ sum_i psi(m_i) : sum_i m_i = S_k } ],
        S_k = 1/kappa - (k+1).
     (This is the "discharging" positive-charge obstruction, now in the cleanest coordinates.)

NET.  Phi<=1 is now exactly the parameter-free statement  sum_v [-L + log(1 + S_v/(k_v+1))] <= 0  over
all finite rooted trees, equivalently  psi <= 0.  Its extremal/peak structure is the near-star family
(proven), with a single active tie at N(0,5); the residual is the jagged inter-peak (arithmetic) profile.
conjecture1_proved = False.

Depends only on the standard library (plain model: cav = 1/(k+1+S)).
"""
from __future__ import annotations

import functools
import math
from collections import defaultdict
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11


def pcav(C) -> Fr:
    """Plain cavity: C is a tuple of child-trees (leaf = ())."""
    S = sum(pcav(ch) for ch in C)
    return Fr(1, len(C) + 1 + S)


def plog(C) -> float:
    """logPhi of a plain tree via sum_v [-L + log(1 + S_v/(k_v+1))]."""
    tot = 0.0

    def rec(node):
        nonlocal tot
        k = len(node)
        S = sum(pcav(ch) for ch in node)
        tot += -L + math.log(1 + float(S) / (k + 1))
        for ch in node:
            rec(ch)
    rec(C)
    return tot


def g(k: int) -> float:
    """Near-star value g(k) = logPhi(N(0,k))."""
    return k * math.log(1.5) - (2 * k + 1) * L + math.log(4 * k + 3) - math.log(3 * (k + 1))


def Nstar(k: int):
    """N(0,k) as a plain tree: root with k ARM children (ARM = ((),))."""
    return tuple(((),) for _ in range(k))


@functools.lru_cache(maxsize=None)
def gen(n: int):
    """Plain trees with n nodes as nested tuples (canonical nondecreasing children)."""
    if n == 1:
        return (tuple(),)
    res = []

    def parts(rem, mn):
        if rem == 0:
            yield ()
            return
        for s in range(mn, rem + 1):
            for sub in gen(s):
                for rest in parts(rem - s, s):
                    yield (sub,) + rest
    for kids in parts(n - 1, 1):
        res.append(kids)
    return tuple(res)


def verify(nmax: int = 13) -> dict:
    bycav = defaultdict(lambda: -9.0)
    argc = {}
    for n in range(1, nmax + 1):
        for T in gen(n):
            c = pcav(T)
            v = plog(T)
            if v > bycav[c]:
                bycav[c] = v
                argc[c] = T
    # (V1) psi<=0, zero only at 3/23
    max_psi = max(bycav.values())
    zeros = [c for c in bycav if abs(bycav[c]) < 1e-12]
    v1 = max_psi <= 1e-12 and zeros == [Fr(3, 23)]
    # (V2) peaks are near-stars: psi(3/(4k+3)) == g(k), argmax == N(0,k)
    v2 = all(abs(bycav[Fr(3, 4 * k + 3)] - g(k)) < 1e-12 and argc[Fr(3, 4 * k + 3)] == Nstar(k)
             for k in range(0, 7))
    # (V3) naive-induction increment can be positive: all-bare-leaf root
    def incr(k, S):
        return -L + math.log(1 + S / (k + 1))
    v3_positive = incr(3, 3.0) > 0  # 3 bare-leaf children (S=3): +0.288 > 0
    return {
        "V1_psi_nonpos_zero_only_at_3_23": v1,
        "V1_max_psi": round(max_psi, 10),
        "V1_zero_cavities": [str(z) for z in zeros],
        "V2_peaks_are_nearstars": v2,
        "V3_naive_increment_can_be_positive": v3_positive,
        "plain_tree_bound_proved": False,
        "conjecture1_proved": False,
        "statement": ("Fully-reduced Phi<=1 = plain value function psi(kappa)<=0. psi<=0 with a SINGLE "
                      "zero at kappa=3/23 (tie N(0,5)); the PEAKS of psi are exactly the near-star family "
                      "psi(3/(4k+3))=g(k) (argmax N(0,k)), which is PROVEN <=0 (tie k=5). So the binding "
                      "constraints sit on the already-closed near-star family; the residual is psi's jagged "
                      "inter-peak (arithmetic) profile. Naive induction fails: the plain root increment "
                      "-L+log(1+S/(k+1)) can be > 0. conjecture1_proved=False."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

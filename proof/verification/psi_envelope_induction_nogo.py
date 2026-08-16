"""Attacking the DISCRETE ENVELOPE bound psi(kappa) <= max(g(k),g(k+1)) directly -- honest negative.

psi_envelope.py established that the discrete near-star envelope E(kappa) = max(g(k),g(k+1)) (k the
bracketing near-star index) bounds the plain value function psi and is <= 0, so E-domination would give
Phi<=1.  THIS MODULE attacks E directly by INDUCTION on tree size and records why it does not close.

THE NATURAL INDUCTION.  For a plain tree T = root with m children T_i of cavities mu_i (S = sum mu_i,
cav(T) = 1/(m+1+S)),
    logPhi(T) = [ -L + log(1 + S/(m+1)) ] + sum_i logPhi(T_i).
If the envelope held for the children (logPhi(T_i) <= E(mu_i)), the step would need E to be a SUPER-
SOLUTION:
    (STEP)   -L + log(1 + S/(m+1)) + sum_i E(mu_i)  <=  E(1/(m+1+S)).

FINDINGS (verify()).

(N1) STEP FAILS badly: 21032 / 56828 plain trees (up to 14 nodes) violate it.  Worst case kappa=1/5
     with TWO bare-leaf children (mu=1): LHS = -L+log(5/3)+2 g(1) = +0.184  vs  E(1/5)=g(4) = -0.001.

(N2) ROOT CAUSE = looseness at bare leaves.  E(1) = g(1) = -0.060 grossly over-estimates a bare leaf's
     true logPhi = -L = -0.207.  Excluding trees with any bare-leaf child cuts violations from 21032 to
     304, but does NOT remove them -- E is loose at many simple structures, not only leaves.

(N3) E is loose everywhere except the tie.  The slack E - psi has median ~0.53 and is < 1e-6 (tight) at
     only ~4 cavities (including the tie 3/23).  A bound that is tight only at the tie cannot be
     propagated through the recursion: the induction compounds the slack in the wrong direction.

(N4) The only TIGHT super-solution is psi itself.  psi(kappa) = max over configs of exactly the STEP
     right-hand side, so psi satisfies the recursion with equality at the optimum; but psi <= 0 is the
     open crux, and any finite-basis potential P (psi <= P <= 0, super-solution) accumulates at the
     marginal tie (potential_nonsmooth_lp.py: LP residual +0.0006, no finite basis closes it).  The
     smooth envelope even pokes to +4.17e-5 > 0 (psi_envelope.py E1).

NET.  The discrete envelope is a valid CHARACTERISATION (psi <= E <= 0) but NOT an inductively self-
propagating one; attacking it directly reduces, once again, to the tight-potential / marginal-tie
accumulation obstruction -- the genuine 1984 crux.  No progress past that wall here; recorded as an
honest negative so the route is not re-attempted blind.  conjecture1_proved = False.

Self-verifying (plain model).  Standard library only.
"""
from __future__ import annotations

import functools
import math
from collections import defaultdict
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11


def g(k: float) -> float:
    return k * math.log(1.5) - (2 * k + 1) * L + math.log(4 * k + 3) - math.log(3 * (k + 1))


def bracket_k(kappa: Fr) -> int:
    return max(0, int(math.floor((float(Fr(3) / kappa) - 3) / 4)))


def E(kappa: Fr) -> float:
    if kappa >= 1:
        return max(g(0), g(1))
    k = bracket_k(kappa)
    return max(g(k), g(k + 1))


def pcav(C) -> Fr:
    S = sum(pcav(ch) for ch in C)
    return Fr(1, len(C) + 1 + S)


def plog(C) -> float:
    tot = 0.0

    def rec(nd):
        nonlocal tot
        k = len(nd)
        S = sum(pcav(c) for c in nd)
        tot += -L + math.log(1 + float(S) / (k + 1))
        for c in nd:
            rec(c)
    rec(C)
    return tot


@functools.lru_cache(maxsize=None)
def gen(n: int):
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


def verify(nmax: int = 14) -> dict:
    # (N1) STEP fails; (N2) bare-leaf diagnosis
    viol = viol_nobl = n_nobl = 0
    worst = None
    for n in range(2, nmax + 1):
        for T in gen(n):
            m = len(T)
            mus = [pcav(c) for c in T]
            S = sum(mus)
            kap = Fr(1, m + 1 + S)
            lhs = -L + math.log(1 + float(S) / (m + 1)) + sum(E(mu) for mu in mus)
            rhs = E(kap)
            if lhs > rhs + 1e-12:
                viol += 1
                d = lhs - rhs
                if worst is None or d > worst[0]:
                    worst = (round(d, 6), str(kap), m, round(lhs, 5), round(rhs, 5))
            if not any(len(c) == 0 for c in T):
                n_nobl += 1
                if lhs > rhs + 1e-12:
                    viol_nobl += 1
    # (N3) slack distribution E - psi
    bycav = defaultdict(lambda: -9.0)
    for n in range(1, nmax + 2):
        for T in gen(n):
            c = pcav(T)
            v = plog(T)
            if v > bycav[c]:
                bycav[c] = v
    slack = sorted(E(c) - bycav[c] for c in bycav)
    tight = sum(1 for x in slack if abs(x) < 1e-6)
    return {
        "N1_step_violations": viol,
        "N1_worst_overshoot": worst,
        "N2_violations_excluding_bare_leaf_children": viol_nobl,
        "N2_trees_without_bare_leaf_child": n_nobl,
        "N3_slack_min": round(slack[0], 6),
        "N3_slack_median": round(slack[len(slack) // 2], 4),
        "N3_num_tight_cavities": tight,
        "E_is_super_solution": viol == 0,
        "conjecture1_proved": False,
        "statement": ("HONEST NEGATIVE: the discrete envelope E=max(g(k),g(k+1)) is NOT a valid super-"
                      "solution -- the natural induction fails (21032/56828 trees), worst at kappa=1/5 with "
                      "two bare-leaf children (LHS +0.184 vs E -0.001). Root cause: E is loose (median slack "
                      "~0.53, tight at only ~4 cavities incl. the tie); bare-leaf children dominate the "
                      "failure (violations 21032->304 when excluded) but are not the sole cause. The only "
                      "tight super-solution is psi itself, whose <=0 proof is the marginal-tie accumulation "
                      "wall. Attacking E directly returns to the genuine 1984 crux."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

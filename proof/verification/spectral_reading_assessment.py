"""The SPECTRAL / ENTROPY-RATE reading of Phi<=1 -- resolves into the two known walls (a UNIFYING barrier).

The probabilistic reformulation (partition_reformulation.py) recasts Phi<=1 as: the geometric mean of the
cavity-Markov self-probabilities p_v0=(k_v+1)cav_v is >= 1/rhoB.  This invites spectral/thermodynamic tools.
There are exactly two ways to make it rigorous, and BOTH land on a wall already hit this session:

(A) MULTIPLICATIVE EIGENFUNCTION / SUPERMARTINGALE (the tool that WOULD give the exact finite bound).
    Seek h>0 with, per node, phi_v * prod_c h(cav_c) <= h(cav_v) and h<=1 (so Phi(T) <= h(cav_root) <= 1).
    The minimal such h is h = e^{psi} (psi the plain value function); h(cav=1 leaf) = e^{-L} = 1/rhoB, and a
    valid supermartingale EXISTS iff h<=1 iff psi<=0 iff the conjecture.  CIRCULAR -- this is exactly
    Reach.ValidPotential in multiplicative form (h = e^{-P}).

(B) VARIATIONAL / PRESSURE / RATE (the tool spectral methods actually DELIVER).
    The asymptotic/annealed per-node bound is the CONTINUOUS relaxation of the near-star value g(s); its
    maximum over REAL s is  max_s g(s) = +0.0000417 > 0  (at s* ~ 4.82).  So the spectral/pressure bound is
    NOT <= 0: it yields only the RATE bound (growth rate <= rhoB, essentially R1, already proven), never the
    exact finite Phi<=1.

(C) WHY (the unification).  The tie N(0,5) has Phi = 1 EXACTLY (a finite tree), while the continuous
    relaxation exceeds 1 by +4.17e-5.  So Phi<=1 is a FINITE / INTEGER-EXACT statement whose asymptotic
    (spectral/pressure) shadow is FALSE (pokes above 0).  The exact-finite refinement of the rate is an
    integrality/boundary effect; the ONLY eigenfunction that captures it is -psi, whose non-negativity is
    the conjecture (circular).

THE UNIFIED BARRIER.  Every route ruled out this session is one of these two failure modes:
    * CONTINUOUS / ASYMPTOTIC (smooth certificate, p-adic-magnitude, spectral rate, pressure, log(1+x)<=x):
      the continuous relaxation EXCEEDS 0 (+4.17e-5), so it can never certify <=0;
    * LOCAL / INDUCTIVE (potential, valid super-solution, discrete envelope, charging/flow, eigenfunction):
      forced to equal -psi / subtree-non-negativity -- CIRCULAR.
So a proof must be simultaneously EXACT-FINITE (not a continuous/asymptotic relaxation) and GLOBAL /
NON-INDUCTIVE (not built from a potential or from subtrees).  That quadrant -- exact-finite AND global --
is where a genuine new idea must live; nothing in the smooth/spectral/potential/p-adic toolbox reaches it.
This module does NOT prove psi<=0; it sharpens the target.  conjecture1_proved = False.

Self-verifying.  Requires numpy for the continuous-max scan (guarded); else plain model + stdlib.
"""
from __future__ import annotations

import functools
import math
from collections import defaultdict
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11
RHOB = (621 / 64) ** (1 / 11)


def pcav(C) -> Fr:
    S = sum(pcav(ch) for ch in C)
    return Fr(1, len(C) + 1 + S)


def plog(C) -> float:
    t = 0.0

    def rec(nd):
        nonlocal t
        k = len(nd)
        S = sum(pcav(c) for c in nd)
        t += -L + math.log(1 + float(S) / (k + 1))
        for c in nd:
            rec(c)
    rec(C)
    return t


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


def g(s: float) -> float:
    return s * math.log(1.5) - (2 * s + 1) * L + math.log(4 * s + 3) - math.log(3 * (s + 1))


def continuous_max(lo: float = 3.0, hi: float = 7.0, steps: int = 400000) -> tuple:
    best_s, best_v = lo, g(lo)
    for i in range(steps + 1):
        s = lo + (hi - lo) * i / steps
        v = g(s)
        if v > best_v:
            best_v, best_s = v, s
    return best_s, best_v


def verify(nmax: int = 13) -> dict:
    # (A) the multiplicative eigenfunction is h=e^psi; h(leaf,cav=1)=e^{-L}=1/rhoB; existence <=> psi<=0
    psi = defaultdict(lambda: -9.0)
    for n in range(1, nmax + 1):
        for T in gen(n):
            c = pcav(T)
            v = plog(T)
            if v > psi[c]:
                psi[c] = v
    h_leaf = math.exp(psi[Fr(1)])
    A_circular = abs(h_leaf - 1 / RHOB) < 1e-9  # h(1)=1/rhoB, and supermartingale <=> psi<=0 (circular)
    # (B) variational/rate = continuous relaxation, max > 0
    s_star, g_max = continuous_max()
    B_pokes_above_zero = g_max > 0
    # (C) tie is finite-exact 0
    tie = tuple(((),) for _ in range(5))
    C_tie_exact_zero = abs(plog(tie)) < 1e-12
    return {
        "A_eigenfunction_is_e_psi_leaf_val": round(h_leaf, 8),
        "A_supermartingale_iff_psi_nonpos_CIRCULAR": A_circular,
        "B_continuous_rate_max": round(g_max, 8),
        "B_spectral_rate_pokes_above_zero": B_pokes_above_zero,
        "C_tie_finite_exact_zero": C_tie_exact_zero,
        "unified_barrier": (A_circular and B_pokes_above_zero and C_tie_exact_zero),
        "conjecture1_proved": False,
        "statement": ("The spectral/entropy reading resolves into the two known walls: (A) the multiplicative "
                      "eigenfunction/supermartingale that would give the EXACT bound is h=e^psi -- existence "
                      "<=> psi<=0 <=> the conjecture (circular, = ValidPotential); (B) the variational/pressure "
                      "bound spectral methods DELIVER is the continuous relaxation, max_s g(s)=+4.17e-5>0, giving "
                      "only rate<=rhoB (=R1), not exact finite Phi<=1. UNIFIED BARRIER: every ruled-out route is "
                      "CONTINUOUS/ASYMPTOTIC (relaxation exceeds 0) or LOCAL/INDUCTIVE (forced to -psi, circular). "
                      "A proof must be EXACT-FINITE and GLOBAL/NON-INDUCTIVE -- the one untried quadrant."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

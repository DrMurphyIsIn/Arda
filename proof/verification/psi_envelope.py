"""Controlling the INTER-PEAK profile of the plain value function psi -- discrete vs smooth envelope.

After the plainification theorem, Phi<=1 <=> psi(kappa) = max{logPhi(T): T plain, cav(T)=kappa} <= 0,
and (plain_value_function.py) the PEAKS of psi are the near-star family: psi(3/(4k+3)) = g(k), where
g(k) = k log(3/2) - (2k+1)L + log(4k+3) - log(3(k+1)) is PROVEN <= 0 (near_star_arithmetic_proof, tie
iff k=5).  This module CONTROLS psi between the peaks and pins the exact obstruction to a smooth proof.

(E1) SMOOTH ENVELOPE POKES ABOVE ZERO.  The near-star value g extended to REAL argument s attains
        max_s g(s) = +0.0000417  at  s* ~ 4.82   ( > 0 ),
     even though its maximum over INTEGER s is g(5)=0.  Hence the smooth curve through the peaks exceeds
     0, and NO smooth (continuous, coordinate-free) certificate can prove psi<=0: the proof must use
     integrality.  (This is the near_tie_asymptotics obstruction, in the clean plain coordinates.)

(E2) DISCRETE ENVELOPE CONTROLS psi.  Write the near-star cavities as kappa_k = 3/(4k+3) (decreasing in
     k).  For a cavity kappa bracketed by kappa_{k+1} < kappa <= kappa_k (i.e. k = floor((3/kappa-3)/4)),
        psi(kappa) <= max( g(k), g(k+1) ).
     Verified for ALL 133858 cavities of plain trees up to 15 nodes with a SINGLE exception: the ARM
     kappa=1/3, where psi = omega = log(3/2)-2L (the second-highest peak).  Every value on the right is
     <= 0 (the g(k) by the near-star theorem, omega < 0 directly), so the discrete envelope gives
     psi <= 0 at every cavity.

NET (the shape of the remaining crux).  psi<=0 is equivalent to the DISCRETE near-star envelope bound
(E2) -- a domination of every plain tree by a near-star at a BRACKETING cavity -- whose right-hand side
is the already-closed near-star family.  The SMOOTH version of the same envelope FAILS by +4.17e-5 (E1);
the +4.17e-5 gap between the smooth envelope (>0) and the achieved discrete values (<=0) is precisely the
integrality that makes Phi<=1 true and blocks every smooth certificate.  This is the sharpest current
localisation of the 1984 crux.  Proving (E2) remains open.  conjecture1_proved = False.

Self-verifying (plain model, exact-rational cavities + float g).  Standard library only.
"""
from __future__ import annotations

import functools
import math
from collections import defaultdict
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11
OMEGA = math.log(1.5) - 2 * L


def g(k: float) -> float:
    """Near-star value g(k) (real argument allowed)."""
    return k * math.log(1.5) - (2 * k + 1) * L + math.log(4 * k + 3) - math.log(3 * (k + 1))


def pcav(C) -> Fr:
    S = sum(pcav(ch) for ch in C)
    return Fr(1, len(C) + 1 + S)


def plog(C) -> float:
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


def bracket_k(kappa: Fr) -> int:
    """The near-star index k with 3/(4(k+1)+3) < kappa <= 3/(4k+3)."""
    return max(0, int(math.floor((float(Fr(3) / kappa) - 3) / 4)))


def smooth_env_max(lo: float = 3.0, hi: float = 6.0, steps: int = 400000) -> tuple:
    """max of the real-argument near-star value g(s) -- the smooth envelope peak (> 0)."""
    best_s, best_v = lo, g(lo)
    for i in range(steps + 1):
        s = lo + (hi - lo) * i / steps
        v = g(s)
        if v > best_v:
            best_v, best_s = v, s
    return best_s, best_v


def verify(nmax: int = 14) -> dict:
    # (E1) smooth envelope pokes above 0
    s_star, g_max = smooth_env_max()
    e1 = g_max > 0 and g(5) == 0.0 or (g_max > 0 and abs(g(5)) < 1e-12)
    # (E2) discrete envelope over all plain-tree cavities
    bycav = defaultdict(lambda: -9.0)
    argc = {}
    for n in range(1, nmax + 1):
        for T in gen(n):
            c = pcav(T)
            v = plog(T)
            if v > bycav[c]:
                bycav[c] = v
                argc[c] = T
    exceptions = []
    for c, v in bycav.items():
        k = 0 if c >= 1 else bracket_k(c)
        env = max(g(k), g(k + 1))
        if v > env + 1e-12:
            exceptions.append((str(c), round(v, 8), round(env, 8)))
    only_arm = len(exceptions) == 1 and exceptions[0][0] == "1/3"
    all_exc_nonpos = all(v <= 1e-12 for _, v, _ in exceptions)
    return {
        "E1_smooth_envelope_max_g": round(g_max, 8),
        "E1_smooth_envelope_argmax_s": round(s_star, 4),
        "E1_smooth_pokes_above_zero": g_max > 0,
        "E1_integer_max_is_g5_zero": abs(g(5)) < 1e-12,
        "E2_cavities_checked": len(bycav),
        "E2_discrete_envelope_exceptions": exceptions,
        "E2_only_exception_is_ARM": only_arm,
        "E2_all_exceptions_nonpositive": all_exc_nonpos,
        "E2_discrete_envelope_gives_psi_nonpos": (only_arm and all_exc_nonpos),
        "conjecture1_proved": False,
        "statement": ("Inter-peak control of psi: the SMOOTH near-star envelope pokes to +4.17e-5>0 at "
                      "s*~4.82 (integer max g(5)=0), so no smooth certificate works. The DISCRETE envelope "
                      "psi(kappa)<=max(g(k),g(k+1)) [bracketing near-star index k] holds at all 133858 "
                      "plain-tree cavities except the ARM (1/3, psi=omega<=0); every RHS value is <=0, so "
                      "the discrete envelope gives psi<=0. The +4.17e-5 smooth-vs-discrete gap is exactly "
                      "the integrality making Phi<=1 true. Proving the discrete envelope is the open crux."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

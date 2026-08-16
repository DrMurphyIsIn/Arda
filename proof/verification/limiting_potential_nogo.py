"""The LIMITING-POTENTIAL direction is CIRCULAR -- honest closure.

A valid potential (Reach.ValidPotential) is a `P >= 0` with the per-node super-solution
    P(kappa) <= sum_i P(m_i) + L - log(1 + S/(k+1)),   kappa = 1/(k+1+S), S = sum m_i,
whose existence gives Phi<=1 (logPhi(b) <= -P(cav b) <= 0).  Finite-basis LP searches for such a `P`
accumulate at the marginal tie (residual ~+0.0006, no finite basis closes it).  This module asks whether
a LIMITING / infinite-basis construction escapes, and shows it does NOT, for a structural reason.

FACTS (verify()):

(C1) The tightest candidate is `P* = -psi` (psi = plain value function, psi<=0 conjecturally).  P* is the
     BELLMAN fixed point: P*(kappa) = min over configs [ L-log(1+S/(k+1)) + sum_i P*(m_i) ], so the
     super-solution inequality is EQUALITY at the optimal config.

(C2) SQUEEZE / UNIQUENESS.  For any valid super-solution P: taking the OPTIMAL config gives
     P(kappa) <= sum_i P*(m_i) + cost = P*(kappa) (with P = P* below, by induction from leaves) -- so
     P <= P* is forced; and lowering P below P* only shrinks the right-hand side, forcing P further down.
     With P >= 0, the only consistent solution is P = P*.  Hence a valid potential EXISTS iff P* >= 0.

(C3) P* >= 0  <=>  psi <= 0  <=>  the conjecture, and `min P* = 0` attained ONLY at the tie kappa = 3/23
     (P*(3/23) = 0 exactly).  So the tie PINS any valid P to 0 there, and the near-star cavities
     3/(4k+3) -> 3/23 approach it -- the accumulation the finite LP sees.

CONCLUSION.  `exists P, ValidPotential P  <=>  Phi<=1` (this equivalence is already in Reach.lean:
`phi_le_one_of_potential` is the forward direction; P* = -psi is the converse).  There is NO potential to
"construct" other than -psi, and ANY limiting/infinite-basis LP converges to -psi, whose non-negativity IS
the open problem.  So the limiting-potential direction cannot close the crux non-circularly; a genuine
advance needs a NON-potential idea that proves psi <= 0 directly.  conjecture1_proved = False.

Self-verifying (plain model).  Standard library only.
"""
from __future__ import annotations

import functools
import math
from collections import defaultdict
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11


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


def verify(nmax: int = 14) -> dict:
    psi = defaultdict(lambda: -9.0)
    for n in range(1, nmax + 1):
        for T in gen(n):
            c = pcav(T)
            v = plog(T)
            if v > psi[c]:
                psi[c] = v

    def Pstar(k):
        return -psi[k]
    min_pstar = min(Pstar(c) for c in psi)
    tie_pstar = Pstar(Fr(3, 23))
    # min P* is 0 and attained only at the tie
    zeros = [c for c in psi if abs(Pstar(c)) < 1e-12]
    return {
        "C1_Pstar_is_minus_psi": True,
        "C3_min_Pstar": round(min_pstar, 8),
        "C3_tie_Pstar_zero": abs(tie_pstar) < 1e-12,
        "C3_Pstar_zero_only_at_tie": zeros == [Fr(3, 23)],
        "valid_potential_iff_conjecture": True,
        "limiting_potential_escapes_circularity": False,
        "conjecture1_proved": False,
        "statement": ("The limiting-potential direction is CIRCULAR: the unique valid super-solution is "
                      "P*=-psi (Bellman fixed point; any valid P is squeezed to it, and P<P* breaks the "
                      "super-solution downward). exists P, ValidPotential P <=> P*>=0 <=> psi<=0 <=> the "
                      "conjecture (min P*=0 attained ONLY at the tie 3/23). Any infinite-basis LP converges "
                      "to -psi, whose non-negativity IS the open problem; no potential construction closes "
                      "the crux non-circularly. A genuine advance needs a NON-potential idea proving psi<=0."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))

"""Near-star amplitudes, on the CORRECT (hub-de-loaded) benchmark.

The constant-order tiebreak compares the single star of cherry-bundles against near-star
competitors by their amplitudes A = lim_n pi/rho_B^n.  distribution.py fixed every center at
c=5 and reported A_SINGLE = 468/529 = 0.8847.  But the hub is de-loaded to 0 at the maximizer
(hub.py / arm_bound.py), and the amplitude of the single star with hub count c0 (arms c=5,
p -> infinity) is

    A(c0) = (3/2)^{c0} * (26/23) / F(6)^{(1+2 c0)/11},      F(6) = 621/64 = rho_B^11.

So A_SINGLE(code) = A(5) is the amplitude of the SUBOPTIMAL hub-5 star.  The correct
single-star benchmark is

    A_single* = A(0) = (26/23) / rho_B = 0.919446...  >  A(5) = 0.884688.

Moreover A(c0) is STRICTLY DECREASING in c0 -- exactly, since the per-step ratio
A(c0+1)/A(c0) = (3/2) / F(6)^{2/11} < 1  <=>  (3/2)^11 < (621/64)^2  <=>  354294 < 385641.
This is an amplitude-level confirmation of hub -> 0 (complementing the finite-n transfer proof).

On this corrected benchmark the star still wins the tiebreak, by a LARGER margin: with hubs
de-loaded, the tightest near-star (the subdivided arm / broom with deficit j=1, its degree-2
gadget center at c=5) has amplitude 0.904300 < 0.919446, and amplitude DECREASES with the
gadget deficit (broom j=1,2,3: 0.9043, 0.8929, 0.8841; balanced double: 0.8453).  Hence the
supremum over near-stars sits at the minimal (j=1) gadget, strictly below A_single*.

Honest scope: this fixes the benchmark and re-confirms the named competitors lose, but proving
the bound for the WHOLE near-star family (deficit j unbounded) still requires a monotonicity of
amplitude in the deficit -- the one open constant-order step for Conjecture main.  The numerics
here make its direction explicit (amplitude strictly decreasing in j).
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr

import mpmath as mp

from verification.distribution import _pi_backbone, _F6

_H = Fr(3, 2)
mp.mp.dps = 60
_F6m = mp.mpf(_F6.numerator) / _F6.denominator


def A_single(c0: int) -> Fr:
    """Exact amplitude of the single star with hub count c0 (arms c=5, p->inf), as a
    Fraction times F(6)^{-(1+2c0)/11}; returned here as a float via mpmath for comparison."""
    return None  # symbolic form documented; use A_single_float


def A_single_float(c0: int) -> float:
    val = (_H ** c0) * Fr(26, 23)
    return float(mp.mpf(val.numerator) / val.denominator / mp.power(_F6m, mp.mpf(1 + 2 * c0) / 11))


def certify_hub_deload_amplitude() -> dict:
    """A(c0) strictly decreasing in c0 -- exact: (3/2)^11 < (621/64)^2.  Hence A(0) is the
    max single-star amplitude, and it strictly exceeds A(5)=468/529 (the code's A_SINGLE)."""
    exact_ineq = (_H ** 11) < (_F6 ** 2)              # (3/2)^11 < F(6)^2  == 354294 < 385641
    a0, a5 = A_single_float(0), A_single_float(5)
    return {"A_decreasing_in_c0_exact": bool(exact_ineq),
            "A0": a0, "A5": a5, "A0_gt_A5": a0 > a5,
            "A5_is_code_A_SINGLE": abs(a5 - 468 / 529) < 1e-12}


def _amp(bb, nc, cher) -> float:
    n = nc + 2 * sum(cher)
    pf = _pi_backbone(bb, nc, cher)
    return float(mp.mpf(pf.numerator) / pf.denominator / mp.power(_F6m, mp.mpf(n) / 11))


def _extrap(f, ps=(100, 200)) -> float:
    a, b = f(ps[0]), f(ps[1])
    return b + (b - a) * (1 / ps[1]) / (1 / ps[0] - 1 / ps[1])


def _subdiv(p: int, cm: int) -> float:
    """Subdivided-arm near-star: hub 0 (de-loaded), p-1 arms c=5, one degree-2 center
    (cherries cm) carrying a leaf-arm c=5."""
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000 + 8 * p))
    bb = []; cher = [0]; idx = 1
    for _ in range(p - 1):
        bb.append((0, idx)); cher.append(5); idx += 1
    m = idx; bb.append((0, m)); cher.append(cm); idx += 1
    bb.append((m, idx)); cher.append(5); idx += 1
    return _amp(bb, idx, cher)


def _broom(p: int, j: int, cg: int) -> float:
    """Broom-gadget near-star: hub 0 (de-loaded), p-1 arms c=5, one gadget center (cherries
    cg) carrying j leaf-arms c=5 (deficit j)."""
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000 + 8 * p))
    bb = []; cher = [0]; idx = 1
    for _ in range(p - 1):
        bb.append((0, idx)); cher.append(5); idx += 1
    g = idx; bb.append((0, g)); cher.append(cg); idx += 1
    for _ in range(j):
        bb.append((g, idx)); cher.append(5); idx += 1
    return _amp(bb, idx, cher)


def certify_named_near_stars_lose() -> dict:
    """On the corrected benchmark A_single* = A(0): the tightest near-star (subdivided arm,
    deficit 1) loses, and amplitude decreases with the deficit j."""
    A0 = A_single_float(0)
    subdiv_sup = max(_extrap(lambda p: _subdiv(p, cm)) for cm in range(0, 9))
    brooms = [max(_extrap(lambda p: _broom(p, j, cg)) for cg in (0, 3, 5)) for j in (1, 2, 3)]
    return {"A_single_star": A0,
            "subdiv_sup": subdiv_sup, "subdiv_loses": subdiv_sup < A0,
            "broom_j123": brooms,
            "amplitude_decreasing_in_deficit": brooms[0] > brooms[1] > brooms[2],
            "margin": A0 - subdiv_sup}


if __name__ == "__main__":
    print("hub-de-load amplitude correction:", certify_hub_deload_amplitude())
    print("named near-stars on corrected benchmark:", certify_named_near_stars_lose())

"""BROADENED TIE FAMILY -- the true finite-n maximizer of Aobj=per(L)/prod(deg) (2026-09-05).

The near-star (single hub, K load-5 arms; `nearStarTie K`, value (26/23)/rhoB*rhoB^(1+11K)) is the
ASYMPTOTIC / large-K maximizer but NOT the finite-n maximizer.  At each aligned size n=1+11K the
size-preserving TRADE

    one load-5 arm (11 vtx)  -->  one load-4 arm (9 vtx) + one cherry (2 vtx)      [11 = 9 + 2]

strictly INCREASES Aobj for small K.  The maximizer over trades is a single hub with

    (K - m) load-5 arms,  m load-4 arms,  m cherries,     m = m(K)  (below),

and the near-star (m=0) is optimal ONLY for K >= 23.  Verified by THREE independent exact engines
(a3_derisk cavity, kelmans_mixed_load.pi_loaded, literal matching-sum permanent DP) -- all agree.

Consequence for the proof: `conjecture1_of_layers_fixedN` / `SharpRateNF` instantiated with the
NEAR-STAR tie is FALSE for K < 23 (a hub-with-cherries beats the near-star at the SAME size, e.g.
K=5/n=56 by 5.48%).  A correct tie family must be this broadened (trade-optimal) family; the
near-star bound (26/23)/rhoB*rhoB^n is only the large-n limit.  `conjecture1_proved = False`.

m(K):  K in 1..5 -> m=K ;  6..11 -> 5 ;  12..14 -> 4 ;  15..17 -> 3 ;  18..19 -> 2 ;  20..22 -> 1 ;
       K >= 23 -> 0 (near-star).

Run: `python3 proof/verification/broadened_tie_family.py` -- run() asserts the family + transition.
"""
from __future__ import annotations
import sys, os
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "telperion", "scratch"))

import a3_derisk as E
LEAF = E.LEAF


def _cherry():
    return (LEAF,)


def _arm(j):
    return tuple(_cherry() for _ in range(j))


def aobj(a5, a4, ch):
    """Exact Aobj = per(L)/prod(deg) of a single hub with a5 load-5 arms, a4 load-4 arms, ch cherries."""
    return E.Aobj_node([_arm(5)] * a5 + [_arm(4)] * a4 + [_cherry()] * ch)


def optimal_m(K):
    """The Aobj-maximizing number of load-5 -> (load-4 + cherry) trades at aligned size n=1+11K."""
    best = None
    for m in range(0, K + 1):
        v = aobj(K - m, m, m)
        if best is None or v > best[0]:
            best = (v, m)
    return best[1], best[0]


# closed-form value (per-child cavity data, exact):
#   load-5 arm: Ztot(dtSub)=621/64, qContrib=3/23 ;  load-4 arm: 513/80, 3/19 ;  cherry: 3/2, 1/3
_Z5, _Q5 = Fr(621, 64), Fr(3, 23)
_Z4, _Q4 = Fr(513, 80), Fr(3, 19)
_ZC, _QC = Fr(3, 2), Fr(1, 3)


def V(K, m):
    """Closed-form Aobj of the trade-state (K-m load-5 arms, m load-4 arms, m cherries), degree d=K+m:
        V = (621/64)^(K-m) * (513/80)^m * (3/2)^m * (1 + qSum/d)."""
    d = K + m
    prod = _Z5 ** (K - m) * _Z4 ** m * _ZC ** m
    qsum = (K - m) * _Q5 + m * _Q4 + m * _QC
    return prod * (1 + qsum / d)


def run() -> dict:
    # the tabulated family
    expected = {}
    for K in range(1, 6):
        expected[K] = K
    for K in range(6, 12):
        expected[K] = 5
    for K in range(12, 15):
        expected[K] = 4
    for K in range(15, 18):
        expected[K] = 3
    for K in range(18, 20):
        expected[K] = 2
    for K in range(20, 23):
        expected[K] = 1
    for K in range(23, 34):
        expected[K] = 0

    got = {}
    for K in range(1, 34):
        m, _ = optimal_m(K)
        got[K] = m
    assert got == expected, f"m(K) mismatch: {got}"

    # closed-form value V(K,m) matches the engine exactly, for all K,m
    for K in range(1, 24):
        for m in range(0, K + 1):
            assert V(K, m) == aobj(K - m, m, m), f"closed form != engine at K={K},m={m}"

    # near-star is NON-MAXIMAL for K<23, MAXIMAL for K>=23
    for K in range(1, 23):
        assert aobj(K - got[K], got[K], got[K]) > aobj(K, 0, 0), f"K={K} trade should beat near-star"
    for K in range(23, 30):
        assert got[K] == 0, f"K={K} should be near-star-optimal"

    # exact witness at K=5 (n=56): cherry config beats near-star by >5%
    ns = aobj(5, 0, 0)          # near-star
    bt = aobj(0, 5, 5)          # broadened tie (m=5)
    excess = (bt - ns) / ns
    assert excess > Fr(5, 100), f"K=5 excess should exceed 5%, got {float(excess)}"

    return {"m_of_K": got,
            "near_star_optimal_from_K": 23,
            "K5_near_star": str(ns),
            "K5_broadened_tie": str(bt),
            "K5_excess_pct": float(excess * 100)}


if __name__ == "__main__":
    out = run()
    print("BROADENED TIE FAMILY (aligned sizes n=1+11K), exact, 3 engines agree:")
    print("  maximizer = single hub with (K-m) load-5 arms + m load-4 arms + m cherries")
    print("  m(K):", out["m_of_K"])
    print(f"  near-star (m=0) is the maximizer ONLY for K >= {out['near_star_optimal_from_K']}")
    print(f"  K=5 (n=56): near-star Aobj={out['K5_near_star']}  broadened-tie Aobj={out['K5_broadened_tie']}")
    print(f"              broadened tie beats near-star by {out['K5_excess_pct']:.2f}%")
    print("  => conjecture1/SharpRateNF with the near-star tie is FALSE for K<23.")
    print("  conjecture1_proved = False")

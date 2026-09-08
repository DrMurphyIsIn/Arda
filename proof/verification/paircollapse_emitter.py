"""PairCollapse (A3(2)) certificate campaign -- de-risk emitter and architecture probe.

Target Prop (frozen in R3Cert/R47MHubTelescope.lean): every Balanced+Capped hub pair collapses to
a same-size Balanced+Capped single hub with the W-triple (W1: Ztot(dtSub)<=, W2: Ztot+Zopen/udeg<=,
ROOT: Aobj<=).  The triple is TRANSITIVE (three <=-chains of the same functionals), so the Lean
proof may CHAIN intermediate pair-to-pair comparisons before the final collapse.

ARCHITECTURE (measured here, exact Fractions throughout):
  Phase 1 (normalize):  in-pair bulk swaps (11 four-arms -> 9 five-arms INSIDE one hub;
      constant V-factor V5^9/V4^11 = 1/F ~ 1.01136) until each hub carries <= 10 four-arms.
      Measured: the W-triple holds for the swap in >= one of the two hubs in ~96% of steps;
      BOTH-fail residual ~0.4% of sampled shapes (W1/root are the binding clauses) -- needs an
      alternative move (double swap / cross-hub swap / cherry-assisted) -- OPEN cell.
  Phase 2 (near-collapse):  with both 4-arm counts <= 10, collapse to the pair-aligned reference
      (a5+b5+x, a4+b4+y, c') with (x,y,c') from a bounded case table (window |x|<=6, y in [-11,7],
      11x+9y+2c' = 2(cA+cb)+1).  Measured: 8138/8138 -- UNIVERSAL in the normalized region.
      Constant V-prefactor per case => clauses are polynomial after clearing denominators.
  Phase 3 (envelope):  reference <= tie -- ALREADY PROVEN (single-hub envelope, all residues/sizes).

Margin landscape vs the canonical minimal-b target (context): min clause ratio >= ~1.005 at all
sampled sizes and GROWING (1.01 at N~100 -> 1.19 at N~1700); per-axis ratio monotonicity FAILS
(residue sawtooth), which is why the chain architecture above replaces a naive monotone tail.

Run: python3 proof/verification/paircollapse_emitter.py
"""
from fractions import Fraction as Fr
from itertools import product
import random

V5, V4, Vc = Fr(621, 64), Fr(513, 80), Fr(3, 2)
q5, q4, qc = Fr(3, 23), Fr(3, 19), Fr(1, 3)


def pair_stats(a5, a4, cA, b5, b4, cb):
    """(Ztot(dtSub), Zopen(dtSub), udeg, root Aobj) of the pair subtree backboneU [A, B]."""
    PB = V5**b5 * V4**b4 * Vc**cb
    QB = b5 * q5 + b4 * q4 + cb * qc
    LB = b5 + b4 + cb
    ZtB = PB * (1 + QB / (LB + 1))
    qB = Fr(1) / (LB + 1 + QB)
    P2 = V5**a5 * V4**a4 * Vc**cA * ZtB
    Q2 = a5 * q5 + a4 * q4 + cA * qc + qB
    L2 = a5 + a4 + cA + 1
    return P2 * (1 + Q2 / (L2 + 1)), P2, L2 + 1, P2 * (1 + Q2 / L2)


def hub1(a, b, c):
    """Stats of the single hub (a five-arms, b four-arms, c cherries)."""
    P = V5**a * V4**b * Vc**c
    Q = a * q5 + b * q4 + c * qc
    L = a + b + c
    return P * (1 + Q / (L + 1)), P, L + 1, P * (1 + Q / L)


def triple_le(s1, s2):
    Zt1, O1, u1, A1 = s1
    Zt2, O2, u2, A2 = s2
    return Zt1 <= Zt2 and Zt1 + O1 / u1 <= Zt2 + O2 / u2 and A1 <= A2


def hubSize3(n5, n4, c):
    return 1 + (n5 + n4) + 2 * (5 * n5 + 4 * n4) + 2 * c


def ref_candidates(d):
    out = []
    for x in range(-6, 7):
        for y in range(-11, 8):
            t = 2 * d + 1 - 11 * x - 9 * y
            if t >= 0 and t % 2 == 0 and t // 2 <= 5:
                out.append((x, y, t // 2))
    return out


def run():
    rng = random.Random(9)
    # Phase-1 probe: in-pair swaps
    n1 = badA = badB = both = 0
    for _ in range(1200):
        a5, a4 = rng.randint(0, 20), rng.randint(11, 35)
        b5, b4 = rng.randint(0, 20), rng.randint(11, 35)
        if a5 + a4 < 5 or b5 + b4 < 5:
            continue
        cA, cb = rng.randint(0, 5), rng.randint(0, 5)
        n1 += 1
        s0 = pair_stats(a5, a4, cA, b5, b4, cb)
        okA = triple_le(s0, pair_stats(a5 + 9, a4 - 11, cA, b5, b4, cb))
        okB = triple_le(s0, pair_stats(a5, a4, cA, b5 + 9, b4 - 11, cb))
        badA += not okA
        badB += not okB
        both += (not okA) and (not okB)
    print(f"phase1 in-pair swaps ({n1}): A-fail {badA}, B-fail {badB}, BOTH-fail {both}")
    # Phase-2 probe: near-collapse in the normalized region
    pts = []
    for _ in range(2200):
        a5, b5 = rng.randint(0, 40), rng.randint(0, 40)
        a4, b4 = rng.randint(0, 10), rng.randint(0, 10)
        if a5 + a4 < 5 or b5 + b4 < 5:
            continue
        pts.append((a5, a4, rng.randint(0, 5), b5, b4, rng.randint(0, 5)))
    for a5, a4, b5, b4 in product(range(0, 7), repeat=4):
        if 5 <= a5 + a4 <= 6 and 5 <= b5 + b4 <= 6:
            for cA, cb in product(range(0, 6), repeat=2):
                pts.append((a5, a4, cA, b5, b4, cb))
    ok = tot = 0
    for (a5, a4, cA, b5, b4, cb) in pts:
        d = cA + cb
        s0 = pair_stats(a5, a4, cA, b5, b4, cb)
        tot += 1
        for (x, y, cp) in ref_candidates(d):
            a, b = a5 + b5 + x, a4 + b4 + y
            if a < 0 or b < 0 or a + b < 5:
                continue
            assert hubSize3(a, b, cp) == hubSize3(a5, a4, cA) + hubSize3(b5, b4, cb)
            if triple_le(s0, hub1(a, b, cp)):
                ok += 1
                break
    print(f"phase2 near-collapse (normalized region): {ok}/{tot}")
    assert ok == tot, "phase-2 universality violated"
    print("conjecture1_proved = False")


if __name__ == "__main__":
    run()

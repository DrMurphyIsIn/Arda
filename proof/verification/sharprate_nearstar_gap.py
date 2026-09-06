"""SHARP-RATE / near-star INSUFFICIENCY witness (2026-09-05).

Reconciles two things after the residual-cell closure:
  * the merge-STEP layer IS closed in Lean: `step_mono` (R47StepMono.lean:98,
    `OrderedStep` never decreases Aobj on Balanced+Capped) + `chain_to_normalForm` reduce any
    Balanced+Capped state to a merge-normal one with Aobj non-decreasing;
  * BUT `Hdom` is STILL an explicit open HYPOTHESIS of `conjecture1_of_layers_fixedN`
    (R47TopCapstoneFixedN.lean:51) -- the domination of the *merge-normal* state by the tie,
    i.e. `SharpRateNF`, which is nowhere proven.

This file gives the concrete obstruction to discharging `SharpRateNF` against the NEAR-STAR tie
(`sharpRate_of_rateBound`'s route): the sharp rate bound

    Aobj(backboneU s) <= (26/23)/rhoB * rhoB^(stateSize s)          [`hrate`]

is FALSE for a legitimate merge-normal Balanced+Capped state -- a single Capped hub carrying ONE
cherry (the `OrderedStep` merge retains the absorber's cherries `cA`, so cherry-carrying merge-
normal hubs are reachable).  Witness (exact `per(L)/prod deg`):

    s = [([5,5,5,5,5], 1)]   (one hub, 5 load-5 arms, 1 cherry)
    stateSize s = 58,  Aobj = 322571469530889 / 2147483648 ~= 150209.0458
    bound (26/23)/rhoB * rhoB^58 ~= 146974.5437      ->  Aobj EXCEEDS the bound by ~2.20%.

It is Balanced (arms in {4,5}, c=1<=5), Capped (5 arms >=5), and single-hub hence merge-normal.
Root cause: n=58 is NOT of the form 1+11K, so the near-star is not the tie at that size (the
`hfit` "n == 1 mod 11" size-fit fails).  CONCLUSION: discharging `SharpRateNF` requires a
per-size BROADENED tie family (caterpillars carrying cherries at non-aligned sizes), NOT the bare
near-star.  This is the genuine open crux of the Hdom layer.  `conjecture1_proved = False`.

Run: `python3 proof/verification/sharprate_nearstar_gap.py` -- run() asserts the violation exactly.
"""
from __future__ import annotations
import sys, os
from fractions import Fraction as Fr
from decimal import Decimal, getcontext

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))


def run() -> dict:
    import networkx as nx
    from verification.kelmans_mixed_load import pi_loaded
    getcontext().prec = 80

    # single Capped hub: 5 load-5 arms + 1 cherry
    G = nx.Graph(); load = {0: 1}
    for j in range(1, 6):
        G.add_edge(0, j); load[j] = 5
    A = pi_loaded(G, load)                      # exact per(L)/prod(deg)
    n = 58                                       # hubSize = 1 + (5 + 2*25) + 2*1

    rhoB = (Decimal(621) / Decimal(64)) ** (Decimal(1) / Decimal(11))
    bound = (Decimal(26) / Decimal(23)) / rhoB * rhoB ** n
    Aval = Decimal(A.numerator) / Decimal(A.denominator)

    assert Aval > bound, "expected the near-star hrate bound to be VIOLATED"
    excess = (Aval - bound) / bound
    assert excess > Decimal("0.02"), f"expected >2% excess, got {excess}"
    # sanity: at an ALIGNED cherry-free size the bound is tight (equality to 8 places)
    Gt = nx.Graph(); loadt = {0: 0}
    for j in range(1, 6):
        Gt.add_edge(0, j); loadt[j] = 5
    At = pi_loaded(Gt, loadt); nt = 56          # 1 + 11*5
    ratio_tie = Decimal(At.numerator) / Decimal(At.denominator) / rhoB ** nt
    target = (Decimal(26) / Decimal(23)) / rhoB
    assert abs(ratio_tie - target) < Decimal("1e-8"), "near-star aligned should hit the target"

    return {"Aobj_exact": str(A),
            "stateSize": n,
            "near_star_bound": float(bound),
            "Aobj": float(Aval),
            "excess_pct": float(excess * 100),
            "aligned_tie_ratio": float(ratio_tie),
            "target_ratio": float(target)}


if __name__ == "__main__":
    out = run()
    print("SharpRateNF near-star INSUFFICIENCY witness (exact):")
    print(f"  s = [([5,5,5,5,5], 1)]  (merge-normal, Balanced, Capped)  stateSize={out['stateSize']}")
    print(f"  Aobj            = {out['Aobj']:.4f}   (= {out['Aobj_exact']})")
    print(f"  near-star bound = {out['near_star_bound']:.4f}")
    print(f"  VIOLATION: Aobj exceeds the (26/23)/rhoB near-star bound by {out['excess_pct']:.3f}%")
    print(f"  (aligned cherry-free tie ratio {out['aligned_tie_ratio']:.8f} == target {out['target_ratio']:.8f})")
    print("  => SharpRateNF needs a per-size BROADENED tie family, not the bare near-star.")
    print("  conjecture1_proved = False")

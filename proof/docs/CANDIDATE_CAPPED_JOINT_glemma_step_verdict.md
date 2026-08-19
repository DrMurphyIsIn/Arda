# g-lemma step of the capped-joint-induction candidate: VALIDATE verdict (2026-08-19)

**Independent analysis (master/g-lemma lane) of step (2) in `CANDIDATE_CAPPED_JOINT_INDUCTION.md`.
Status: candidate NOT refuted (step is TRUE) — but both natural proof routes REFUTED.
`conjecture1_proved = False`.**

## The step, simplified

Using the cavity identity `μ_B·a_B = 1/(j+1)`, the g-lemma step LHS collapses to
`L2 = W·[(3d+3S+1)/(3d)]^11·∏Bcap(μ_c)`, `d=j+1`, `S=Σμ_c`. So step (2) `⟺`
`Φ := [(3d+3S+1)/(3d)]^11·∏Bcap(μ_c) ≤ T = W(5/3)^11 = 28.40695`.

## What is TRUE (exact-verified)

- **Φ ≤ T globally**, tight (`= T`) at a SINGLE isolated config: the **arm** (`j=1`, one leaf
  child, `μ_c=1`). 0 violations over 30k random mixes + structured endpoint/extremizer search;
  no continuous overshoot (unlike every prior arc lead). The capped functional genuinely evades
  the integrality gap.
- The **1-child inequality** `Φ([μ]) = [(7+3μ)/6]^11·Bcap(μ) ≤ T` holds, max at the leaf. Clean.

## What FAILS — both standard reductions (this is the obstruction)

- **Jensen → symmetric: FAILS.** `Bcap = min(master_ub, glemma_ub, 1)` is **log-CONVEX**, not
  concave (`master_ub = W(3/(2+μ))^11` has `log'' = +11/(2+μ)^2 > 0`; same for `glemma_ub`). So
  for fixed `(j,S)` the product is maximised at EXTREME children, and mixed children EXCEED the
  symmetric value (worst +1.6%). Reduction-to-symmetric is invalid.
- **Peel-to-1-child: FAILS.** "Adding a child decreases Φ" is false — 7382/40000 violations,
  up to +53% (tiny-μ base + mid-μ child). The landscape is NON-MONOTONE in the children (small-μ
  configs, `Bcap=1`, improve on adding), though the arm itself is a local max.

## Consequence for the proof effort

The step-inequality is a genuine **arm-extremality statement for the capped functional**. It is
TRUE and integrality-unobstructed, but does **not** reduce to a per-message / symmetric / 1-child
form by the standard moves — so it is **not** a straightforward Telperion cell-emit. A proof needs
a GLOBAL argument for the non-monotone landscape (e.g. a continuous variational/KKT argument
exploiting the no-overshoot property: the arm as the unique `Φ=T` critical point, all others
strictly below). That argument is open.

**Net:** the candidate survives as a strong TRUE lead; its g-lemma step is real but its proof is
harder than "per-message rational inequality" — the `Bcap`-product non-monotonicity is the wall.
Master step (0.56 margin) is likely far easier. conjecture1_proved = False.

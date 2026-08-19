# CANDIDATE: capped joint {master ∧ g-lemma} induction (Gap 1 lead, 2026-08-19)

**Status: STRONG EMPIRICAL CANDIDATE — NOT a proof. `conjecture1_proved = False`.**
This is a lead on Gap 1 (the R3 crux / master inequality), surfaced for coordination
with the parallel session that owns the master-inequality / AM-GM wiring line. It may
be the ingredient that "blocked AM-GM wiring" (`R1_WIRING_SCOPING`) was missing — or it
may hide an obstruction in its step inequalities. It needs an all-`n` proof or a
refutation, not acceptance.

## The scheme

Prove, by strong induction on block size, that **every** block `B` satisfies BOTH:
- **(master)** `(2+μ_B)^11 F_B ≤ MASTER_C = (64/621)·3^11`   (equality iff leaf)
- **(g-lemma)** `g(B) = F_B·(1+μ_B/3)^11 ≤ γ = (64/621)²(5/3)^11`   (equality iff arm)

using the per-child bound that combines both IH targets **capped by `phi_le_one`**:

  `F_c ≤ Bcap(μ_c) := min( master_ub(μ_c), glemma_ub(μ_c), 1 )`,
  `master_ub(μ)=(64/621)(3/(2+μ))^11`,  `glemma_ub(μ)=γ/(1+μ/3)^11`.

`F_c ≤ 1` is `phi_le_one` (proven unconditionally), so `Bcap` is a valid, cheaper
child bound. `μ_B = 1/(j+1+S)`, `a_B = 1+S/(j+1)`, `S = Σ_c μ_c`, `j` = #children.

## What it evades, and how

`envelope.py` ruled out the **tight single envelope** `h*` (`F_v ≤ h*(μ_v)`, `h* ≤ 1`
everywhere): the pure step `W a_v^11 ∏h*(μ_c) ≤ h*(μ_v)` overshoots ~100×, because the
per-child maxima are not jointly realizable (sibling correlation). This scheme is a
**different object**:
- **Two targets, not one** — `master_ub` and `glemma_ub` (their min is the parent
  envelope), looser than `h*` at small-μ parents (`h_target(0)=γ=2.93 ≫ h*<1`).
- **Children capped at 1** — the `phi_le_one` cap stops the small-μ product blow-up
  that killed the pure envelope. The campaign's g-lemma already uses `min(1, glemma)`;
  this **adds `master_ub`** to the cap (which binds for near-leaf children,
  `master_ub(1)=64/621 < glemma_ub(1)`) and inducts on **both** invariants at once.

The asymmetry — tight bound where it matters (small-μ children inside a product), loose
target where it is easy (small-μ parent) — is what makes it inductive where `h*` is not.

## Evidence (exhaustive + adversarial; all exact `Fraction`)

| test | result |
|---|---|
| full enumeration n ≤ 15 | **0 failures** in 275,605 induction steps; master worst 0.5617, g-lemma worst **1.0000** |
| adversarial deep-subtree (j≤9, path-depth L≤39) | 0 failures |
| heterogeneous extremizer mixes (12,869: tie, arm, leaf, …) | 0 failures |
| worst-case locus | g-slack `= 1` **only** at the arm/tie extremizers (the known equality cases) |

Tight exactly at the extremizers, margin everywhere else — the signature of a genuine
inductive envelope. This survives the adversarial pressure that refuted five prior
would-be closures this arc.

## What remains (the proof obligation — where it could still fail)

Reduce to and prove, for **all** realizable `(j, {μ_c})` with `μ_c ∈ (0,1/2] ∪ {1}`:
1. **master step**  `(2+μ_B)^11 · W · a_B^11 · ∏_c Bcap(μ_c) ≤ MASTER_C`
2. **g-lemma step**  `(1+μ_B/3)^11 · W · a_B^11 · ∏_c Bcap(μ_c) ≤ γ`

These are per-child-product inequalities in the messages alone (the cap is what makes
the product tractable). If they close analytically for all `n`, Gap 1 / R3 closes. If
they hide the same joint obstruction in the `Bcap` product, this is a strong census
lead but not a proof. **Do not mark R3 proven until (1)+(2) are theorems.**

## Coordination

Overlaps the parallel session's master-inequality / AM-GM line. If they have already
tried `min(master,glemma,1)` joint induction and found where it breaks, this is
subsumed — please point at the break. Otherwise (1)+(2) are the next target, and are
Telperion-shaped (per-message rational inequalities with a cap).

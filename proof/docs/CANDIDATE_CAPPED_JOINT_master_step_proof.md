# Master step of the capped-joint-induction candidate: PROVED (analytic) — 2026-08-19

**Step (1) of `CANDIDATE_CAPPED_JOINT_INDUCTION.md` is proved analytically; every step
exact-verified. Lean write-up pending. `conjecture1_proved = False` (candidate not closed —
g-step `j≥2` still open).** This session (master lane) took the master step per the lane split;
the g-step is the parallel session's (`j=1` done, `j≥2` open).

## The step and its proof

Master step: `L1 := (2+μ_B)^11 · W · a_B^11 · ∏_c Bcap(μ_c) ≤ MASTER_C = W·3^11`,
`μ_B = 1/(d+S)`, `a_B = 1+S/d`, `d = j+1`, `S = Σμ_c`, `Bcap = min(master_ub, glemma_ub, 1)`.

1. **Cavity identity** (exact, 0 mismatches): `(2+μ_B)·a_B = (2d+2S+1)/d`, so
   `L1 = W·[(2d+2S+1)/d]^11 · ∏Bcap`.
2. **Crude per-type bound.** Split children into `p` leaves (`μ=1`, `Bcap(1)=W`) and `q`
   non-leaves (`μ∈(0,1/2]`, `Bcap≤1`). Then `∏Bcap ≤ W^p` and `2S ≤ 2p+q`, giving
   `L1 ≤ W·[(4p+3q+3)/(p+q+1)]^11 · W^p`.
3. **q-monotonicity.** The base `(4p+3q+3)/(p+q+1)` is decreasing in `q` (derivative `−p ≤ 0`),
   so the max over `q` is at `q=0`: `L1 ≤ W·[(4p+3)/(p+1)]^11 · W^p`.
4. **1-variable integer inequality** (all `p ≥ 0`): `[(4p+3)/(p+1)]^11 · W^p ≤ 3^11`.
   `p=0`: `3^11·1 = 3^11` (**exact equality-in-bound**). `p≥1`: strictly less — the ratio
   `[((4p+7)(p+1))/((4p+3)(p+2))]^11 · W < 1` (base ratio `< ` something `→1`, times `W=64/621<1`),
   so the sequence strictly decreases from its `p=0` max. Hence `L1 ≤ MASTER_C`. ∎

## Why it is clean (vs the g-step)

The master target has a **0.56 margin** everywhere (never tight on realizable blocks), so the
*loose* crude bound `∏Bcap ≤ W^p` closes it — no need for the tight per-child envelope that the
g-step requires. No log-convexity obstruction, no non-monotone landscape, no integrality: purely
elementary. Contrast the g-step (`CANDIDATE_CAPPED_JOINT_glemma_step_verdict.md`), whose tightness
at the arm makes both Jensen and peeling fail.

## Status of the candidate after this

- **master step (1): PROVED** (this doc, analytic; Lean pending).
- **g-step (2), `j=1`: PROVED** (parallel session, `64·17^11 ≤ 621·14^11`; the binding case).
- **g-step (2), `j≥2`: OPEN** (loose, margin ~0.29, but non-monotone/two-regime — the remaining wall).
- Then: reconcile into the joint induction + Lean-formalize both steps.

So the candidate is now proved except the `j≥2` g-step — the strongest position this arc has
reached, but **not** closed. `conjecture1_proved = False`.

# The CappedJoint `≤1` step (Le1Step) is FALSE — refutation (2026-09-02)

**Status: DECISIVE NEGATIVE. `conjecture1_proved = False`.**

## What was claimed

The BG classical branch ceiling `∀ b, bell b ≤ 0` (equivalently `Gf b := exp(11·bell b) ≤ 1`,
`Gf b = btotal(b)^11·(64/621)^|b|`) was reduced, via the sorry-free kernel bridge
`R3Cert.BGSCLGStepBridge.ceiling_of_glemma_le1`, to two per-hub message inequalities on the
CappedJoint cap `Bcap(μ) = min(masterUb μ, glemmaUb μ, 1)` (`W = 64/621`):
- `GlemmaStep` — PROVEN in ℚ as `CappedJointClosure.gstep_le_one_achievable` (all arities);
- `Le1Step` : `W · a^11 · ∏_c Bcap(μ_c) ≤ 1`, `a = 1 + (Σ μ_c)/(j+1)`, over achievable child
  messages `μ_c ∈ (0,1/2] ∪ {1}`.

`glemmaUb_le_masterUb` (`μ ≤ 1/2`) shows `masterUb` is subsumed, so the whole ceiling rests on `Le1Step`.
This is exactly the CappedJoint candidate's `≤1` / `phi_le_one` step (the "1" leg of `Bcap`).

## The refutation (exact rational counterexample)

`Le1Step` is **FALSE**. Take a hub whose `j = 3` children each have message `μ_c = 13/42 ≈ 0.30952`:

    Bcap(13/42) = 0.994091…  (the glemma cap binds; < 1, a genuine capped factor)
    a = 1 + (3·13/42)/4 = 69/56
    W · a^11 · Bcap(13/42)^3 = 1.006094…  > 1        (exact Fraction, verified)

and it grows to `1.147` at `j=4`, `1.249` at `j=5`. The config is **reachable**: `μ = 13/42`
means `d_c + S_c = 42/13`, i.e. a degree-3 child with two deep grandchildren (message sum `3/13`).
So `Le1Step` fails on a real branch — it is not merely unproven, it is false.

## Root cause

`Bcap` is **too loose in the mid-message band `μ ∈ (0.30, 0.45)`**. A real branch with `bY = 0.31`
has actual `Gf ≈ 0.20`, but `Bcap(0.31) = 0.994` (a ~5× over-estimate), so the capped product
`∏ Bcap` overshoots. The induction `Gf b ≤ Bcap(bY b)` uses `Gf(c) ≤ Bcap(μ_c)`, discarding the
true tightness; the multiplicative step then exceeds 1.

## Consequences

1. The bridge `ceiling ⟸ GlemmaStep ∧ Le1Step` is a **valid** reduction but to a **false**
   hypothesis, so it cannot close the ceiling.
2. The **CappedJoint candidate is refuted**: its `≤1` (`phi_le_one`) step is false, not just
   "empirically verified but unproven." The `n ≤ 15` census missed it because for actual small
   trees the child `Gf` and message are linked (tight); the abstract `Bcap`-cap step is not.
3. The ceiling `∀b bell b ≤ 0` is still **TRUE** (376k-branch numeric check). Closing it needs a
   cap `ψ` **tighter than `Bcap`** in the mid-band — the true per-message envelope
   `env(μ) = sup{Gf(b) : bY(b)=μ}` (which DOES satisfy the step, with large margin, e.g. the
   `13/42` family closes at `0.0004 ≤ 1` under a tight `ψ`). Finding an explicit, *provable* such
   `ψ` is the M_d frontier — the genuine open crux.

## Reproduce

    python3 -c "
    from fractions import Fraction as Fr
    W=Fr(64,621)
    def mU(m): return W*(Fr(3)/(2+m))**11
    def gU(m): return W*W*(Fr(5,3))**11/((1+m/3)**11)
    def B(m): return min(mU(m),gU(m),Fr(1))
    mu=Fr(13,42)
    for j in (3,4,5):
        S=j*mu; a=1+S/(j+1); v=W*a**11*B(mu)**j
        print(j, float(v), v>1)"

Kernel artifacts: `R3Cert.BGSCLGStepBridge` (`Le1Step`, `ceiling_of_glemma_le1`, `Gf_node`,
`glemmaUb_le_masterUb`) on branch `bg/scl-on-main`.

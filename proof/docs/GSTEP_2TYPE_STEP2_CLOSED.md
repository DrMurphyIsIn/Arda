# g-step uniform attack: STEP 2 closed, STEP 1 (2-type reduction) is the non-monotone wall — 2026-08-20

**Route-(B) attack on the g-step (avoiding the per-arity variable-explosion of route A). The
downstream 2-variable inequality (STEP 2) is CLOSED exactly; the upstream reduction (STEP 1) is
TRUE empirically but resists every elementary argument. `conjecture1_proved = False`.**

## The decomposition

The real g-step `GS(l) := base¹¹·∏Bcap ≤ T` (`Bcap=min(master_ub,glemma,1)`, `T=W(5/3)¹¹`,
unconditional, tight at the arm) splits into:

- **STEP 1 (reduction):** the max of `GS` over all achievable configs is attained on the
  **2-type family** `{a children at μ=½, c leaves at μ=1}`. VERIFIED (2-type max = full max =
  `T`, at the arm `(a,c)=(0,1)`; 600k random). **But UNPROVEN** — see obstruction below.
- **STEP 2 (the 2-type inequality):** `GS2(a,c) := base(a,c)¹¹·Bcap(½)^a·W^c ≤ T` for all
  `a,c ≥ 0`, `a+c ≥ 1`. **CLOSED**, exact.

## STEP 2 — closed (the reusable artifact)

`Bcap(½) = γ/(7/6)¹¹`, `base(a,c) = (9a/2+6c+4)/(3(a+c+1)) ≤ 3/2`. Three pieces, all exact:
- **`a ≥ 2` tail:** `base ≤ 3/2` ⟹ `GS2 ≤ (3/2)¹¹·Bcap(½)^a ≤ (3/2)¹¹·Bcap(½)² = 24.957 < T`
  (a single `norm_num`; `Bcap(½)² < Bcap(½)^a` for `a≥2`).
- **`a = 0` slice** (pure leaves): `GS2(0,c) = base¹¹·W^c`, decreasing in `c`, **max `= T` at
  `c=1` = the arm** (`GS2(0,1) = T` exactly). 1-variable.
- **`a = 1` slice:** `GS2(1,c)`, decreasing in `c`, max `0.872` at `c=0`. 1-variable, `< T`.

So STEP 2 is a finite core `a∈{0,1}` (two decreasing 1-var `c`-tails) + an `a≥2` crude tail —
Lean-emittable in the `master_core` style, tight only at the arm.

## STEP 1 — the non-monotone wall (why the obvious arguments fail)

Every elementary reduction to the 2-type family was tried and **fails** (all exact-tested):
- **Peeling** (adding a child decreases `GS`): FALSE — real-`Bcap` 94.6% (worst +1.02×),
  glemma worse. Small children can *inflate* `GS`.
- **"Remove small children"** (`μ≤ν*`, `Bcap=1`): FALSE — adding a small child can increase
  `GS` by up to **1.22×** (5% of cases).
- **"Push large children to ½"**: FALSE — `GS` is *decreasing* in a large child's `μ` 91% of
  the time (opposite of a bang-bang-to-½ argument).
- **Jensen / log-concavity**: FALSE — `Bcap`, `glemma` are log-*convex*.

The g-step is a genuinely **non-monotone** multivariate max; the maximizer is at the arm (2-type)
but the landscape is not reducible there by monotonicity/convexity. STEP 1 is therefore the
**DirectPolya/envelope target** — bound the non-monotone max as a polynomial optimization, or
prove monotonicity-*of-the-max* (`max_config GS` decreasing in arity; empirically holds, global
max `0.689` at q=2) by a non-peeling argument.

## Status of the g-step overall

- **Small arities:** q=2, q=3 machine-closed by the Handelman finder (see
  `GSTEP_HANDELMAN_RECIPE.md`). Per-arity does NOT scale (q=4 finder stalls — variable explosion).
- **Uniform:** reduces to STEP 1 (unproven, non-monotone) + STEP 2 (this doc, closed).

STEP 2 is the proven, reusable downstream — ready to close the g-step the moment STEP 1 lands by
any route. `conjecture1_proved = False`.

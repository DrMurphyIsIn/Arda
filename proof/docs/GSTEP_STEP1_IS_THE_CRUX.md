# STEP 1 = the master inequality: every open thread is one crux — 2026-08-21

**Attacking STEP 1 (the g-step's non-monotone core) proved it is the SAME object as the
master-inequality / R3 crux, via a below-average → homogeneous reduction. A unification, not a
closure. `conjecture1_proved = False`.**

## The reduction (attacking STEP 1)

STEP 1 (`GSTEP_2TYPE_STEP2_CLOSED.md`): reduce every achievable config to the maximizer family for
the real g-step `GS(l) = base¹¹·∏Bcap ≤ T`.

- **The non-monotonicity is the below-average lemma, exactly.** Adding a small child (`Bcap=1`,
  `μ≤ν*`) multiplies `GS` by `(base_new/base_old)¹¹`, which (exact algebra) is `>1` iff
  `μ > (S+1/3)/(q+1)` — i.e. the child is *above the config's average message*. So the maximizer
  has no below-average children ⟹ it is **homogeneous**.
- **Verified:** the g-step max lives at a homogeneous config `{k copies of μ}` — homogeneous max
  = full max = `1.0` at the arm `(k=1, μ=1)` (500k random, exact).
- Therefore **STEP 1 ⟹ the homogeneous bound** `GS([μ]*k) = base¹¹·Bcap(μ)^k ≤ T` — the
  **C-broom / master inequality**.

## Every open thread is the same crux

| thread | = |
|---|---|
| R3 / `Φ≤1` branching tail (`conjecture1_status.py`) | the master inequality |
| homogeneous face (`MASTER_INEQUALITY_FRONTIER.md`) | the master inequality |
| capped-joint g-step Case-2 (`CandidateCappedJoint*`) | the master inequality |
| Handelman-recipe Case-2 wall (`GSTEP_HANDELMAN_RECIPE.md`) | the master inequality |
| **g-step STEP 1** (this attack) | the master inequality |

They are one object: an integer-tight, **non-monotone** arithmetic core, tight at the arm.

## Already kernel-checked pieces of the crux (on `main`, CI-green)

- `HomogeneousSlice` — trivial zone `μ ≤ 229/1000` (`Bcap≤1` only).
- `NearStarBandSlice` — near-star band `k=1,2` (tail decay).
- `NearStar`/`R(s)` — the arm and near-star family.
- `MasterCore` — the master-step 1-var core `[(4p+3)/(p+1)]¹¹·W^p ≤ 3¹¹`.
- `TieClosure`, `R47LegsAT`, `CappedJointConfig`/`Achievable` — tie-half, arms+ties, config g-step
  modulo the achievable Case-2 hypothesis.
- `GSTEP_2TYPE_STEP2_CLOSED` — the 2-type downstream (STEP 2), closed exact.

## The remaining gap (unchanged, now fully unified)

The general homogeneous bound `base¹¹·Bcap(μ)^k ≤ T` for all `(k, μ)` — equivalently the master
inequality's general case. **Ruled out (exact evidence):** peeling, bang-bang→½, Jensen
(log-convex), unconditional polynomial envelope (small-`μ` inflation), per-arity finder (arity
explosion beyond q=3). The heterogeneous→homogeneous reduction is verified but its elementary
proof breaks (below-average chain has non-homogeneous fixed points).

So the residual is a genuine integer-tight/non-monotone arithmetic breakthrough — the DirectPolya
treatment of the non-monotone max, or an arithmetic argument extending the near-star integrality
proof. Maximally localized, all elementary dead-ends marked, all proven pieces identified.
`conjecture1_proved = False`.

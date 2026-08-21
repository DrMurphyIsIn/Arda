import R3Cert.GStepCore
import R3Cert.ProdBounds

/-!
  # Capped-joint g-step: config-based defs + (superseded) Case 2 (2026-08-20)

  This file supplies the shared config-level **definitions** — `glemma`, `master_ub`, `Bcap`,
  `baseOf`, `prodBcap` and their nonneg/`≤ 1` lemmas — reused by `CappedJointAchievable`.
  Those defs are correct and load-bearing; keep them.

  **⚠ HONESTY CORRECTION (2026-08-20).** The `Case2Property` defined below (config over
  `l : List ℚ` with children constrained only by `0 < μ`) was previously advertised here as
  "SATISFIABLE / the genuine analytic wall". **That claim was wrong — `Case2Property` is still
  FALSE.** Moving the abstract `(base, Pgl)` linkage into a config fixed *one* leak but left
  another: `0 < μ` admits child messages `μ ∈ (1/2, 1)`, and there the single-child g-step
  factor `baseOf([μ])^11 / (W(5/3)^11)` exceeds `1` (peak `≈ 1.076` at `μ = 13/16`). That band
  is a GAP the cavity recursion can never realize — every message is `μ = 1/(j+1+S)`, so a leaf
  (`j=0`) has `μ = 1` and every non-leaf (`j ≥ 1`) has `μ ≤ 1/2` (exact-enumeration cross-check:
  all 16,755 rooted vertices with `n ≤ 10` have max non-leaf message `17/35 < 1/2`).

  The genuine fix adds the **achievability** hypothesis `μ ≤ 1/2 ∨ μ = 1`. It lives in
  `CappedJointAchievable` as `Case2PropertyAchievable` (same `R3Cert.CappedJointConfig`
  namespace), which is the canonical open wall and which also DISCHARGES the single- and
  two-child cases unconditionally. The `Case2Property`/`gstep_le_one` below are retained,
  DEPRECATED, only so older bridges still typecheck. Entirely in `ℚ`. `conjecture1_proved = False`.
-/

namespace R3Cert.CappedJointConfig

open R3Cert.GStepCore

/-- `glemma(μ) = γ/(1+μ/3)¹¹`, `γ = W²(5/3)¹¹`. -/
def glemma (μ : ℚ) : ℚ := W ^ 2 * (5 / 3) ^ 11 / (1 + μ / 3) ^ 11

/-- `master_ub(μ) = W(3/(2+μ))¹¹`. -/
def master_ub (μ : ℚ) : ℚ := W * (3 / (2 + μ)) ^ 11

/-- `Bcap(μ) = min(master_ub, glemma, 1)` — the per-child cap (`1` is `phi_le_one`). -/
def Bcap (μ : ℚ) : ℚ := min (master_ub μ) (min (glemma μ) 1)

/-- `baseOf l = (3d+3S+1)/(3d)`, `d = |l|+1`, `S = Σ l` — the g-step base of the config `l`. -/
def baseOf (l : List ℚ) : ℚ :=
  (3 * ((l.length : ℚ) + 1) + 3 * l.sum + 1) / (3 * ((l.length : ℚ) + 1))

/-- `prodBcap l = ∏ Bcap(μ_c)` over the config. -/
def prodBcap (l : List ℚ) : ℚ := (l.map Bcap).prod

theorem Bcap_le_one (μ : ℚ) : Bcap μ ≤ 1 := by
  unfold Bcap
  exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem master_ub_nonneg {μ : ℚ} (hμ : 0 ≤ μ) : 0 ≤ master_ub μ := by
  unfold master_ub
  apply mul_nonneg
  · norm_num [W]
  · apply pow_nonneg
    apply div_nonneg
    · norm_num
    · linarith

theorem glemma_nonneg {μ : ℚ} (hμ : 0 ≤ μ) : 0 ≤ glemma μ := by
  unfold glemma
  apply div_nonneg
  · positivity
  · apply pow_nonneg; linarith

theorem Bcap_nonneg {μ : ℚ} (hμ : 0 ≤ μ) : 0 ≤ Bcap μ := by
  unfold Bcap
  exact le_min (master_ub_nonneg hμ) (le_min (glemma_nonneg hμ) (by norm_num))

theorem baseOf_nonneg (l : List ℚ) (hl : ∀ μ ∈ l, 0 ≤ μ) : 0 ≤ baseOf l := by
  unfold baseOf
  have hsum : 0 ≤ l.sum := List.sum_nonneg hl
  have hlen : (0 : ℚ) ≤ (l.length : ℚ) := Nat.cast_nonneg _
  apply div_nonneg <;> nlinarith [hsum, hlen]

theorem prodBcap_nonneg (l : List ℚ) (hl : ∀ μ ∈ l, 0 ≤ μ) : 0 ≤ prodBcap l :=
  R3Cert.ProdBounds.map_prod_nonneg l Bcap (fun μ hμ => Bcap_nonneg (hl μ hμ))

theorem prodBcap_le_one (l : List ℚ) (hl : ∀ μ ∈ l, 0 ≤ μ) : prodBcap l ≤ 1 :=
  R3Cert.ProdBounds.map_prod_le_one l Bcap (fun μ hμ => Bcap_nonneg (hl μ hμ))
    (fun μ _ => Bcap_le_one μ)

/-- **⚠ DEPRECATED / FALSE — do NOT use as the crux's open hypothesis.** This config form
    linked `base` and `∏Bcap` (fixing the abstract `(base, Pgl)` leak) but still quantifies the
    children only as `0 < μ`, which admits the unrealizable band `μ ∈ (1/2, 1)` where the
    single-child g-step factor exceeds `1` (peak `≈ 1.076` at `μ = 13/16`). So this statement is
    FALSE. **SUPERSEDED by `CappedJointAchievable.Case2PropertyAchievable`**, which adds the
    achievability hypothesis `μ ≤ 1/2 ∨ μ = 1` (the domain the cavity recursion actually
    realizes) and is genuinely the open analytic wall. Retained only so the deprecated
    `gstep_le_one` below still typechecks. -/
def Case2Property : Prop :=
  ∀ l : List ℚ, (∀ μ ∈ l, 0 < μ) → W * (5 / 3) ^ 11 < (baseOf l) ^ 11 →
    (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1

/-- **⚠ DEPRECATED — conditional on the FALSE `Case2Property` above.** Valid as a theorem, but
    its `Case2Property` hypothesis is false (admits the unrealizable band `μ ∈ (1/2,1)`), so it
    can never be discharged. **Use the achievability-corrected results in
    `CappedJointAchievable`** (`single_child_le_one`, `two_child_le_one` — proven unconditionally;
    `gstep_le_one_of_glemmaBound` — general arity) instead. Retained for continuity.
    Case 1 (`base ≤ threshold`) is discharged by `case1_bound` (with `∏Bcap ≤ 1`). -/
theorem gstep_le_one (h2 : Case2Property) (l : List ℚ) (hl : ∀ μ ∈ l, 0 < μ) :
    (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1 := by
  have hl0 : ∀ μ ∈ l, 0 ≤ μ := fun μ hμ => le_of_lt (hl μ hμ)
  have hbase : 0 ≤ baseOf l := baseOf_nonneg l hl0
  have hPbc0 : 0 ≤ prodBcap l := prodBcap_nonneg l hl0
  have hPbc1 : prodBcap l ≤ 1 := prodBcap_le_one l hl0
  by_cases h : (baseOf l) ^ 11 ≤ W * (5 / 3) ^ 11
  · exact case1_bound hbase h hPbc0 hPbc1
  · push_neg at h
    exact h2 l hl h

end R3Cert.CappedJointConfig

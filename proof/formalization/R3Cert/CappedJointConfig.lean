import R3Cert.GStepCore
import R3Cert.ProdBounds

/-!
  # Capped-joint g-step: config-based, SATISFIABLE Case 2 (corrected, 2026-08-20)

  Fixes a real flaw in `CappedJointSkeleton`: its `Case2Property` was stated abstractly over
  independent `(base, Pgl)` and is therefore **FALSE** (`base=2, Pgl=1` gives `72 ≤ 1`) — the
  abstract form dropped the config linkage (`base > threshold` *forces* suppression, so `Pbc`
  cannot be large). A false open hypothesis makes the reduction hollow.

  Here `Case2Property` is over an actual config (`l : List ℚ` of child messages), with `base`
  and `∏Bcap` **derived** from `l`, so the linkage is intrinsic. This is the genuine analytic
  wall — the real-`Bcap` g-step for `base > threshold` configs (verified `≤ 1`; the reframe),
  not the glemma over-count. `case1_bound` discharges the `base ≤ threshold` half; `ProdBounds`
  supplies `∏Bcap ≤ 1`. Entirely in `ℚ`. `conjecture1_proved = False`.
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

/-- **Case 2 — the corrected, SATISFIABLE open hypothesis.** For every achievable config `l`
    whose base exceeds the threshold, the real-`Bcap` g-step factor is `≤ 1`. `base` and
    `∏Bcap` are both derived from `l`, so the linkage is intrinsic (unlike the FALSE abstract
    form). This is the genuine remaining analytic wall (verified `≤ 1`, margin ~0.25). -/
def Case2Property : Prop :=
  ∀ l : List ℚ, (∀ μ ∈ l, 0 < μ) → W * (5 / 3) ^ 11 < (baseOf l) ^ 11 →
    (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1

/-- **g-step (config-based), conditional on the corrected Case 2.** For every achievable
    config, the g-step factor `≤ 1` — Case 1 (`base ≤ threshold`) discharged by `case1_bound`
    (with `∏Bcap ≤ 1`), Case 2 by the now-satisfiable hypothesis. -/
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

/- PHASE 4 (dVP frontier, item 4 — zero location): every ζ-zero in the disk has `Re < σ` (`σ > 1`),
   which discharges the `hother`/`hlt` hypotheses of `dlvp_zeta_region_of_canonical_decomp`.

   A point `ρ` in the divisor support of ζ is a zero (`divisor ≠ 0` ⟹ `analyticOrderAt ≠ 0` ⟹ `ζ ρ = 0`,
   using `AnalyticOnNhd.divisor_apply` + `apply_eq_zero_of_analyticOrderAt_ne_zero`), and ζ has no zeros
   with `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`), so `Re ρ < 1 < σ`.  conjecture1_proved = False.
-/
import DlvpZetaDisk
import Mathlib

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **ζ-zeros in the disk lie left of `σ`.**  For `ρ ∈ ball c₀ R` with nonzero divisor (a ζ-zero) and
    `σ > 1`, `Re ρ < σ`. -/
theorem zeta_zero_re_lt {c₀ ρ : ℂ} {R σ : ℝ} (hσ : 1 < σ)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hρ : ρ ∈ ball c₀ R)
    (hdiv : divisor riemannZeta (ball c₀ R) ρ ≠ 0) :
    ρ.re < σ := by
  have hana : AnalyticOnNhd ℂ riemannZeta (ball c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).mono ball_subset_closedBall
  -- divisor ρ ≠ 0 ⟹ analyticOrderAt ρ ≠ 0
  have hord : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro hord0
    apply hdiv
    rw [hana.divisor_apply hρ, hord0]
    rfl
  -- analyticOrderAt ρ ≠ 0 ⟹ ζ ρ = 0
  have hzero : riemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hord
  -- ζ has no zeros with Re ≥ 1
  by_contra h
  push_neg at h
  exact (riemannZeta_ne_zero_of_one_le_re (by linarith)) hzero

/-- **ζ divisor is nonnegative on the disk** (no poles there — `hm`). -/
theorem zeta_divisor_nonneg {c₀ : ℂ} {R : ℝ} (h1 : (1 : ℂ) ∉ closedBall c₀ R) (ρ : ℂ) :
    0 ≤ divisor riemannZeta (ball c₀ R) ρ := by
  have hana : AnalyticOnNhd ℂ riemannZeta (ball c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).mono ball_subset_closedBall
  exact hana.divisor_nonneg ρ

end ZeroFreeBridge

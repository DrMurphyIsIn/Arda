/- Audit probes for LiLadderSharp (auditor-forward, 2026-09-22). -/
import LiLadderSharp
open scoped Real
open LiCriterion LiLadderHeight LiFacePrelude

#print axioms li_rungs_of_bands_4000_upto_sharp

/- 1. Three-case split re-composed abstractly from |a| ≤ |b| and |a| + |b| ≤ 2π (expected SUCCESS). -/
example (a b : ℝ) (hab : |a| ≤ |b|) (hsum : |a| + |b| ≤ 2 * π) : Real.cosh a * Real.cos b ≤ 1 := by
  rcases le_or_gt |b| (3 * π / 2) with h | h
  · exact cosh_mul_cos_le_one_of_le_three_pi_div_two hab h
  · exact cosh_mul_cos_le_one_window h (by linarith [abs_nonneg a]) (by linarith)

/- 2. Deficit in [0, π/2) on the window (expected SUCCESS). -/
example (b : ℝ) (h1 : 3 * π / 2 < |b|) (h2 : |b| ≤ 2 * π) : 0 ≤ 2 * π - |b| ∧ 2 * π - |b| < π / 2 :=
  ⟨by linarith, by linarith⟩

/- 3. Lemma B'' algebra (expected SUCCESS, abstract). -/
example (g : ℝ) (hg : 1 / 2 < g) : (2 * g + 1) * (g - 1 / 2) ≤ 2 * g ^ 2 := by nlinarith

/- 4. The reach is exact: 25129 ≤ 7999π needs pi_gt_d6, and 7999π < 25130 (expected SUCCESS). -/
example : (25129 : ℝ) ≤ 2 * π * (4000 - 1 / 2) := by nlinarith [Real.pi_gt_d6]
example : 2 * π * (4000 - 1 / 2) < (25130 : ℝ) := by nlinarith [Real.pi_lt_d6]

/- 5. Consumption at rung 25128 (expected SUCCESS). -/
example (H : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    0 ≤ (taylorCoeff riemannXi 25128).re :=
  li_rungs_of_bands_4000_upto_sharp H 25128 le_rfl

/- 6. Sharp rate dominates the LiLadderHeight rate for T ≥ 2 (expected SUCCESS). -/
example (T : ℝ) (hT : 2 ≤ T) : 3 * π * T / 2 ≤ 2 * π * (T - 1 / 2) := by nlinarith [Real.pi_pos]

/- 7. EXPECTED FAIL: rung 25129 is just above the reach as stated. -/
example (H : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    0 ≤ (taylorCoeff riemannXi 25129).re :=
  li_rungs_of_bands_4000_upto_sharp H 25129 (by norm_num)

/- 8. EXPECTED FAIL: rung 25129 through the real-valued form (25130 ≤ 7999π is false). -/
example (H : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    0 ≤ (taylorCoeff riemannXi 25129).re :=
  li_rungs_of_bands_4000_sharp H 25129 (by nlinarith [Real.pi_gt_d6, Real.pi_lt_d6])

/- 9. EXPECTED FAIL: pi_gt_d4 is too weak for 25129 ≤ 7999π. -/
example : (25129 : ℝ) ≤ 2 * π * (4000 - 1 / 2) := by nlinarith [Real.pi_gt_d4, Real.pi_lt_d4]

/- 10. EXPECTED FAIL: T = 1/2. -/
example (hline : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 1 / 2 → ρ.re = 1 / 2) :
    0 ≤ (taylorCoeff riemannXi 0).re :=
  li_rung_of_zeros_on_line_below_sharp (1 / 2) (by norm_num) hline 0 (by norm_num [Real.pi_pos])

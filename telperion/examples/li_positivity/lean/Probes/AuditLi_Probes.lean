/- Audit probes for LowHeightBox / LiLadderHeight (auditor-forward, 2026-09-21). -/
import LiLadderHeight
open scoped Real
open LiCriterion LiLadderHeight LowHeightBox LiFacePrelude

/- 1. Kernel + registry shape: rung 0 hypothesis-free, statement as in the registry (expected SUCCESS). -/
example : 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi 0).re := li_rung0_kernel
#print axioms li_rung0_kernel

/- 2. Box algebra re-derived abstractly: from 2σ ≤ ‖s-1‖ and 2(1-σ) ≤ ‖s‖ to Box 2 (expected SUCCESS). -/
example (σ t : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hA : (2 * σ) ^ 2 ≤ (σ - 1) ^ 2 + t ^ 2) (hB : (2 * (1 - σ)) ^ 2 ≤ σ ^ 2 + t ^ 2) :
    (σ - 1 / 2) ^ 2 ≤ t ^ 2 / 3 - 1 / 4 := by nlinarith

/- 3. Box 1 from Box 2 abstractly (expected SUCCESS). -/
example (σ t : ℝ) (h : (σ - 1 / 2) ^ 2 ≤ t ^ 2 / 3 - 1 / 4) : 3 / 4 ≤ t ^ 2 := by
  nlinarith [sq_nonneg (σ - 1 / 2)]

/- 4. Box 1 applies to every upstream NontrivialZero (the hypothesis shape matches; expected SUCCESS). -/
example (ρ : NontrivialZero) : Real.sqrt 3 / 2 ≤ |ρ.val.im| :=
  zeta_zero_im_ge ρ.val ρ.property.1 ρ.property.2

/- 5. The factor-3 split: cos ≤ 0 on [π/2, 3π/2], so no condition on a there (expected SUCCESS). -/
example (a b : ℝ) (h1 : π / 2 ≤ |b|) (h2 : |b| ≤ 3 * π / 2) : Real.cosh a * Real.cos b ≤ 0 := by
  have hc : Real.cos b ≤ 0 := by
    rw [← Real.cos_abs b]; exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
  nlinarith [Real.cosh_pos a]

/- 6. The window cannot be widened to 2π: at b = 2π, a = 1 the product exceeds 1 (expected SUCCESS). -/
example : 1 < Real.cosh 1 * Real.cos (2 * π) := by
  rw [Real.cos_two_pi, mul_one]
  have := Real.one_lt_cosh.mpr (show (1 : ℝ) ≠ 0 by norm_num)
  exact this

/- 7. Threshold arithmetic of Theorem D: n + 1 ≤ 3πT/2 gives 2(n+1)/(3π) ≤ T (expected SUCCESS). -/
example (T : ℝ) (n : ℕ) (hn : (n + 1 : ℝ) ≤ 3 * π * T / 2) : 2 * ((n : ℝ) + 1) / (3 * π) ≤ T := by
  rw [div_le_iff₀ (by positivity)]; linarith

/- 8. Rung 0 sign re-derived: Re(1/(ρ(1-ρ))) numerator is β(1-β) + γ² (expected SUCCESS). -/
example (β γ : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    0 ≤ (β * (1 - β) + γ ^ 2) := by nlinarith [sq_nonneg γ, mul_pos h0 (sub_pos.mpr h1)]

/- 9. Consumption of Theorem D with the conclusion shape of the h4000 capstone (expected SUCCESS). -/
example (H : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    0 ≤ (taylorCoeff riemannXi 18848).re :=
  li_rungs_of_bands_4000_upto H 18848 le_rfl

/- 10. Lemma A consumed at the corner |a| = |b| = π/2 (expected SUCCESS). -/
example : Real.cosh (π / 2) * Real.cos (π / 2) ≤ 1 :=
  cosh_mul_cos_le_one (le_refl _) (by rw [abs_of_pos (by positivity)])

/- 11. EXPECTED FAIL: the rung-0 termwise argument does not leak to rung 1. -/
example : 0 ≤ (taylorCoeff riemannXi 1).re :=
  re_taylorCoeff_nonneg_of_termwise 1 re_liPairedSummand_zero_nonneg

/- 12. EXPECTED FAIL: Theorem D needs T ≥ 1; T = 1/2 is rejected. -/
example (hline : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 1 / 2 → ρ.re = 1 / 2) :
    0 ≤ (taylorCoeff riemannXi 0).re :=
  li_rung_of_zeros_on_line_below (1 / 2) (by norm_num) hline 0 (by norm_num [Real.pi_pos])

/- 13. EXPECTED FAIL: rung 18849 is outside the height-4000 reach as stated. -/
example (H : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    0 ≤ (taylorCoeff riemannXi 18849).re :=
  li_rungs_of_bands_4000_upto H 18849 (by norm_num)

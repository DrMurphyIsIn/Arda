/- telperion 0.1.6 | family BoxResidueSum | input-hash 2844ab6b8a231ac2
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace BoxResidueSum

open Complex intervalIntegral MeasureTheory

/-- Box residue-sum on `[0, 1] × [0, 1]`: the four-segment boundary
    integral of a Herglotz sum equals `2πi·Σ m`, GIVEN the per-pole winding
    primitive `Bd((z-ρ)⁻¹) = 2πi` (a Mathlib gap — non-circular winding).
    This atom discharges the Finset-linearity plumbing over the four sides. -/
theorem box_residue_sum_unit {s : Finset ℂ} (m : ℂ → ℤ)
    (hb : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + (0 : ℝ) * I) - ρ)⁻¹) volume (0) (1))
    (ht : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + (1 : ℝ) * I) - ρ)⁻¹) volume (0) (1))
    (hr : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((1 : ℝ) + ↑y * I) - ρ)⁻¹) volume (0) (1))
    (hl : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((0 : ℝ) + ↑y * I) - ρ)⁻¹) volume (0) (1))
    (hwind : ∀ ρ ∈ s,
      (∫ x in (0: ℝ)..(1), ((↑x + (0 : ℝ) * I) - ρ)⁻¹)
        - (∫ x in (0: ℝ)..(1), ((↑x + (1 : ℝ) * I) - ρ)⁻¹)
        + I • (∫ y in (0: ℝ)..(1), (((1 : ℝ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (0: ℝ)..(1), (((0 : ℝ) + ↑y * I) - ρ)⁻¹) = 2 * π * I) :
    (∫ x in (0: ℝ)..(1), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (0 : ℝ) * I) - ρ)⁻¹)
        - (∫ x in (0: ℝ)..(1), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (1 : ℝ) * I) - ρ)⁻¹)
        + I • (∫ y in (0: ℝ)..(1), ∑ ρ ∈ s, (m ρ : ℂ) * (((1 : ℝ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (0: ℝ)..(1), ∑ ρ ∈ s, (m ρ : ℂ) * (((0 : ℝ) + ↑y * I) - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  rw [intervalIntegral.integral_finsetSum (fun ρ hρ => (hb ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (ht ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hr ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hl ρ hρ).const_mul (m ρ : ℂ))]
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hw := hwind ρ hρ; simp only [smul_eq_mul] at hw
  linear_combination (m ρ : ℂ) * hw
/-- Box residue-sum on `[0, 2] × [0, 1]`: the four-segment boundary
    integral of a Herglotz sum equals `2πi·Σ m`, GIVEN the per-pole winding
    primitive `Bd((z-ρ)⁻¹) = 2πi` (a Mathlib gap — non-circular winding).
    This atom discharges the Finset-linearity plumbing over the four sides. -/
theorem box_residue_sum_wide {s : Finset ℂ} (m : ℂ → ℤ)
    (hb : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + (0 : ℝ) * I) - ρ)⁻¹) volume (0) (2))
    (ht : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + (1 : ℝ) * I) - ρ)⁻¹) volume (0) (2))
    (hr : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((2 : ℝ) + ↑y * I) - ρ)⁻¹) volume (0) (1))
    (hl : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((0 : ℝ) + ↑y * I) - ρ)⁻¹) volume (0) (1))
    (hwind : ∀ ρ ∈ s,
      (∫ x in (0: ℝ)..(2), ((↑x + (0 : ℝ) * I) - ρ)⁻¹)
        - (∫ x in (0: ℝ)..(2), ((↑x + (1 : ℝ) * I) - ρ)⁻¹)
        + I • (∫ y in (0: ℝ)..(1), (((2 : ℝ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (0: ℝ)..(1), (((0 : ℝ) + ↑y * I) - ρ)⁻¹) = 2 * π * I) :
    (∫ x in (0: ℝ)..(2), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (0 : ℝ) * I) - ρ)⁻¹)
        - (∫ x in (0: ℝ)..(2), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (1 : ℝ) * I) - ρ)⁻¹)
        + I • (∫ y in (0: ℝ)..(1), ∑ ρ ∈ s, (m ρ : ℂ) * (((2 : ℝ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (0: ℝ)..(1), ∑ ρ ∈ s, (m ρ : ℂ) * (((0 : ℝ) + ↑y * I) - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  rw [intervalIntegral.integral_finsetSum (fun ρ hρ => (hb ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (ht ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hr ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hl ρ hρ).const_mul (m ρ : ℂ))]
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hw := hwind ρ hρ; simp only [smul_eq_mul] at hw
  linear_combination (m ρ : ℂ) * hw

end BoxResidueSum

/- telperion 0.1.6 | family CauchyDeriv | input-hash 3302c1c51c8d0195
   4 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace CauchyDeriv

/-- Cauchy's derivative estimate on the disk of radius `(1 / 2)` about `z0`:
    `f` holomorphic on `ball z0 (1 / 2)` (continuous up to the boundary) with
    `‖f z‖ ≤ 12` on `sphere z0 (1 / 2)` implies `‖deriv f z0‖ ≤ 12 / (1 / 2)`.
    A concrete-radius copy of `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. -/
theorem cd_half (f : ℂ → ℂ) (z0 : ℂ)
    (hd : DiffContOnCl ℂ f (Metric.ball z0 ((1 / 2) : ℝ)))
    (hC : ∀ z ∈ Metric.sphere z0 ((1 / 2) : ℝ), ‖f z‖ ≤ (12 : ℝ)) :
    ‖deriv f z0‖ ≤ (12 : ℝ) / ((1 / 2) : ℝ) :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < (1 / 2)) hd hC
/-- Borel-Caratheodory constant identity at inner radius `ρ' = (2 - 1)/2`:
    the Cauchy constant `(2(r+ρ')/(R−(r+ρ')))·(1/ρ')` collapses to
    `4(R+r)/(R−r)²` (a `field_simp; ring` fact for `R > r ≥ 0`). -/
theorem cd_two_one_const :
    (2 * ((1 : ℝ) + (2 - 1) / 2) / (2 - ((1 : ℝ) + (2 - 1) / 2)))
        * (1 / ((2 - 1) / 2))
      = 4 * ((2 : ℝ) + 1) / (2 - 1) ^ 2 := by
  have hRr : ((2 : ℝ) - 1) ≠ 0 := by norm_num
  field_simp
  ring
/-- Cauchy's derivative estimate on the disk of radius `1` about `z0`:
    `f` holomorphic on `ball z0 1` (continuous up to the boundary) with
    `‖f z‖ ≤ 3` on `sphere z0 1` implies `‖deriv f z0‖ ≤ 3 / 1`.
    A concrete-radius copy of `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. -/
theorem cd_both (f : ℂ → ℂ) (z0 : ℂ)
    (hd : DiffContOnCl ℂ f (Metric.ball z0 (1 : ℝ)))
    (hC : ∀ z ∈ Metric.sphere z0 (1 : ℝ), ‖f z‖ ≤ (3 : ℝ)) :
    ‖deriv f z0‖ ≤ (3 : ℝ) / (1 : ℝ) :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1) hd hC
/-- Borel-Caratheodory constant identity at inner radius `ρ' = (1 - (1 / 2))/2`:
    the Cauchy constant `(2(r+ρ')/(R−(r+ρ')))·(1/ρ')` collapses to
    `4(R+r)/(R−r)²` (a `field_simp; ring` fact for `R > r ≥ 0`). -/
theorem cd_both_const :
    (2 * (((1 / 2) : ℝ) + (1 - (1 / 2)) / 2) / (1 - (((1 / 2) : ℝ) + (1 - (1 / 2)) / 2)))
        * (1 / ((1 - (1 / 2)) / 2))
      = 4 * ((1 : ℝ) + (1 / 2)) / (1 - (1 / 2)) ^ 2 := by
  have hRr : ((1 : ℝ) - (1 / 2)) ≠ 0 := by norm_num
  field_simp
  ring

end CauchyDeriv

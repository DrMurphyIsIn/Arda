/- Landing a genuine zeta-numerics lemma in Mathlib v4.32.0.
   Step 1 (this file): zeta(2) bounds from the exact value pi^2/6 + the confirmed
   pi bounds -- proves the zeta-numerics pipeline compiles end to end. -/
import Mathlib
open scoped Real

theorem riemannZeta_two_re_bounds :
    (3 : ℝ) / 2 < (riemannZeta 2).re ∧ (riemannZeta 2).re < 8 / 3 := by
  have h : riemannZeta 2 = ((π ^ 2 / 6 : ℝ) : ℂ) := by
    rw [riemannZeta_two]; push_cast; ring
  rw [h, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_three, Real.pi_pos]
  · nlinarith [Real.pi_lt_four, Real.pi_pos]

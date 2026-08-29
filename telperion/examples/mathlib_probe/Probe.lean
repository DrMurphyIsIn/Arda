/- zeta(4) bounds via riemannZeta_four = pi^4/90 + the confirmed pi bounds. -/
import Mathlib
open scoped Real

theorem riemannZeta_four_re_bounds :
    (9 : ℝ) / 10 < (riemannZeta 4).re ∧ (riemannZeta 4).re < 128 / 45 := by
  have h : riemannZeta 4 = ((π ^ 4 / 90 : ℝ) : ℂ) := by
    rw [riemannZeta_four]; push_cast; ring
  rw [h, Complex.ofReal_re]
  have h9 : (9 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have h16 : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hp : (0 : ℝ) < π ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [h9, hp]
  · nlinarith [h16, hp]

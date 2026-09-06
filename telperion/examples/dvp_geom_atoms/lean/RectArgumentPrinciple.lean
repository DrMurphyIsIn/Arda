/- telperion 0.1.6 | family RectArgumentPrinciple | input-hash e6f7dbb8b60f6285
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace RectArgumentPrinciple

open Complex Metric Real intervalIntegral

/-- Argument principle (analytic/Cauchy part) on the rectangle
    `[0, 1] × [0, 1]`: the four-segment boundary integral of a
    holomorphic `f` vanishes.  Box counterpart of the analytic `E`-term. -/
theorem rect_arg_principle_unit (f : ℂ → ℂ)
    (H : DifferentiableOn ℂ f (Set.Icc ((0) : ℝ) (1) ×ℂ Set.Icc ((0) : ℝ) (1))) :
    (∫ x : ℝ in ((0) : ℝ)..(1), f (↑x + (((0) : ℝ) : ℂ) * I))
        - (∫ x : ℝ in ((0) : ℝ)..(1), f (↑x + (((1) : ℝ) : ℂ) * I))
        + I • (∫ y : ℝ in ((0) : ℝ)..(1), f ((((1) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y : ℝ in ((0) : ℝ)..(1), f ((((0) : ℝ) : ℂ) + ↑y * I)) = 0 := by
  have key := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((((0) : ℝ) : ℂ) + (((0) : ℝ) : ℂ) * I) ((((1) : ℝ) : ℂ) + (((1) : ℝ) : ℂ) * I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at key
  norm_num at key ⊢
  exact key H
/-- Argument principle (analytic/Cauchy part) on the rectangle
    `[0, 2] × [0, 1]`: the four-segment boundary integral of a
    holomorphic `f` vanishes.  Box counterpart of the analytic `E`-term. -/
theorem rect_arg_principle_wide (f : ℂ → ℂ)
    (H : DifferentiableOn ℂ f (Set.Icc ((0) : ℝ) (2) ×ℂ Set.Icc ((0) : ℝ) (1))) :
    (∫ x : ℝ in ((0) : ℝ)..(2), f (↑x + (((0) : ℝ) : ℂ) * I))
        - (∫ x : ℝ in ((0) : ℝ)..(2), f (↑x + (((1) : ℝ) : ℂ) * I))
        + I • (∫ y : ℝ in ((0) : ℝ)..(1), f ((((2) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y : ℝ in ((0) : ℝ)..(1), f ((((0) : ℝ) : ℂ) + ↑y * I)) = 0 := by
  have key := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((((0) : ℝ) : ℂ) + (((0) : ℝ) : ℂ) * I) ((((2) : ℝ) : ℂ) + (((1) : ℝ) : ℂ) * I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at key
  norm_num at key ⊢
  exact key H

end RectArgumentPrinciple

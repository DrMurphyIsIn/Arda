/- sqrt_bracket wired into BG: the sqrt 2 bracket of ExactCruxes.e2_two_rhoB_gt.
   `bg_rhob_e2_sqrt2` gives `sqrt 2 <= 17/12` (BG's coarse bound) -- combined with
   `1 + 17/12 < 2 * rhoB` (from rhoB > 29/24 via the 11th-root clearing) it yields
   `1 + sqrt 2 <= 1 + 17/12 < 2 * rhoB`, i.e. e2_two_rhoB_gt with `<=` in place of the
   hand-written strict `<`.  Generated + kernel-checkable (Real.sqrt_sq / sqrt_le_sqrt). -/
import Mathlib

namespace BGRhoBSqrt

theorem bg_rhob_e2_sqrt2 :
    (1 : ℝ) / 1 ≤ Real.sqrt ((2 : ℝ) / 1)
      ∧ Real.sqrt ((2 : ℝ) / 1) ≤ (17 : ℝ) / 12 := by
  constructor
  · calc ((1 : ℝ) / 1)
        = Real.sqrt (((1 : ℝ) / 1) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt ((2 : ℝ) / 1) := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt ((2 : ℝ) / 1)
        ≤ Real.sqrt (((17 : ℝ) / 12) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (17 : ℝ) / 12 := Real.sqrt_sq (by norm_num)

theorem bg_rhob_e2_sqrt2_tight :
    (1414213562373 : ℝ) / 1000000000000 ≤ Real.sqrt ((2 : ℝ) / 1)
      ∧ Real.sqrt ((2 : ℝ) / 1) ≤ (14142135623731 : ℝ) / 10000000000000 := by
  constructor
  · calc ((1414213562373 : ℝ) / 1000000000000)
        = Real.sqrt (((1414213562373 : ℝ) / 1000000000000) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt ((2 : ℝ) / 1) := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt ((2 : ℝ) / 1)
        ≤ Real.sqrt (((14142135623731 : ℝ) / 10000000000000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (14142135623731 : ℝ) / 10000000000000 := Real.sqrt_sq (by norm_num)

end BGRhoBSqrt

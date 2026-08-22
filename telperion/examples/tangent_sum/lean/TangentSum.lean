/- telperion 0.1.6 | family TangentSum | input-hash 58642c3d408f28c8
   4 theorems, 9 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace TangentSum

theorem jensen_sq (x1 x2 x3 : ℝ) (hsum : x1 + x2 + x3 = 3) :
    (3 : ℝ) ≤ (x1 ^ 2) + (x2 ^ 2) + (x3 ^ 2) := by
  have h1 : (0:ℝ) ≤ (x1 ^ 2) - ((-1) + 2 * x1) := by
    have e1 : (x1 ^ 2) - ((-1) + 2 * x1) = 1 * (x1 - 1)^2 := by ring
    rw [e1]; positivity
  have h2 : (0:ℝ) ≤ (x2 ^ 2) - ((-1) + 2 * x2) := by
    have e2 : (x2 ^ 2) - ((-1) + 2 * x2) = 1 * (x2 - 1)^2 := by ring
    rw [e2]; positivity
  have h3 : (0:ℝ) ≤ (x3 ^ 2) - ((-1) + 2 * x3) := by
    have e3 : (x3 ^ 2) - ((-1) + 2 * x3) = 1 * (x3 - 1)^2 := by ring
    rw [e3]; positivity
  linarith [h1, h2, h3, hsum]
theorem quad_shift (x1 x2 : ℝ) (hsum : x1 + x2 = 4) :
    (14 : ℝ) ≤ (5 + 2 * x1 ^ 2 - 3 * x1) + (5 + 2 * x2 ^ 2 - 3 * x2) := by
  have h1 : (0:ℝ) ≤ (5 + 2 * x1 ^ 2 - 3 * x1) - ((-3) + 5 * x1) := by
    have e1 : (5 + 2 * x1 ^ 2 - 3 * x1) - ((-3) + 5 * x1) = 2 * (x1 - 2)^2 := by ring
    rw [e1]; positivity
  have h2 : (0:ℝ) ≤ (5 + 2 * x2 ^ 2 - 3 * x2) - ((-3) + 5 * x2) := by
    have e2 : (5 + 2 * x2 ^ 2 - 3 * x2) - ((-3) + 5 * x2) = 2 * (x2 - 2)^2 := by ring
    rw [e2]; positivity
  linarith [h1, h2, hsum]
theorem quartic_two (x1 x2 : ℝ) (hsum : x1 + x2 = 2) :
    (2 : ℝ) ≤ (x1 ^ 4) + (x2 ^ 4) := by
  have h1 : (0:ℝ) ≤ (x1 ^ 4) - ((-3) + 4 * x1) := by
    have e1 : (x1 ^ 4) - ((-3) + 4 * x1) = 1 * (x1 ^ 2 - 1)^2 + 2 * (x1 - 1)^2 := by ring
    rw [e1]; positivity
  have h2 : (0:ℝ) ≤ (x2 ^ 4) - ((-3) + 4 * x2) := by
    have e2 : (x2 ^ 4) - ((-3) + 4 * x2) = 1 * (x2 ^ 2 - 1)^2 + 2 * (x2 - 1)^2 := by ring
    rw [e2]; positivity
  linarith [h1, h2, hsum]
theorem sextic_two (x1 x2 : ℝ) (hsum : x1 + x2 = 0) :
    (0 : ℝ) ≤ (2 * x1 ^ 2 + 3 * x1 ^ 4 + x1 ^ 6) + (2 * x2 ^ 2 + 3 * x2 ^ 4 + x2 ^ 6) := by
  have h1 : (0:ℝ) ≤ (2 * x1 ^ 2 + 3 * x1 ^ 4 + x1 ^ 6) - (0 + 0 * x1) := by
    have e1 : (2 * x1 ^ 2 + 3 * x1 ^ 4 + x1 ^ 6) - (0 + 0 * x1) = 1 * (x1 ^ 3)^2 + 3 * (x1 ^ 2)^2 + 2 * (x1)^2 := by ring
    rw [e1]; positivity
  have h2 : (0:ℝ) ≤ (2 * x2 ^ 2 + 3 * x2 ^ 4 + x2 ^ 6) - (0 + 0 * x2) := by
    have e2 : (2 * x2 ^ 2 + 3 * x2 ^ 4 + x2 ^ 6) - (0 + 0 * x2) = 1 * (x2 ^ 3)^2 + 3 * (x2 ^ 2)^2 + 2 * (x2)^2 := by ring
    rw [e2]; positivity
  linarith [h1, h2, hsum]

end TangentSum

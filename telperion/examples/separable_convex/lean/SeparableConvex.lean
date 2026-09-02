/- telperion 0.1.6 | family SeparableConvex | input-hash 09e71b31e7514f5b
   2 theorems, 5 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SeparableConvex

-- Separable-convex MINIMUM at the homogeneous point S/n (Jensen); box bounds scope the slice.
theorem sepconv_jensen_sq3 (x1 x2 x3 : ℝ) (hlo1 : (0 : ℝ) ≤ x1) (hhi1 : x1 ≤ 3) (hlo2 : (0 : ℝ) ≤ x2) (hhi2 : x2 ≤ 3) (hlo3 : (0 : ℝ) ≤ x3) (hhi3 : x3 ≤ 3) (hsum : x1 + x2 + x3 = 3) :
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
-- Separable-convex MINIMUM at the homogeneous point S/n (Jensen); box bounds scope the slice.
theorem sepconv_quartic_box (x1 x2 : ℝ) (hlo1 : ((1 / 2) : ℝ) ≤ x1) (hhi1 : x1 ≤ (3 / 2)) (hlo2 : ((1 / 2) : ℝ) ≤ x2) (hhi2 : x2 ≤ (3 / 2)) (hsum : x1 + x2 = 2) :
    (2 : ℝ) ≤ (x1 ^ 4) + (x2 ^ 4) := by
  have h1 : (0:ℝ) ≤ (x1 ^ 4) - ((-3) + 4 * x1) := by
    have e1 : (x1 ^ 4) - ((-3) + 4 * x1) = 1 * (x1 ^ 2 - 1)^2 + 2 * (x1 - 1)^2 := by ring
    rw [e1]; positivity
  have h2 : (0:ℝ) ≤ (x2 ^ 4) - ((-3) + 4 * x2) := by
    have e2 : (x2 ^ 4) - ((-3) + 4 * x2) = 1 * (x2 ^ 2 - 1)^2 + 2 * (x2 - 1)^2 := by ring
    rw [e2]; positivity
  linarith [h1, h2, hsum]

end SeparableConvex

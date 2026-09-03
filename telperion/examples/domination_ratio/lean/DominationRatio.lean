/- telperion 0.1.6 | family DominationRatio | input-hash 6734701b649db1c4
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace DominationRatio

-- Domination ratio r = P/Q ≥ 1 on a 2-parameter box (cross-multiplied to Q ≤ P; D = P - Q multi-affine, corner-dispatched).
theorem dr_two_param (x y : ℝ)
    (hl0 : 0 ≤ x) (hu0 : x ≤ 1)
    (hl1 : 0 ≤ y) (hu1 : y ≤ 1)
    : x*y + x + y + 1 ≤ 2*x*y + 2*x + 2*y + 2 := by
  have hg0 : (0:ℝ) ≤ x - 0 := by linarith
  have hh0 : (0:ℝ) ≤ 1 - x := by linarith
  have hg1 : (0:ℝ) ≤ y - 0 := by linarith
  have hh1 : (0:ℝ) ≤ 1 - y := by linarith
  have hw0 : (0:ℝ) ≤ (1 - x)*(1 - y) := (mul_nonneg hh0 hh1)
  have hq0 : (0:ℝ) ≤ ((1 - x)*(1 - y)) * (1) := mul_nonneg hw0 (by norm_num)
  have hw1 : (0:ℝ) ≤ (1 - x)*(y - 0) := (mul_nonneg hh0 hg1)
  have hq1 : (0:ℝ) ≤ ((1 - x)*(y - 0)) * (2) := mul_nonneg hw1 (by norm_num)
  have hw2 : (0:ℝ) ≤ (x - 0)*(1 - y) := (mul_nonneg hg0 hh1)
  have hq2 : (0:ℝ) ≤ ((x - 0)*(1 - y)) * (2) := mul_nonneg hw2 (by norm_num)
  have hw3 : (0:ℝ) ≤ (x - 0)*(y - 0) := (mul_nonneg hg0 hg1)
  have hq3 : (0:ℝ) ≤ ((x - 0)*(y - 0)) * (4) := mul_nonneg hw3 (by norm_num)
  have hid : (x*y + x + y + 1) * ((1 - 0)*(1 - 0)) = ((1 - x)*(1 - y)) * (1) + ((1 - x)*(y - 0)) * (2) + ((x - 0)*(1 - y)) * (2) + ((x - 0)*(y - 0)) * (4) := by ring
  have hd : (0:ℝ) < (1 - 0)*(1 - 0) := (mul_pos (by norm_num : (0:ℝ) < 1 - 0) (by norm_num : (0:ℝ) < 1 - 0))
  nlinarith [hid, hd, hq0, hq1, hq2, hq3]
-- Domination ratio r = P/Q ≥ 1 on a 2-parameter box (cross-multiplied to Q ≤ P; D = P - Q multi-affine, corner-dispatched).
theorem dr_mixed_slope (x y : ℝ)
    (hl0 : 0 ≤ x) (hu0 : x ≤ 1)
    (hl1 : 0 ≤ y) (hu1 : y ≤ 1)
    : x + 2*y + 2 ≤ x*y + 5 := by
  have hg0 : (0:ℝ) ≤ x - 0 := by linarith
  have hh0 : (0:ℝ) ≤ 1 - x := by linarith
  have hg1 : (0:ℝ) ≤ y - 0 := by linarith
  have hh1 : (0:ℝ) ≤ 1 - y := by linarith
  have hw0 : (0:ℝ) ≤ (1 - x)*(1 - y) := (mul_nonneg hh0 hh1)
  have hq0 : (0:ℝ) ≤ ((1 - x)*(1 - y)) * (3) := mul_nonneg hw0 (by norm_num)
  have hw1 : (0:ℝ) ≤ (1 - x)*(y - 0) := (mul_nonneg hh0 hg1)
  have hq1 : (0:ℝ) ≤ ((1 - x)*(y - 0)) * (1) := mul_nonneg hw1 (by norm_num)
  have hw2 : (0:ℝ) ≤ (x - 0)*(1 - y) := (mul_nonneg hg0 hh1)
  have hq2 : (0:ℝ) ≤ ((x - 0)*(1 - y)) * (2) := mul_nonneg hw2 (by norm_num)
  have hw3 : (0:ℝ) ≤ (x - 0)*(y - 0) := (mul_nonneg hg0 hg1)
  have hq3 : (0:ℝ) ≤ ((x - 0)*(y - 0)) * (1) := mul_nonneg hw3 (by norm_num)
  have hid : (x*y - x - 2*y + 3) * ((1 - 0)*(1 - 0)) = ((1 - x)*(1 - y)) * (3) + ((1 - x)*(y - 0)) * (1) + ((x - 0)*(1 - y)) * (2) + ((x - 0)*(y - 0)) * (1) := by ring
  have hd : (0:ℝ) < (1 - 0)*(1 - 0) := (mul_pos (by norm_num : (0:ℝ) < 1 - 0) (by norm_num : (0:ℝ) < 1 - 0))
  nlinarith [hid, hd, hq0, hq1, hq2, hq3]

end DominationRatio

/- telperion 0.1.6 | family Achievability | input-hash 53bf59af4efa3469
   3 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace Achievability

-- Achievability closure: Q(x) ≥ 0 is FALSE on the relaxed domain [0, 1]
-- (witness Q((201 / 400)) = (-(1 / 200)) < 0), but TRUE on the ACHIEVABLE subset [0, (1 / 2)].
-- Restricted inequality, closed by nlinarith from the corner product (x-l)(b-x) ≥ 0.
theorem ach_cavity_half (x : ℝ) (hx_lo : 0 ≤ x) (hx_hi : x ≤ (1 / 2)) :
    (0:ℝ) ≤ (-2) * x + 1 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 0)
                        (by linarith : (0:ℝ) ≤ (1 / 2) - x),
             hx_lo, hx_hi, sq_nonneg x, sq_nonneg (x - (1 / 2))]
-- Achievability derivation: a cavity message μ = 1/(j+1+S) with j ≥ 1, S ≥ 0 satisfies μ ≤ (1 / 2).
theorem ach_cavity_half_achievable (j S : ℝ) (hj : 1 ≤ j) (hS : 0 ≤ S) :
    1 / (j + 1 + S) ≤ (1 / 2) := by
  have hden : (2:ℝ) ≤ j + 1 + S := by linarith
  have h2 : (0:ℝ) < 2 := by norm_num
  -- 1/(j+1+S) ≤ 1/2 = (1 / 2) since 2 ≤ j+1+S; monotone reciprocal.
  have hrec : 1 / (j + 1 + S) ≤ 1 / 2 :=
    one_div_le_one_div_of_le h2 hden
  simpa using hrec
-- Achievability closure: Q(x) ≥ 0 is FALSE on the relaxed domain [0, 1]
-- (witness Q((201 / 400)) = (-(199 / 80000)) < 0), but TRUE on the ACHIEVABLE subset [0, (1 / 2)].
-- Restricted inequality, closed by nlinarith from the corner product (x-l)(b-x) ≥ 0.
theorem ach_quadratic_half (x : ℝ) (hx_lo : 0 ≤ x) (hx_hi : x ≤ (1 / 2)) :
    (0:ℝ) ≤ 2 * x^2 + (-3) * x + 1 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 0)
                        (by linarith : (0:ℝ) ≤ (1 / 2) - x),
             hx_lo, hx_hi, sq_nonneg x, sq_nonneg (x - (1 / 2))]

end Achievability

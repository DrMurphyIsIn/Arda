/- telperion 0.1.6 | family TangentSum | input-hash f217dbbfae17a35e
   2 theorems, 5 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace TangentSum

theorem jensen_sq (x1 x2 x3 : ℝ) (hsum : x1 + x2 + x3 = 3) :
    (3 : ℝ) ≤ (x1 ^ 2) + (x2 ^ 2) + (x3 ^ 2) := by
  nlinarith [sq_nonneg (x1 - 1), sq_nonneg (x2 - 1), sq_nonneg (x3 - 1), hsum]
theorem quad_shift (x1 x2 : ℝ) (hsum : x1 + x2 = 4) :
    (14 : ℝ) ≤ (5 + 2 * x1 ^ 2 - 3 * x1) + (5 + 2 * x2 ^ 2 - 3 * x2) := by
  nlinarith [sq_nonneg (x1 - 2), sq_nonneg (x2 - 2), hsum]

end TangentSum

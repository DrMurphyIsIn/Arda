/- telperion 0.1.6 | family CauchySchwarz | input-hash c301cae96555bb51
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace CauchySchwarz

theorem qm_am_three (x1 x2 x3 : ℝ) :
    (1 * x1 + 1 * x2 + 1 * x3)^2 ≤ 3 * (1 * x1^2 + 1 * x2^2 + 1 * x3^2) := by
  have key : 3 * (1 * x1^2 + 1 * x2^2 + 1 * x3^2) - (1 * x1 + 1 * x2 + 1 * x3)^2 = 1 * (x1 - x2)^2 + 1 * (x1 - x3)^2 + 1 * (x2 - x3)^2 := by ring
  have hpos : (0:ℝ) ≤ 1 * (x1 - x2)^2 + 1 * (x1 - x3)^2 + 1 * (x2 - x3)^2 := by positivity
  linarith [key, hpos]
theorem weighted_three (x1 x2 x3 : ℝ) :
    (1 * x1 + 2 * x2 + 3 * x3)^2 ≤ 6 * (1 * x1^2 + 2 * x2^2 + 3 * x3^2) := by
  have key : 6 * (1 * x1^2 + 2 * x2^2 + 3 * x3^2) - (1 * x1 + 2 * x2 + 3 * x3)^2 = 2 * (x1 - x2)^2 + 3 * (x1 - x3)^2 + 6 * (x2 - x3)^2 := by ring
  have hpos : (0:ℝ) ≤ 2 * (x1 - x2)^2 + 3 * (x1 - x3)^2 + 6 * (x2 - x3)^2 := by positivity
  linarith [key, hpos]

end CauchySchwarz

/- telperion 0.1.6 | family PSDForm | input-hash 12d05e3e18e1a6bc
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace PSDForm

theorem psd_two (x1 x2 : ℝ) :
    (0:ℝ) ≤ 2 * x1 ^ 2 + 2 * x1 * x2 + 2 * x2 ^ 2 := by
  have hid : 2 * x1 ^ 2 + 2 * x1 * x2 + 2 * x2 ^ 2 = 2 * ((2 * x1 + x2) / (2))^2 + (3 / 2) * (x2)^2 := by ring
  rw [hid]; positivity
theorem psd_three (x1 x2 x3 : ℝ) :
    (0:ℝ) ≤ 4 * x1 ^ 2 + 4 * x1 * x2 + 3 * x2 ^ 2 + 2 * x2 * x3 + 5 * x3 ^ 2 := by
  have hid : 4 * x1 ^ 2 + 4 * x1 * x2 + 3 * x2 ^ 2 + 2 * x2 * x3 + 5 * x3 ^ 2 = 4 * ((2 * x1 + x2) / (2))^2 + 2 * ((2 * x2 + x3) / (2))^2 + (9 / 2) * (x3)^2 := by ring
  rw [hid]; positivity

end PSDForm

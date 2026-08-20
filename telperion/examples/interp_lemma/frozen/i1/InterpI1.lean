/- telperion 0.1.6 | family InterpI1 | input-hash cf4feab95013f282
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace Interp

theorem interp_I1_cavity (y : ℝ) (hy : 0 ≤ y) :
    3 / ((1 + (9 / 23) * (1 + y) / (6 + 3 * y)) * (6 + 3 * y)) = 23 / (49 + 26 * y) := by
  have hd1 : (49 + 26 * y : ℝ) ≠ 0 := by positivity
  field_simp
  try ring

theorem interp_I1_subopen (y : ℝ) (hy : 0 ≤ y) :
    1 + (9 / 23) * (1 + y) / (6 + 3 * y) = 26 / (23 + 9 / ((1 + (9 / 23) * (1 + y) / (6 + 3 * y)) * (6 + 3 * y))) := by
  have hd1 : (2 + y : ℝ) ≠ 0 := by positivity
  field_simp
  try ring

end Interp

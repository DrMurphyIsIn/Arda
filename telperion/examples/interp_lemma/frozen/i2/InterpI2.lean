/- telperion 0.1.5 | family InterpI2 | input-hash cf7367aaa7ff90d9
   1 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace Interp

theorem interp_I2_sign_poly (c z T : ℝ) (hc : 0 ≤ c) (hz : 0 ≤ z) (hT : 0 ≤ T) :
    (-3) + z * (23 + 3 * c) + (-3) * z * (T + c) = (-3) + 23 * z + (-3) * T * z := by
  field_simp
  try ring

end Interp

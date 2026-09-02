/- telperion 0.1.6 | family AlgebraicBracket | input-hash fc3641b4a5819a75
   3 theorems, 9 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace AlgebraicBracket

theorem sqrt_two :
    (1 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (17 / 12) := by
  refine ⟨Real.le_sqrt_of_sq_le (by norm_num),
          Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩⟩
theorem sqrt_three :
    ((12 / 7) : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ (7 / 4) := by
  refine ⟨Real.le_sqrt_of_sq_le (by norm_num),
          Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩⟩
theorem sqrt_twentythree :
    ((14 / 3) : ℝ) ≤ Real.sqrt 23 ∧ Real.sqrt 23 ≤ (24 / 5) := by
  refine ⟨Real.le_sqrt_of_sq_le (by norm_num),
          Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩⟩

end AlgebraicBracket

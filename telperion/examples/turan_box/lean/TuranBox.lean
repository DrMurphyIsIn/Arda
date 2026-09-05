/- telperion 0.1.6 | family TuranBox | input-hash e2a5c2be87f18e3d
   1 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace TuranBox

theorem turan_triple_1_2_1 : ∀ a0 a1 a2 : ℝ, 1 ≤ a0 → a0 ≤ 1 → 2 ≤ a1 → a1 ≤ 2 → 1 ≤ a2 → a2 ≤ 1 → (0:ℝ) ≤ a1 ^ 2 - a0 * a2 := by
  intro a0 a1 a2 hlo0 hhi0 hlo1 hhi1 hlo2 hhi2
  nlinarith [sq_nonneg (a0 - 1), sq_nonneg (1 - a0), sq_nonneg (a1 - 2), sq_nonneg (2 - a1), sq_nonneg (a2 - 1), sq_nonneg (1 - a2), mul_nonneg (by linarith : (0:ℝ) ≤ a0 - 1) (by linarith : (0:ℝ) ≤ a2 - 1), mul_nonneg (by linarith : (0:ℝ) ≤ a0 - 1) (by linarith : (0:ℝ) ≤ 1 - a2), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a0) (by linarith : (0:ℝ) ≤ a2 - 1), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a0) (by linarith : (0:ℝ) ≤ 1 - a2)]
example : ∀ a0 a1 a2 : ℝ, 1 ≤ a0 → a0 ≤ 1 → 2 ≤ a1 → a1 ≤ 2 → 1 ≤ a2 → a2 ≤ 1 → (0:ℝ) ≤ a1 ^ 2 - a0 * a2 := turan_triple_1_2_1

end TuranBox

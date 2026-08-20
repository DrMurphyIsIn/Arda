/- telperion 0.1.6 | family RealNSSFind | input-hash 6bf2c7fbb6c8afd3
   2 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace RealNSSFind

-- real_nss_found_x: Real-Nullstellensatz certificate  p^(2m) + s = Σ h_k·g_k (s a sum of squares) — p vanishes on the REAL variety.
theorem real_nss_found_x : ∀ x y : ℝ, x ^ 2 + y ^ 2 = 0 → x = 0 := by
  intro x y e1
  have hpow : (0:ℝ) ≤ (x)^2 := by positivity
  have hsos : (0:ℝ) ≤ 1 * (y)^2 := by positivity
  have key : (x)^2 + (1 * (y)^2) = 0 := by linear_combination (1) * e1
  have hz : (x)^2 = 0 := by linarith
  exact (pow_eq_zero_iff (by norm_num)).mp hz

-- real_nss_found_y: Real-Nullstellensatz certificate  p^(2m) + s = Σ h_k·g_k (s a sum of squares) — p vanishes on the REAL variety.
theorem real_nss_found_y : ∀ x y : ℝ, x ^ 2 + y ^ 2 = 0 → y = 0 := by
  intro x y e1
  have hpow : (0:ℝ) ≤ (y)^2 := by positivity
  have hsos : (0:ℝ) ≤ 1 * (x)^2 := by positivity
  have key : (y)^2 + (1 * (x)^2) = 0 := by linear_combination (1) * e1
  have hz : (y)^2 = 0 := by linarith
  exact (pow_eq_zero_iff (by norm_num)).mp hz

end RealNSSFind
end G1

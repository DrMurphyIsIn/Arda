/- telperion 0.1.6 | family Hyperbolicity | input-hash 44104242e1f13db3
   2 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import HyperbolicityBridge

namespace Hyperbolicity

theorem x_sq_minus_one_real_rooted : ∀ a0 a1 a2 : ℝ, (-1) ≤ a0 → a0 ≤ (-1) → 0 ≤ a1 → a1 ≤ 0 → 1 ≤ a2 → a2 ≤ 1 → (Polynomial.C a2 * Polynomial.X ^ 2 + Polynomial.C a1 * Polynomial.X + Polynomial.C a0).roots.card = 2 := by
  intro a0 a1 a2 hlo0 hhi0 hlo1 hhi1 hlo2 hhi2
  have ha : a2 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < a2)
  have hdisc : (0:ℝ) ≤ a1 ^ 2 - 4 * a2 * a0 := by
    nlinarith [sq_nonneg (a0 - (-1)), sq_nonneg ((-1) - a0), sq_nonneg (a1 - 0), sq_nonneg (0 - a1), sq_nonneg (a2 - 1), sq_nonneg (1 - a2), mul_nonneg (by linarith : (0:ℝ) ≤ a0 - (-1)) (by linarith : (0:ℝ) ≤ a2 - 1), mul_nonneg (by linarith : (0:ℝ) ≤ a0 - (-1)) (by linarith : (0:ℝ) ≤ 1 - a2), mul_nonneg (by linarith : (0:ℝ) ≤ (-1) - a0) (by linarith : (0:ℝ) ≤ a2 - 1), mul_nonneg (by linarith : (0:ℝ) ≤ (-1) - a0) (by linarith : (0:ℝ) ≤ 1 - a2)]
  exact hyperbolic_deg2_of_discrim_nonneg a2 a1 a0 ha hdisc
example : ∀ a0 a1 a2 : ℝ, (-1) ≤ a0 → a0 ≤ (-1) → 0 ≤ a1 → a1 ≤ 0 → 1 ≤ a2 → a2 ≤ 1 → (Polynomial.C a2 * Polynomial.X ^ 2 + Polynomial.C a1 * Polynomial.X + Polynomial.C a0).roots.card = 2 := x_sq_minus_one_real_rooted
theorem x_sq_minus_3x_plus_2_real_rooted : ∀ a0 a1 a2 : ℝ, 2 ≤ a0 → a0 ≤ 2 → (-3) ≤ a1 → a1 ≤ (-3) → 1 ≤ a2 → a2 ≤ 1 → (Polynomial.C a2 * Polynomial.X ^ 2 + Polynomial.C a1 * Polynomial.X + Polynomial.C a0).roots.card = 2 := by
  intro a0 a1 a2 hlo0 hhi0 hlo1 hhi1 hlo2 hhi2
  have ha : a2 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < a2)
  have hdisc : (0:ℝ) ≤ a1 ^ 2 - 4 * a2 * a0 := by
    nlinarith [sq_nonneg (a0 - 2), sq_nonneg (2 - a0), sq_nonneg (a1 - (-3)), sq_nonneg ((-3) - a1), sq_nonneg (a2 - 1), sq_nonneg (1 - a2), mul_nonneg (by linarith : (0:ℝ) ≤ a0 - 2) (by linarith : (0:ℝ) ≤ a2 - 1), mul_nonneg (by linarith : (0:ℝ) ≤ a0 - 2) (by linarith : (0:ℝ) ≤ 1 - a2), mul_nonneg (by linarith : (0:ℝ) ≤ 2 - a0) (by linarith : (0:ℝ) ≤ a2 - 1), mul_nonneg (by linarith : (0:ℝ) ≤ 2 - a0) (by linarith : (0:ℝ) ≤ 1 - a2)]
  exact hyperbolic_deg2_of_discrim_nonneg a2 a1 a0 ha hdisc
example : ∀ a0 a1 a2 : ℝ, 2 ≤ a0 → a0 ≤ 2 → (-3) ≤ a1 → a1 ≤ (-3) → 1 ≤ a2 → a2 ≤ 1 → (Polynomial.C a2 * Polynomial.X ^ 2 + Polynomial.C a1 * Polynomial.X + Polynomial.C a0).roots.card = 2 := x_sq_minus_3x_plus_2_real_rooted

end Hyperbolicity

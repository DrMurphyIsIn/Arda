/- PHASE 4 (dVP frontier, BLASCHKE step 2): the canonical-decomposition part `g` is analytic and
   zero-free on the open ball.

   `MeromorphicOn.exists_canonicalDecomp` returns `g` in meromorphic NORMAL FORM on `closedBall 0 R`
   with `g ≠ 0` on `ball 0 R` (`CanonicalDecomp.ne_zero`).  Normal form + nonvanishing forces order 0,
   hence analyticity: `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff` (`g z ≠ 0 ⟹ order 0`) then
   `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` (`order ≥ 0 ⟹ AnalyticAt`).

   Output: `g` is `AnalyticOnNhd` and zero-free on `ball 0 R` — the input `DlvpMaxMod` needs for the
   log branch and max-modulus.  conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

/-- **The canonical-decomposition part `g` is analytic on the ball.**  From a `CanonicalDecomp f g R`,
    `g` is analytic at every point of `ball 0 R` (normal form + nonvanishing ⟹ order 0 ⟹ analytic). -/
theorem canonicalDecomp_analyticOnNhd {f g : ℂ → ℂ} {R : ℝ} (D : CanonicalDecomp f g R) :
    AnalyticOnNhd ℂ g (ball 0 R) := by
  intro z hz
  have hzc : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
  have hnf : MeromorphicNFAt g z := D.meromorphicNFOn hzc
  have hne : g z ≠ 0 := D.ne_zero z hz
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (le_of_eq (hnf.meromorphicOrderAt_eq_zero_iff.mpr hne).symm)

/-- `g` is zero-free on `ball 0 R` (a restatement of `CanonicalDecomp.ne_zero`). -/
theorem canonicalDecomp_ne_zero {f g : ℂ → ℂ} {R : ℝ} (D : CanonicalDecomp f g R) :
    ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0 := D.ne_zero

end ZeroFreeBridge

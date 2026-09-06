/- PHASE 4 (dVP frontier, BLASCHKE step 3b): the entire-part bound for the canonical decomposition
   — `‖logDeriv g 0‖ ≤ 2 M'/(R − r)` with no AP term.

   Combines the boundary identity `‖f‖ = ‖g‖` on the sphere (`DlvpCanonicalNorm`) with the g-side
   inputs (zero-free `DlvpBlaschkeAnalytic`, continuous up to the boundary) and feeds the max-modulus
   entire-part bound `DlvpMaxMod.norm_logDeriv_le_of_sphere_log_norm_le`.  Because `‖g‖ = ‖f‖` on the
   sphere, the required sphere bound is on `log‖f‖` (the growth of `f = ζ`) alone — no zero-factor
   (AP) term, resolving the monomial-path gap.

     `norm_logDeriv_canonicalDecomp_le` :  for a `CanonicalDecomp f g R`, `g` continuous up to the
       boundary, and `log‖f z‖ − log‖g 0‖ ≤ M'` on the sphere (`M' > 0`, `0 < r < R`),
         `‖logDeriv g 0‖ ≤ 2 M'/(R − r)`.

   Feeding `M' = O(L)` (ζ growth via `zeta_sphere_bound` + `g 0` lower bound) gives `‖E‖ = O(L)`.
   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpMaxMod
import DlvpCanonicalNorm
import DlvpBlaschkeAnalytic

open Complex Metric

namespace ZeroFreeBridge

/-- **Entire-part bound for the canonical decomposition.**  For `CanonicalDecomp f g R`, `g`
    continuous up to the boundary, and a growth bound `log‖f z‖ − log‖g 0‖ ≤ M'` on the sphere,
    the entire part at the centre is bounded: `‖logDeriv g 0‖ ≤ 2 M'/(R − r)`. -/
theorem norm_logDeriv_canonicalDecomp_le {f g : ℂ → ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM' : 0 < M')
    (D : CanonicalDecomp f g R)
    (hd : DiffContOnCl ℂ g (ball 0 R))
    (hcont_f : ContinuousOn f (sphere 0 R))
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖f z‖ - Real.log ‖g 0‖ ≤ M') :
    ‖logDeriv g 0‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0 := canonicalDecomp_ne_zero D
  have hcont_g : ContinuousOn g (sphere 0 R) :=
    hd.continuousOn.mono (by rw [closure_ball 0 hR.ne']; exact sphere_subset_closedBall)
  have hsphere : ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M' := by
    intro z hz
    rw [← canonicalDecomp_norm_eq_on_sphere hR D hcont_f hcont_g hz]
    exact hbound z hz
  exact norm_logDeriv_le_of_sphere_log_norm_le hr hrR hM' hd hne hsphere

end ZeroFreeBridge

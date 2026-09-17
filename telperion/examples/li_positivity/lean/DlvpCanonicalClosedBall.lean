/- PHASE 4 (dVP frontier, item 1 RESOLVED — g boundary regularity via option (b)): the
   canonical-decomp quotient `g` is analytic UP TO THE SPHERE, so `hg_cont`/`hg_dcc` (the two
   remaining inputs of `norm_logDeriv_g_le_strip`) are discharged.

   The subtlety (PR #287): `D` only gives `g` `MeromorphicNFOn (closedBall 0 R)` + zero-free on the
   OPEN ball; `D.eventuallyEq` holds only `codiscreteWithin (closedBall)`, giving no control in a full
   punctured neighbourhood of a sphere point — so an order-transfer via `meromorphicOrderAt_congr`
   fails there.

   RESOLUTION: Mathlib's `CanonicalDecomp.divisor_eq_divisor` already proves the hard step,
   `divisor g (closedBall 0 R) x = divisor f (sphere 0 R) x` (its sphere case: the canonical factors
   are analytic and non-vanishing there, so the orders of `f` and `g` agree).  When `f = ζ(c₀+·)` is
   analytic on the sphere, `divisor f (sphere) ≥ 0`, hence `divisor g (closedBall) ≥ 0`, hence — by
   `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd` — `g` is `AnalyticOnNhd (closedBall 0 R)`.
   `ContinuousOn` (sphere) and `DiffContOnCl` (ball) follow immediately.  conjecture1_proved = False.
-/
import Mathlib

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **`g` analytic up to the sphere.**  If `f` is analytic on `sphere 0 R`, the canonical-decomp
    quotient `g` is `AnalyticOnNhd` on the CLOSED ball.  Via `CanonicalDecomp.divisor_eq_divisor`
    (order `g` = order `f` on the sphere) + `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`. -/
theorem canonicalDecomp_analyticOnNhd_closedBall {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R) (hf_sphere : AnalyticOnNhd ℂ f (sphere 0 R)) :
    AnalyticOnNhd ℂ g (closedBall 0 R) := by
  rw [← D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd]
  intro x
  rw [D.divisor_eq_divisor hR]
  exact hf_sphere.divisor_nonneg x

/-- **`hg_cont`.**  `g` continuous on the sphere. -/
theorem canonicalDecomp_contOn_sphere {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R) (hf_sphere : AnalyticOnNhd ℂ f (sphere 0 R)) :
    ContinuousOn g (sphere 0 R) :=
  ((canonicalDecomp_analyticOnNhd_closedBall hR D hf_sphere).mono
    sphere_subset_closedBall).continuousOn

/-- **`hg_dcc`.**  `g` is `DiffContOnCl` on the open ball (differentiable inside, continuous up to
    the closed ball). -/
theorem canonicalDecomp_diffContOnCl {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R) (hf_sphere : AnalyticOnNhd ℂ f (sphere 0 R)) :
    DiffContOnCl ℂ g (ball 0 R) := by
  have hg := canonicalDecomp_analyticOnNhd_closedBall hR D hf_sphere
  refine ⟨(hg.mono ball_subset_closedBall).differentiableOn, ?_⟩
  rw [closure_ball 0 hR.ne']
  exact hg.continuousOn

end ZeroFreeBridge

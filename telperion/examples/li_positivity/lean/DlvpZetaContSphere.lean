/- PHASE 4 (dVP frontier, item 1 partial — the ζ-side sphere continuity `hf_cont`): one of the four
   inputs `norm_logDeriv_g_le_strip` needs to produce `hg_bound`.

   `norm_logDeriv_g_le_strip` (via `norm_logDeriv_le_of_sphere_log_norm_le_interior`) requires, on the
   sphere `sphere 0 R`:  `hf_cont` (ζ(c₀+·) continuous), `hg_cont` (g continuous), `hg_dcc`
   (`DiffContOnCl g (ball 0 R)`), plus `hfg0` (`zeta_norm_le_g_zero`, already built).

   `hf_cont` is elementary: ζ is analytic (hence continuous) on `closedBall c₀ R` when `1 ∉ closedBall`,
   and the shift `w ↦ c₀ + w` maps `sphere 0 R` into `closedBall c₀ R`.

   BOUNDARY-REGULARITY SUBTLETY (the genuinely hard remainder of item 1): `hg_cont`/`hg_dcc` are NOT
   derivable from the `CanonicalDecomp` alone.  `D` gives `g` `MeromorphicNFOn (closedBall 0 R)` and
   zero-free only on the OPEN ball; `D.eventuallyEq` holds `codiscreteWithin (closedBall 0 R)`, which
   gives NO control in a full punctured neighbourhood of a sphere point (points just OUTSIDE the ball
   are uncontrolled), so the order-transfer `order g = order f - order B` (which would give `g`
   analytic on the sphere) cannot be run via `meromorphicOrderAt_congr` at boundary points.  The two
   candidate resolutions — (a) reformulate the entire-part bound at a strictly smaller radius `r < R`
   (where `g` is analytic, but then the Blaschke modulus-1 identity `‖g‖=‖ζ‖` no longer holds on
   `sphere r`), or (b) a construction-level argument that `g = ζ(c₀+·)·∏canonicalFactor^{divisor}` is
   analytic up to the sphere — are each real work, not a quick lemma.  conjecture1_proved = False.
-/
import DlvpZetaDisk

open Complex Metric

namespace ZeroFreeBridge

/-- **`hf_cont`: the recentred ζ is continuous on the sphere.**  For `1 ∉ closedBall c₀ R`,
    `fun w => riemannZeta (c₀ + w)` is `ContinuousOn` `sphere 0 R` (ζ analytic on the disk, composed
    with the shift into `closedBall c₀ R`). -/
theorem zeta_recenter_cont_sphere {c₀ : ℂ} {R : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) :
    ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R) := by
  have hζ : ContinuousOn riemannZeta (closedBall c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).continuousOn
  have hmaps : Set.MapsTo (fun w => c₀ + w) (sphere (0 : ℂ) R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, hw]
  exact hζ.comp ((continuous_const.add continuous_id).continuousOn) hmaps

end ZeroFreeBridge

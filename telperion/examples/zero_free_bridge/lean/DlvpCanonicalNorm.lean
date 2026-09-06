/- PHASE 4 (dVP frontier, BLASCHKE step 3a): ‖f‖ = ‖g‖ on the sphere for the canonical
   decomposition — the no-AP boundary identity, assembled for the actual `CanonicalDecomp`.

   Composes the Blaschke atoms:
     * `DlvpBlaschke.norm_finprod_canonicalFactor_zpow_eq_one` — ‖Blaschke product‖ = 1 on the sphere;
     * `DlvpSphereDense.dense_inter_sphere_of_codiscrete` — the codiscrete agreement set is dense in
       the sphere;
     * `DlvpBlaschkeSphere.norm_eq_of_codiscrete_factor_on_sphere` — continuity + density upgrade.

   Result: for a `CanonicalDecomp f g R` with `f, g` continuous on the sphere, `‖f z‖ = ‖g z‖` for
   every `z ∈ sphere 0 R`.  With `f = ζ` this makes the boundary `M' = sup log‖ζ‖ − log‖g c‖ = O(L)`
   with NO zero-factor term.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpBlaschke
import DlvpBlaschkeSphere
import DlvpSphereDense

open Complex Metric MeromorphicOn Filter

namespace ZeroFreeBridge

/-- **Boundary norm identity for a canonical decomposition.**  For `CanonicalDecomp f g R`
    (`0 < R`, `f, g` continuous on the sphere), `‖f z‖ = ‖g z‖` at every `z ∈ sphere 0 R`. -/
theorem canonicalDecomp_norm_eq_on_sphere {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R)
    (hcont_f : ContinuousOn f (sphere 0 R)) (hcont_g : ContinuousOn g (sphere 0 R))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖f z‖ = ‖g z‖ := by
  -- support of the (negated) divisor is finite and lives in the open ball.
  have hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D.meromorphicOn.divisor_ball_support_finite
  have hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) R := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hdu : divisor f (ball 0 R) u ≠ 0 := fun h => hu (by rw [h]; ring)
    exact (divisor f (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hdu)
  -- the Blaschke product has modulus 1 on the sphere.
  have hB1 : ∀ w ∈ sphere (0 : ℂ) R,
      ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(divisor f (ball 0 R) u))) w‖ = 1 :=
    fun w hw => norm_finprod_canonicalFactor_zpow_eq_one _ hfin hsupp hw
  -- the agreement set is codiscrete, hence dense in the sphere.
  have hcod : {w | f w = (∏ᶠ u, (canonicalFactor R u) ^ (-(divisor f (ball 0 R) u))) w • g w}
      ∈ codiscreteWithin (closedBall (0 : ℂ) R) := D.eventuallyEq
  have hdense := dense_inter_sphere_of_codiscrete hR hcod
  exact norm_eq_of_codiscrete_factor_on_sphere hcont_f hcont_g hB1 hdense hz

end ZeroFreeBridge

/- PHASE 4 (dVP frontier, BLASCHKE step 1): the pointwise sphere identity ‖f‖ = ‖g‖ from a
   codiscrete factorization, via continuity + density.

   `MeromorphicOn.exists_canonicalDecomp` gives `f =ᶠ[codiscreteWithin closedBall] B • g` (with
   `B` the finite Blaschke product `∏ᶠ canonicalFactor^{-divisor}`), i.e. `f w = B w • g w` only
   OFF a discrete exceptional set.  On the boundary sphere `‖B‖ = 1`
   (`DlvpBlaschke.norm_finprod_canonicalFactor_zpow_eq_one`), so wherever the factorization holds
   `‖f w‖ = ‖g w‖`.  Both norms are continuous, and the agreement set is dense in the sphere (the
   exceptional set is discrete, hence finite on the compact sphere, hence its complement is
   cofinite = dense).  `Set.EqOn.closure` then upgrades the identity to EVERY sphere point.

   This atom does the continuity+density upgrade, taking density as the one explicit hypothesis
   `hdense` (dischargeable from codiscreteWithin ⟹ locally-finite complement ⟹ finite on the
   compact sphere).  Function-agnostic in `f, g, B`.  conjecture1_proved = False (NOT RH).
-/
import DlvpBlaschke

open Complex Metric Set

namespace ZeroFreeBridge

/-- **Pointwise sphere identity from a codiscrete unit-modulus factorization.**  If `f w = B w • g w`
    on a set dense in `sphere 0 R`, `‖B‖ = 1` on the sphere, and `f, g` are continuous on the sphere,
    then `‖f z‖ = ‖g z‖` for EVERY `z ∈ sphere 0 R`. -/
theorem norm_eq_of_codiscrete_factor_on_sphere {f g B : ℂ → ℂ} {R : ℝ}
    (hcont_f : ContinuousOn f (sphere 0 R)) (hcont_g : ContinuousOn g (sphere 0 R))
    (hB1 : ∀ z ∈ sphere (0 : ℂ) R, ‖B z‖ = 1)
    (hdense : sphere (0 : ℂ) R ⊆ closure ({w | f w = B w • g w} ∩ sphere 0 R))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖f z‖ = ‖g z‖ := by
  set S : Set ℂ := {w | f w = B w • g w} ∩ sphere 0 R with hSdef
  have hSsub : S ⊆ sphere (0 : ℂ) R := Set.inter_subset_right
  have hEq : Set.EqOn (fun w => ‖f w‖) (fun w => ‖g w‖) S := by
    intro w hw
    show ‖f w‖ = ‖g w‖
    rw [hw.1, norm_smul, hB1 w hw.2, one_mul]
  exact hEq.of_subset_closure hcont_f.norm hcont_g.norm hSsub hdense hz

end ZeroFreeBridge

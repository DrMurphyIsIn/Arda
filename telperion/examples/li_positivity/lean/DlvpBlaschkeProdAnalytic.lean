/- PHASE 4 (dVP frontier, BLASCHKE item (d2) sub-lemma): the finite Blaschke product is analytic
   AWAY FROM ITS ZEROS.

   The Blaschke product `∏ᶠ_u (canonicalFactor R u)^{n u}` has (for `n = -divisor ≤ 0`) removable
   singularities exactly at the support points `u`.  AT a point `z` avoiding all of them, each factor
   is genuinely analytic and nonzero (`canonicalFactor` is analytic off `{u}` and nonzero away from
   `u` inside the disk), so `AnalyticAt.zpow` applies to each and `Finset.analyticAt_prod` to the
   product — NO meromorphic-order argument needed.

   This is exactly the analyticity the codiscrete → pointwise transfer (`DlvpTransfer`) needs to split
   `logDeriv ζ = logDeriv(Blaschke) + logDeriv g` at points off the zeros (item d2).  Function-agnostic
   in the exponent `n`.  conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

open Complex Metric

namespace ZeroFreeBridge

/-- **The Blaschke product is analytic away from its zeros.**  For finitely-supported `n` with
    support in `ball 0 R`, at a point `z ∈ closedBall 0 R` avoiding every support point,
    `∏ᶠ_u (canonicalFactor R u)^{n u}` is analytic. -/
theorem blaschke_analyticAt {R : ℝ} (n : ℂ → ℤ) (hn : (Function.support n).Finite)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R)
    (hsupp : ∀ u ∈ hn.toFinset, u ∈ ball (0 : ℂ) R)
    (hzne : ∀ u ∈ hn.toFinset, z ≠ u) :
    AnalyticAt ℂ (∏ᶠ u, (canonicalFactor R u) ^ (n u)) z := by
  have hsub : Function.mulSupport (fun u => (canonicalFactor R u) ^ (n u)) ⊆ hn.toFinset := by
    intro u hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hnu
    apply hu
    funext w
    simp [hnu]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  apply Finset.analyticAt_prod
  intro u hu
  apply AnalyticAt.zpow
  · exact analyticOnNhd_canonicalFactor R u z (Set.mem_compl_singleton_iff.mpr (hzne u hu))
  · exact canonicalFactor_ne_zero (hsupp u hu) hz (hzne u hu)

end ZeroFreeBridge

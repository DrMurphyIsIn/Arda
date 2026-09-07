/- PHASE 4 (dVP frontier, the Blaschke-CENTRE relation, assembled): `‖ζ c₀‖ ≤ ‖g 0‖` from `‖B 0‖ ≤ 1`
   (`DlvpBlaschkeCenter.norm_blaschke_center_le_one`) and the centre factorization `ζ c₀ = B 0 · g 0`.

   The recentred ζ is `f = ζ(c₀+·)`, `f 0 = ζ c₀`; the CanonicalDecomp gives `f = B·g` codiscretely, and
   at the centre (`ζ c₀ ≠ 0`, so `0` is not a zero and `B` is analytic there) the identity principle
   upgrades this to the pointwise `ζ c₀ = B 0 · g 0`.  Taking that pointwise factorization as the single
   hypothesis `hfac0`, `‖B 0‖ ≤ 1` yields `‖ζ c₀‖ = ‖B 0‖·‖g 0‖ ≤ ‖g 0‖` — exactly the hypothesis
   `DlvpZetaEntire.norm_logDeriv_g_le` needs.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpBlaschkeCenter

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **The Blaschke-centre relation.**  `‖ζ c₀‖ ≤ ‖g 0‖`, from `‖B 0‖ ≤ 1` and the centre factorization
    `ζ c₀ = B 0 · g 0`. -/
theorem zeta_norm_le_g_zero {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (m : ℂ → ℤ) (hfin : (Function.support (fun u => -(m u))).Finite)
    (hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0 ∧ ‖u‖ < R) (hm : ∀ u ∈ hfin.toFinset, 0 ≤ m u)
    (hfac0 : riemannZeta c₀
      = (∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0 * g 0) :
    ‖riemannZeta c₀‖ ≤ ‖g 0‖ := by
  have hB : ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0‖ ≤ 1 :=
    norm_blaschke_center_le_one hR m hfin hsupp hm
  calc ‖riemannZeta c₀‖ = ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0‖ * ‖g 0‖ := by
        rw [hfac0, norm_mul]
    _ ≤ 1 * ‖g 0‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
    _ = ‖g 0‖ := one_mul _

end ZeroFreeBridge

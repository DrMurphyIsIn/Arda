/- PHASE 4 (dVP frontier, item (C) — hpole, the last genuine analytic input): the pole bound
   `-Re(ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + A` near s=1.

   This turned out to be a DIRECT consequence of Mathlib's asymptotics: `log_deriv_riemannZeta_add_
   inv_sub_bounded` states `ζ'/ζ(s) + (s-1)⁻¹ =O[𝓝[≠] 1] 1` (the pole of ζ'/ζ at s=1 is exactly
   -(s-1)⁻¹, so the sum is bounded).  Extracting the O(1) constant `A` and using `Re z ≥ -‖z‖`
   (`Complex.re_le_norm` on `-z`): `Re(ζ'/ζ(σ) + (σ-1)⁻¹) ≥ -A`, i.e. `-Re(ζ'/ζ(σ)) ≤ Re((σ-1)⁻¹)+A`.
   No compactness / h'/h argument needed.  Eventually near 1 (σ = 1+c/L → 1 as |γ|→∞, so in range).
   conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib
open Complex Filter Topology

namespace ZeroFreeBridge

/-- **hpole (pole bound near s=1).**  Directly from Mathlib's
    `log_deriv_riemannZeta_add_inv_sub_bounded` (ζ'/ζ(s) + (s-1)⁻¹ = O(1) near 1):
    `-Re(ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + A` eventually near 1, for an explicit constant A. -/
theorem hpole_bounded :
    ∃ A : ℝ, ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      (-deriv riemannZeta s / riemannZeta s).re ≤ (1 / (s - 1)).re + A := by
  obtain ⟨A, hA⟩ := Asymptotics.isBigO_iff.mp log_deriv_riemannZeta_add_inv_sub_bounded
  refine ⟨A, ?_⟩
  filter_upwards [hA] with s hs
  rw [norm_one, mul_one] at hs
  have hre : -(deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹).re ≤ A := by
    calc -(deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹).re
        = (-(deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹)).re := by rw [Complex.neg_re]
      _ ≤ ‖-(deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹)‖ := Complex.re_le_norm _
      _ = ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖ := by rw [norm_neg]
      _ ≤ A := hs
  rw [Complex.add_re] at hre
  rw [neg_div, Complex.neg_re, one_div]
  linarith [hre]

end ZeroFreeBridge

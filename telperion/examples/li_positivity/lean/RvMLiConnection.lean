/-
RvMLiConnection — the full connection to the upstream Li machinery.

The upstream Li coefficients are `taylorCoeff riemannXi n = (deriv^[n](logDeriv(phi riemannXi)))0/n!`
with `phi f z = f(1/(1−z))`.  The frontier-(a) split `logDeriv ξ = 1/s + 1/(s−1) + logDeriv ζ +
logDeriv Γℝ` (with `ξ = xiTele = riemannXi`), pulled back through the Möbius map via `logDeriv_phi`,
exhibits the **archimedean generating function `logDeriv(phi Γℝ)`** — whose Taylor coefficients we
computed as exact polygamma data (`taylorCoeff_Gammaℝ_leibniz`) — as an explicit summand of
`logDeriv(phi riemannXi)`:

  * `logDeriv_phi_riemannXi_split` —
      `logDeriv(phi ξ) z = (1/s)·M'(z) + (1/(s−1))·M'(z) + logDeriv ζ(s)·M'(z) + logDeriv(phi Γℝ) z`,
    `s = 1/(1−z) = M z`, valid off the poles/zeros.

This places the fully-reduced archimedean factor inside the exact generating function of the Li
coefficients whose positivity `LiCriterion.li_criterion_rh_iff` equates to RH.  conjecture1_proved = False.
-/
import Mathlib
import RvMPhiChain
import RvMLiFrontierA
import RvMLiUnified

open Complex

namespace RvMWeierstrass

set_option maxHeartbeats 1600000 in
/-- **The archimedean generating function inside the Li generating function.**  For `s = (1−z)⁻¹`
    off the poles/zeros, `logDeriv (phi ξ) z` splits as the four Möbius pullbacks, the archimedean one
    being `logDeriv (phi Γℝ) z` (whose Taylor coefficients are the Phase-4 polygamma data). -/
theorem logDeriv_phi_riemannXi_split {z : ℂ} (hz : z ≠ 1)
    (hs0 : (1 - z)⁻¹ ≠ 0) (hs1 : (1 - z)⁻¹ ≠ 1)
    (hζ : riemannZeta ((1 - z)⁻¹) ≠ 0) (hG : Complex.Gammaℝ ((1 - z)⁻¹) ≠ 0) :
    logDeriv (LiCriterion.phi LiCriterion.riemannXi) z
      = ((1 - z)⁻¹)⁻¹ * deriv (fun w : ℂ => (1 - w)⁻¹) z
        + ((1 - z)⁻¹ - 1)⁻¹ * deriv (fun w : ℂ => (1 - w)⁻¹) z
        + logDeriv riemannZeta ((1 - z)⁻¹) * deriv (fun w : ℂ => (1 - w)⁻¹) z
        + logDeriv (LiCriterion.phi Complex.Gammaℝ) z := by
  have hphiXi : LiCriterion.phi LiCriterion.riemannXi
      = fun w : ℂ => LiCriterion.riemannXi ((1 - w)⁻¹) := by
    rw [LiCriterion.phi_eq]; funext w; rw [one_div]
  have hphiG : LiCriterion.phi Complex.Gammaℝ = fun w : ℂ => Complex.Gammaℝ ((1 - w)⁻¹) := by
    rw [LiCriterion.phi_eq]; funext w; rw [one_div]
  -- Γℝ is differentiable at `(1−z)⁻¹` (it is off its zeros)
  have hs2 : ∀ m : ℕ, ((1 - z)⁻¹) / 2 ≠ -(m : ℂ) := by
    intro m hm
    apply hG
    rw [Complex.Gammaℝ_eq_zero_iff]
    refine ⟨m, ?_⟩
    rw [div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)] at hm
    push_cast at hm ⊢; linear_combination hm
  have hGdiff : DifferentiableAt ℂ Complex.Gammaℝ ((1 - z)⁻¹) := by
    rw [show Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) from by
      funext s; rw [Complex.Gammaℝ_def]]
    have hhalf : DifferentiableAt ℂ (fun s : ℂ => s / 2) ((1 - z)⁻¹) :=
      differentiableAt_id.div_const (2 : ℂ)
    have hcpow : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) ((1 - z)⁻¹) :=
      (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    have hgam : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) ((1 - z)⁻¹) :=
      (Complex.differentiableAt_Gamma _ hs2).comp ((1 - z)⁻¹) hhalf
    exact hcpow.mul hgam
  -- rewrite the archimedean summand on the right to the pulled-back form
  rw [show logDeriv (LiCriterion.phi Complex.Gammaℝ) z
        = logDeriv Complex.Gammaℝ ((1 - z)⁻¹) * deriv (fun w : ℂ => (1 - w)⁻¹) z from by
      rw [hphiG, logDeriv_phi hz hGdiff]]
  -- pull back the four-split of `logDeriv ξ` through the Möbius map
  rw [hphiXi, logDeriv_phi hz LiCriterion.xi_entire.differentiableAt,
    ← RvMLiUnified.xiTele_eq_riemannXi, DiffractionCore.logDeriv_xiTele_four_split hs0 hs1 hζ hG]
  ring

end RvMWeierstrass

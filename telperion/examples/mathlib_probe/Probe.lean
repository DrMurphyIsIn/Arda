/- PROBE 8: the ASSEMBLY logic (bridge + three residue limits -> False), with the bridge
   STUBBED as a hypothesis matching zeta_logDeriv_comb_nonneg's conclusion.  Fast logic check
   before wiring the real bridge. -/
import Mathlib
open Filter Topology

theorem zeta_boundary_contradiction (t : ℝ) (k k' : ℤ) (hk : 1 ≤ k) (hk' : 0 ≤ k')
    (bridge : ∀ σ : ℝ, 1 < σ →
      0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re)
    (hpole : Tendsto (fun σ : ℝ => (σ - 1) *
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re) (𝓝[>] (1 : ℝ)) (𝓝 1))
    (hz1 : Tendsto (fun σ : ℝ => (σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re) (𝓝[>] (1 : ℝ)) (𝓝 (-(k : ℝ))))
    (hz2 : Tendsto (fun σ : ℝ => (σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 (-(k' : ℝ)))) :
    False := by
  -- G σ = (σ-1) * (bracket) is >= 0 eventually (bridge, times σ-1 > 0)
  have hGnn : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      0 ≤ (σ - 1) * (3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have h1 : (1 : ℝ) < σ := hσ
    exact mul_nonneg (by linarith) (bridge σ h1)
  -- G σ -> 3 - 4k - k'
  have hlim := ((hpole.const_mul 3).add (hz1.const_mul 4)).add hz2
  have hval : (3 : ℝ) * 1 + 4 * (-(k : ℝ)) + (-(k' : ℝ)) = 3 - 4 * (k : ℝ) - (k' : ℝ) := by ring
  rw [hval] at hlim
  have hGlim : Tendsto (fun σ : ℝ => (σ - 1) *
      (3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re))
      (𝓝[>] (1 : ℝ)) (𝓝 (3 - 4 * (k : ℝ) - (k' : ℝ))) := by
    convert hlim using 1
    funext σ; ring
  have hge : (0 : ℝ) ≤ 3 - 4 * (k : ℝ) - (k' : ℝ) := ge_of_tendsto hGlim hGnn
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk'0 : (0 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'
  linarith

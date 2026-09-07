/- PHASE 4 (dVP frontier, the CANONICAL-DECOMP layer): produce the two Blaschke BC-SUM outputs by
   applying `bc_sum_blaschke`, and feed the downstream assembly `dlvp_zeta_region_of_bc_sums`.

   `bc_sum_blaschke` needs a `CanonicalDecomp` of the recentred ζ, analyticity/non-vanishing of the
   quotient `g`, the finite divisor support, and the entire-part bound `‖logDeriv g z‖ ≤ Bg` (supplied by
   the interior bound `DlvpBCDerivInterior`/`DlvpEntirePlumbing`).  Applied at heights `γ` and `2γ`, it
   yields the two BC-SUM outputs `hbc₁, hbc₂`; `dlvp_zeta_region_of_bc_sums` then delivers the region.

   This is the top of the ζ instantiation: with a `CanonicalDecomp` and the two entire-part bounds in
   hand, `β ≤ 1 - 1/(112·A·L)`.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaBcBridge
import DlvpBCSumBlaschke

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- The recentred divisor support lies in `ball 0 R`, and its `c₀`-shift lies in `ball c₀ R`. -/
private theorem support_dom (c₀ : ℂ) (R : ℝ)
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite) :
    ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) R ∧ c₀ + u ∈ ball c₀ R := by
  intro u hu
  have hne : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0 := by
    have := hfin.mem_toFinset.mp hu
    simpa [Function.mem_support, neg_ne_zero] using this
  have huball : u ∈ ball (0 : ℂ) R :=
    (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
      (Function.mem_support.mpr hne)
  refine ⟨huball, ?_⟩
  rw [mem_ball_iff_norm, add_sub_cancel_left]
  rwa [mem_ball_zero_iff] at huball

/-- **The dVP region for ζ from a `CanonicalDecomp` + the two entire-part bounds.**  Applies
    `bc_sum_blaschke` at heights `γ` and `2γ` and feeds `dlvp_zeta_region_of_bc_sums`. -/
theorem dlvp_zeta_region_of_canonical_decomp (c₀ : ℂ) (σ A L β γ : ℝ) (k : ℤ) (R : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L)))) (hβσ : β < σ)
    (g : ℂ → ℂ) (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hg_ana : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite)
    (hf_mero : MeromorphicOn riemannZeta (ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    -- height γ (hzero)
    (hz₁ : (σ : ℂ) + (γ : ℂ) * I - c₀ ∈ ball (0 : ℂ) R)
    (hzne₁ : ∀ u ∈ hfin.toFinset, (σ : ℂ) + (γ : ℂ) * I - c₀ ≠ u)
    (hcz₁ : c₀ + ((σ : ℂ) + (γ : ℂ) * I - c₀) = (σ : ℂ) + (γ : ℂ) * I)
    (hdiff₁ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I))
    (Bg₁ : ℝ) (hg_bound₁ : ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - c₀)‖ ≤ Bg₁)
    (hAL₁ : (∑ u ∈ hfin.toFinset,
        |(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℝ)|)
          / (R - ‖(σ : ℂ) + (γ : ℂ) * I - c₀‖) + Bg₁ ≤ A * L)
    (hm₁ : ∀ ρ ∈ hfin.toFinset.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (ball c₀ R) ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ hfin.toFinset.image (fun u => c₀ + u)) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I)
    (hmρ₀ : divisor riemannZeta (ball c₀ R) ρ₀ = k)
    (hother₁ : ∀ ρ ∈ hfin.toFinset.image (fun u => c₀ + u), ρ ≠ ρ₀ → ρ.re < σ)
    -- height 2γ (htwo)
    (hz₂ : (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀ ∈ ball (0 : ℂ) R)
    (hzne₂ : ∀ u ∈ hfin.toFinset, (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀ ≠ u)
    (hcz₂ : c₀ + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
    (hdiff₂ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
    (Bg₂ : ℝ) (hg_bound₂ : ‖logDeriv g ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀)‖ ≤ Bg₂)
    (hAL₂ : (∑ u ∈ hfin.toFinset,
        |(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℝ)|)
          / (R - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀‖) + Bg₂ ≤ A * L)
    (hm₂ : ∀ ρ ∈ hfin.toFinset.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (ball c₀ R) ρ)
    (hlt₂ : ∀ ρ ∈ hfin.toFinset.image (fun u => c₀ + u), ρ.re < σ) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  have hbc₁ := bc_sum_blaschke hR D hf_ana hg_ana hg_ne hfin hz₁ hzne₁ hg_bound₁ hAL₁
  have hbc₂ := bc_sum_blaschke hR D hf_ana hg_ana hg_ne hfin hz₂ hzne₂ hg_bound₂ hAL₂
  exact dlvp_zeta_region_of_bc_sums c₀ σ A L β γ k R hA hL hk hσ_opt hβσ hf_mero hf'_mero hpole_pf
    hfin.toFinset (support_dom c₀ R hfin) hcz₁ hdiff₁ hbc₁ hm₁ ρ₀ hρ₀ hρ₀_eq hmρ₀ hother₁
    hfin.toFinset (support_dom c₀ R hfin) hcz₂ hdiff₂ hbc₂ hm₂ hlt₂

end ZeroFreeBridge

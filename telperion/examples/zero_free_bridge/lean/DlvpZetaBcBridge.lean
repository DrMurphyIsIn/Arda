/- PHASE 4 (dVP frontier, the downstream BRIDGE): turn `bc_sum_blaschke`'s recentred output into the
   region skeleton's `hzero` input, entirely by composition of already-built lemmas.

   `bc_sum_blaschke` gives (for `f = ζ(c₀+·)`, recentred eval point `zr = (σ+γI) - c₀`)
     `-Re(logDeriv f zr) ≤ AL - Re(Σ_u divisor f (ball 0 R) u /(zr - u))`.
   `herglotz_sum_reindex` rewrites the sum to the ORIGINAL-coordinate Herglotz sum
     `Σ_ρ divisor ζ (ball c₀ R) ρ /((σ+γI) - ρ)`; `neg_logDeriv_zeta_recenter_re` rewrites the left side
   to `-deriv ζ (σ+γI)/ζ(σ+γI)`; `hzero_of_blaschke` (the Herglotz lower bound) then delivers the
   `hzero` shape `-Re(ζ'/ζ)(σ+γI) ≤ AL - k/(σ-β)` that `DlvpZetaRegion.dlvp_zeta_region` consumes.

   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpDivisorTranslate
import DlvpBlaschkeToSkeleton
import DlvpZetaRecenter
import DlvpZetaRegion

open Complex MeromorphicOn

namespace ZeroFreeBridge

/-- **BC-SUM → `hzero`.**  The recentred Blaschke BC-SUM at height `γ`, reindexed to the true zeros and
    recentred back, yields the skeleton's `hzero` input `-Re(ζ'/ζ)(σ+γI) ≤ AL - k/(σ-β)`. -/
theorem hzero_shape_of_bc_sum (c₀ : ℂ) (σ γ β AL : ℝ) (k : ℤ) (R : ℝ)
    (hf_mero : MeromorphicOn riemannZeta (Metric.ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R))
    (s_rec : Finset ℂ)
    (hs_dom : ∀ u ∈ s_rec, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz : c₀ + ((σ : ℂ) + (γ : ℂ) * I - c₀) = (σ : ℂ) + (γ : ℂ) * I)
    (hdiff : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I))
    (hbc : (-(logDeriv (fun w => riemannZeta (c₀ + w)) ((σ : ℂ) + (γ : ℂ) * I - c₀))).re
             ≤ AL - (∑ u ∈ s_rec,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + (γ : ℂ) * I - c₀) - u)).re)
    (hm : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s_rec.image (fun u => c₀ + u)) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I)
    (hmρ₀ : divisor riemannZeta (Metric.ball c₀ R) ρ₀ = k)
    (hother : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), ρ ≠ ρ₀ → ρ.re < σ) :
    (-deriv riemannZeta ((σ : ℂ) + (γ : ℂ) * I) / riemannZeta ((σ : ℂ) + (γ : ℂ) * I)).re
      ≤ AL - (k : ℝ) / (σ - β) := by
  -- reindex the Herglotz sum to original coordinates
  rw [herglotz_sum_reindex c₀ ((σ : ℂ) + (γ : ℂ) * I - c₀) hf_mero hf'_mero s_rec hs_dom, hcz] at hbc
  -- recentre the left-hand side to -Re(ζ'/ζ)(σ+γI)
  rw [neg_logDeriv_zeta_recenter_re c₀ ((σ : ℂ) + (γ : ℂ) * I - c₀)
      (by rw [hcz]; exact hdiff), hcz] at hbc
  -- apply the Herglotz lower bound (hzero glue) with f = ζ, m = divisor ζ (ball c₀ R)
  have hkey := hzero_of_blaschke (f := riemannZeta) (s_rec.image (fun u => c₀ + u))
    (fun ρ => divisor riemannZeta (Metric.ball c₀ R) ρ) σ γ β AL k
    (by
      -- match hbc: hzero_of_blaschke wants -(logDeriv ζ (σ+γI)) form; hbc has -deriv ζ/ζ form
      simpa only [logDeriv, Pi.div_apply, neg_div] using hbc)
    hm ρ₀ hρ₀ hρ₀_eq hmρ₀ hother
  -- convert hkey's -(logDeriv ζ) back to -deriv ζ/ζ
  simpa only [logDeriv, Pi.div_apply, neg_div] using hkey

/-- **BC-SUM → `htwo`.**  The recentred Blaschke BC-SUM at height `2γ`, reindexed and recentred, drops
    ALL zeros (`Re Z ≥ 0`) to give the skeleton's `htwo` input `-Re(ζ'/ζ)(σ+2γI) ≤ AL`. -/
theorem htwo_shape_of_bc_sum (c₀ : ℂ) (σ γ AL : ℝ) (R : ℝ)
    (hf_mero : MeromorphicOn riemannZeta (Metric.ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R))
    (s_rec : Finset ℂ)
    (hs_dom : ∀ u ∈ s_rec, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz : c₀ + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
    (hdiff : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
    (hbc : (-(logDeriv (fun w => riemannZeta (c₀ + w))
                ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀))).re
             ≤ AL - (∑ u ∈ s_rec,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) - u)).re)
    (hm : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (hlt : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), ρ.re < σ) :
    (-deriv riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
        / riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)).re ≤ AL := by
  rw [herglotz_sum_reindex c₀ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) hf_mero hf'_mero s_rec hs_dom,
    hcz] at hbc
  rw [neg_logDeriv_zeta_recenter_re c₀ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀)
      (by rw [hcz]; exact hdiff), hcz] at hbc
  have hkey := htwo_of_blaschke (f := riemannZeta) (s_rec.image (fun u => c₀ + u))
    (fun ρ => divisor riemannZeta (Metric.ball c₀ R) ρ) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) AL
    (by simpa only [logDeriv, Pi.div_apply, neg_div] using hbc)
    hm (by
      intro ρ hρ
      have := hlt ρ hρ
      simpa using this)
  simpa only [logDeriv, Pi.div_apply, neg_div] using hkey

/-- **The de la Vallée Poussin region for ζ, from the two Blaschke BC-SUM outputs + the pole bound.**
    Assembles `hzero_shape_of_bc_sum` (height γ), `htwo_shape_of_bc_sum` (height 2γ), and the rung-3
    pole bound `hpole_pf` at the optimal width `σ - 1 = 1/(2B)` into `β ≤ 1 - 1/(112·A·L)`. -/
theorem dlvp_zeta_region_of_bc_sums (c₀ : ℂ) (σ A L β γ : ℝ) (k : ℤ) (R : ℝ)
    (hA : 0 < A) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L)))) (hβσ : β < σ)
    (hf_mero : MeromorphicOn riemannZeta (Metric.ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R))
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    -- height-γ inputs (hzero)
    (s₁ : Finset ℂ) (hs₁_dom : ∀ u ∈ s₁, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz₁ : c₀ + ((σ : ℂ) + (γ : ℂ) * I - c₀) = (σ : ℂ) + (γ : ℂ) * I)
    (hdiff₁ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I))
    (hbc₁ : (-(logDeriv (fun w => riemannZeta (c₀ + w)) ((σ : ℂ) + (γ : ℂ) * I - c₀))).re
             ≤ A * L - (∑ u ∈ s₁,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + (γ : ℂ) * I - c₀) - u)).re)
    (hm₁ : ∀ ρ ∈ s₁.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s₁.image (fun u => c₀ + u)) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I)
    (hmρ₀ : divisor riemannZeta (Metric.ball c₀ R) ρ₀ = k)
    (hother₁ : ∀ ρ ∈ s₁.image (fun u => c₀ + u), ρ ≠ ρ₀ → ρ.re < σ)
    -- height-2γ inputs (htwo)
    (s₂ : Finset ℂ) (hs₂_dom : ∀ u ∈ s₂, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz₂ : c₀ + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
    (hdiff₂ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
    (hbc₂ : (-(logDeriv (fun w => riemannZeta (c₀ + w))
                ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀))).re
             ≤ A * L - (∑ u ∈ s₂,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) - u)).re)
    (hm₂ : ∀ ρ ∈ s₂.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (hlt₂ : ∀ ρ ∈ s₂.image (fun u => c₀ + u), ρ.re < σ) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  have hzero := hzero_shape_of_bc_sum c₀ σ γ β (A * L) k R hf_mero hf'_mero s₁ hs₁_dom hcz₁ hdiff₁
    hbc₁ hm₁ ρ₀ hρ₀ hρ₀_eq hmρ₀ hother₁
  have htwo := htwo_shape_of_bc_sum c₀ σ γ (A * L) R hf_mero hf'_mero s₂ hs₂_dom hcz₂ hdiff₂
    hbc₂ hm₂ hlt₂
  exact dlvp_zeta_region σ A L β γ k hA hL hk hσ_opt hβσ hpole_pf hzero 0 le_rfl (by simpa using htwo)

end ZeroFreeBridge

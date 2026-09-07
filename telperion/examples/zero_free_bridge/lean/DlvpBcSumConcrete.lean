/- PHASE 4 (dVP frontier, corrected assembly — the concrete BC-SUM building block): produce the
   height-γ `hbc₁` that the LOWER-layer region theorem `dlvp_zeta_region_of_bc_sums`
   (`DlvpZetaBcBridge`) consumes, for the ρ₀-enclosing disk `c₀ = 2+iγ`, eval point `σ+iγ`.

   The concrete-instantiation analysis (2026-09-06) found that the top layer
   `dlvp_zeta_region_of_canonical_decomp` is over-constrained (one c₀/disk for BOTH heights, but
   σ+2iγ is ≈|γ| away from c₀=2+iγ).  The correct target is `dlvp_zeta_region_of_bc_sums`, which
   needs the two BC-SUM INEQUALITIES hbc₁ (height γ) and hbc₂ (height 2γ) from appropriately-
   centred disks.  This wrapper produces hbc₁: it discharges the geometric hypotheses of
   `bc_sum_blaschke` (`hz` via `concrete_hz_mem`, `hzne` via `concrete_hzne`) and takes the
   structural/analytic inputs (D, g analyticity, `hg_bound` via `norm_logDeriv_g_le_strip`,
   `hAL` via `zeta_zero_count_strip`→`sum_abs_divisor_eq`→`hAL_arith`) as hypotheses.  Its output
   is EXACTLY the `hbc₁` shape (`.re` of the Herglotz sum, `s₁ = hfin.toFinset`).
   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpBCSumBlaschke
import DlvpZetaConcrete
open Complex MeromorphicOn Metric
namespace ZeroFreeBridge

/-- Concrete height-γ BC-SUM on the disk `c₀ = 2+iγ` at eval `σ+iγ`: discharges hz/hzne via the
    concrete geometry lemmas and calls `bc_sum_blaschke`. Produces the `hbc₁` that
    `dlvp_zeta_region_of_bc_sums` consumes. -/
theorem bc_sum_concrete (σ γ : ℝ) {R : ℝ} (hR : 0 < R) (hσ2 : σ ≤ 2) (hσR : 2 - σ < R)
    (g : ℂ → ℂ)
    (D : CanonicalDecomp (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) g R)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R))
    (hg_ana : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball (0:ℂ) R, g w ≠ 0)
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u))).Finite)
    (heval_ne : riemannZeta (((2:ℂ) + (γ:ℂ)*I)
      + ((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I))) ≠ 0)
    {Bg AL : ℝ}
    (hg_bound : ‖logDeriv g ((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I))‖ ≤ Bg)
    (hAL : (∑ u ∈ hfin.toFinset,
        |(divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u : ℝ)|)
          / (R - ‖(σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I)‖) + Bg ≤ AL) :
    (-(logDeriv (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w))
        ((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I)))).re
      ≤ AL - (∑ u ∈ hfin.toFinset,
          (divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u : ℂ)
            / (((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I)) - u)).re := by
  refine bc_sum_blaschke hR D hf_ana hg_ana hg_ne hfin
    (concrete_hz_mem σ γ R hσ2 hσR) ?_ hg_bound hAL
  intro u hu
  have hune : divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u ≠ 0 := by
    have := hfin.mem_toFinset.mp hu
    simpa [Function.mem_support, neg_ne_zero] using this
  exact concrete_hzne σ γ hf_ana heval_ne hune

end ZeroFreeBridge

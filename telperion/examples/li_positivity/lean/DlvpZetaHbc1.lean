/- PHASE 4 (dVP frontier, item (A) — the height-γ hbc₁ wiring): produce the BC-SUM inequality
   `dlvp_zeta_region_of_bc_sums` consumes at height γ, from the O(L) bounds.

   With every analytic input now an explicit kernel-clean lemma (`hg_bound_gamma` for `Bg`,
   `sum_divisor_recenter_le_jensen` for the count `C`), closing `hbc₁` is composition: this wrapper
   takes `Bg`, `C`, and the region constraint `C/(R-‖z₀‖) + Bg ≤ AL`, derives `hAL` (via
   `sum_abs_divisor_eq` + `divisor ≥ 0` from `hf_ana.divisor_nonneg` + monotonicity in the count),
   and calls `bc_sum_concrete`.  Reusable for BOTH heights (the height-2γ `hbc₂` uses the same shape
   on the parallel disk).  `‖z₀‖ = 2-σ` via `concrete_eval_eq`.  conjecture1_proved = False.
-/
import DlvpBcSumConcrete
import DlvpZetaHAL
import DlvpZetaConcrete
open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **Height-γ `hbc₁` from the O(L) bounds.**  Produces the BC-SUM inequality that
    `dlvp_zeta_region_of_bc_sums` consumes, from the explicit entire-part bound `Bg`, the zero-count
    bound `C`, and the region constraint `C/(R-‖z₀‖) + Bg ≤ AL`.  Derives `hAL` (via
    `sum_abs_divisor_eq` + `divisor ≥ 0` + the count) and calls `bc_sum_concrete`. -/
theorem hbc1_from_bounds (σ γ : ℝ) {R : ℝ} (hR : 0 < R) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hσR : 2 - σ < R)
    (g : ℂ → ℂ)
    (D : CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R))
    (hg_ana : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u))).Finite)
    (heval_ne : riemannZeta (((2 : ℂ) + (γ : ℂ) * I)
      + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))) ≠ 0)
    {Bg AL C : ℝ}
    (hg_bound : ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg)
    (hcount : (∑ u ∈ hfin.toFinset,
        (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ)) ≤ C)
    (hAL_bound : C / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg ≤ AL) :
    (-(logDeriv (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w))
        ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)))).re
      ≤ AL - (∑ u ∈ hfin.toFinset,
          (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℂ)
            / (((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) - u)).re := by
  refine bc_sum_concrete σ γ hR hσ2 hσR g D hf_ana hg_ana hg_ne hfin heval_ne hg_bound ?_
  -- ‖z₀‖ = 2 - σ
  have hznorm : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ = 2 - σ := by
    rw [concrete_eval_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    ring
  have hden : (0 : ℝ) < R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ := by
    rw [hznorm]; linarith
  have hdivnn : ∀ u ∈ hfin.toFinset,
      0 ≤ divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u :=
    fun u _ => hf_ana.divisor_nonneg u
  rw [sum_abs_divisor_eq hfin.toFinset _ hdivnn]
  have hmono : (∑ u ∈ hfin.toFinset,
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖)
      ≤ C / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) := by
    gcongr
  linarith [hAL_bound, hmono]

end ZeroFreeBridge

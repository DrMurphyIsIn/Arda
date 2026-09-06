/- PHASE 4 (dVP frontier, ζ zero-factor bound (2) — ζ INSTANTIATION): the abstract
   `log_norm_prod_diff_le` applied to the actual ζ zero-part finprod.

   Taking the divisor on the INNER disk `closedBall c R₀` makes the two-scale hypotheses free:
     * support ⊆ inner disk  (`DivisorOn.supportWithinDomain`)      → `hin`;
     * `divisor ≥ 0`         (`divisor_nonneg`, ζ has no poles)      → `hm`;
     * `c` not a zero        (`ζ(c) ≠ 0` at `Re c > 1 ⟹ divisor c = 0`) → `hcne`;
     * `z ≠ ρ`               (free from the two-scale separation).

   Result: for the ζ zero-part `P = ∏ᶠ_ρ (·-ρ)^{divisor ζ ρ}`,
     `log‖P c‖ - log‖P z‖ ≤ (Σ_ρ divisor ζ ρ)·(log R₀ - log(R-R₀))`  = AP,
   with `Σ_ρ divisor ζ ρ` the zero count (O(L) via `zeta_zero_count_unconditional`) and the constant
   O(1).  This is the `hPbound` input to `norm_logDeriv_le_of_boundary_split`.  conjecture1_proved = False.
-/
import DlvpZetaDisk
import DlvpBridge
import DlvpLogProd

open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

/-- **ζ zero-factor boundary bound (AP).**  On the outer sphere `sphere c R`, the ζ zero-part
    `P = ∏ᶠ_ρ (·-ρ)^{divisor ζ ρ}` (divisor on the inner disk `closedBall c R₀`, `R₀ ≥ 1`,
    `R₀ < R`, `1 ∉ closedBall c R₀`, `Re c > 1`) satisfies
    `log‖P c‖ - log‖P z‖ ≤ (Σ_ρ divisor ζ ρ)·(log R₀ - log(R-R₀))`. -/
theorem zeta_zero_factor_bound (c : ℂ) (R R₀ : ℝ) (hR0 : 1 ≤ R₀) (hR0R : R₀ < R)
    (h1 : (1 : ℂ) ∉ closedBall c R₀) (hc : 1 < c.re) {z : ℂ} (hz : z ∈ sphere c R) :
    Real.log ‖(∏ᶠ u, (· - u) ^ (divisor riemannZeta (closedBall c R₀) u)) c‖
      - Real.log ‖(∏ᶠ u, (· - u) ^ (divisor riemannZeta (closedBall c R₀) u)) z‖
      ≤ (∑ ρ ∈ ((divisor riemannZeta (closedBall c R₀)).finiteSupport
              (isCompact_closedBall c R₀)).toFinset,
            ((divisor riemannZeta (closedBall c R₀) ρ : ℝ)))
          * (Real.log R₀ - Real.log (R - R₀)) := by
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall c R₀) := zeta_analyticOnNhd_disk c R₀ h1
  have hmero := hana.meromorphicOn
  have hcin : c ∈ closedBall c R₀ := mem_closedBall_self (zero_le_one.trans hR0)
  set D := divisor riemannZeta (closedBall c R₀) with hDdef
  have hfin : (Function.support (D : ℂ → ℤ)).Finite := D.finiteSupport (isCompact_closedBall c R₀)
  -- divisor c = 0, since ζ(c) ≠ 0 (Re c > 1) ⟹ order 0.
  have hDc : D c = 0 := by
    have hord : meromorphicOrderAt riemannZeta c = 0 := by
      have h0 : analyticOrderAt riemannZeta c = 0 :=
        (hana c hcin).analyticOrderAt_eq_zero.mpr (zeta_ne_zero_of_one_lt_re c hc)
      rw [(hana c hcin).meromorphicOrderAt_eq, h0]; simp
    rw [hDdef, divisor_apply hmero hcin, hord]; simp
  -- discharge the abstract hypotheses.
  have hm : ∀ ρ ∈ hfin.toFinset, 0 ≤ D ρ :=
    fun ρ _ => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana ρ
  have hin : ∀ ρ ∈ hfin.toFinset, ρ ∈ closedBall c R₀ := by
    intro ρ hρ
    exact D.supportWithinDomain ((Set.Finite.mem_toFinset hfin).mp hρ)
  have hcne : ∀ ρ ∈ hfin.toFinset, c ≠ ρ := by
    intro ρ hρ hcρ
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hρ
    exact hρ (by rw [← hcρ]; exact hDc)
  -- convert the ζ finprods (at c, z) to Finset products.
  have hFP := finprod_sub_zpow_eq (D : ℂ → ℤ) hfin
  rw [show (∏ᶠ u, (· - u) ^ (D u)) = (fun w => ∏ u ∈ hfin.toFinset, (w - u) ^ (D u)) from hFP]
  exact log_norm_prod_diff_le hR0 hR0R hz hfin.toFinset (D : ℂ → ℤ) hm hin hcne

end ZeroFreeBridge

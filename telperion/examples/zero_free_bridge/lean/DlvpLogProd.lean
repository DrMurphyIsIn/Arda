/- PHASE 4 (dVP frontier, ζ zero-factor bound (2) — LOG-OF-FINPROD wiring): turn the geometric
   `sum_log_norm_ratio_le` into a bound on the actual zero-factor `log‖P‖`.

   `P w = ∏_ρ (w-ρ)^{m_ρ}`, so `log‖P w‖ = Σ_ρ m_ρ · log‖w-ρ‖` (norm-of-product → product-of-norms
   → `log` of a `zpow` product → sum), valid where every `w-ρ ≠ 0`.  Combining this at the centre
   `c` and a sphere point `z` with the two-scale per-zero bound (`DlvpZeroFactor`) yields the
   zero-factor boundary bound at the `Finset`-product level:

     `log‖P c‖ - log‖P z‖ ≤ (Σ_ρ m_ρ) · (log R₀ - log(R-R₀))`   =  AP  =  O(L),

   since `Σ_ρ m_ρ = O(L)` is the zero count (`zeta_zero_count_unconditional`) and the constant is
   `O(1)`.  `z ≠ ρ` is FREE from the two-scale separation (`‖z-ρ‖ ≥ R-R₀ > 0`); `c ≠ ρ` is supplied
   (for ζ, `c` has `Re c = 2` so `ζ(c) ≠ 0` and `c` is not a zero).  Function-agnostic in the point
   set.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZeroFactor

open Complex Metric

namespace ZeroFreeBridge

/-- **Log of the zero-factor.**  `log‖∏_ρ (w-ρ)^{m ρ}‖ = Σ_ρ m ρ · log‖w-ρ‖`, given `w ≠ ρ`
    for every `ρ` in the (finite) support. -/
theorem log_norm_prod_sub_zpow {s : Finset ℂ} (m : ℂ → ℤ) (w : ℂ)
    (hw : ∀ ρ ∈ s, w ≠ ρ) :
    Real.log ‖∏ ρ ∈ s, (w - ρ) ^ (m ρ)‖ = ∑ ρ ∈ s, (m ρ : ℝ) * Real.log ‖w - ρ‖ := by
  have hne : ∀ ρ ∈ s, ‖(w - ρ) ^ (m ρ)‖ ≠ 0 := by
    intro ρ hρ
    rw [norm_zpow]
    exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hw ρ hρ)))
  rw [norm_prod, Real.log_prod hne]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [norm_zpow, Real.log_zpow]

/-- **Zero-factor bound (2), assembled at the `Finset`-product level.**  For `P w = ∏_ρ (w-ρ)^{m ρ}`
    with nonnegative multiplicities and zeros in the inner disk `closedBall c R₀` (`R₀ ≥ 1`),
    evaluated at a point `z` on the outer sphere `sphere c R` (`R₀ < R`, `c` not a zero):
    `log‖P c‖ - log‖P z‖ ≤ (Σ_ρ m ρ)·(log R₀ - log(R-R₀))`. -/
theorem log_norm_prod_diff_le {c z : ℂ} {R R₀ : ℝ} (hR0 : 1 ≤ R₀) (hR0R : R₀ < R)
    (hz : z ∈ sphere c R) (s : Finset ℂ) (m : ℂ → ℤ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hin : ∀ ρ ∈ s, ρ ∈ closedBall c R₀)
    (hcne : ∀ ρ ∈ s, c ≠ ρ) :
    Real.log ‖∏ ρ ∈ s, (c - ρ) ^ (m ρ)‖ - Real.log ‖∏ ρ ∈ s, (z - ρ) ^ (m ρ)‖
      ≤ (∑ ρ ∈ s, (m ρ : ℝ)) * (Real.log R₀ - Real.log (R - R₀)) := by
  -- `z ≠ ρ` is free: the two-scale separation gives `‖z-ρ‖ ≥ R-R₀ > 0`.
  have hzne : ∀ ρ ∈ s, z ≠ ρ := by
    intro ρ hρ heq
    have hsep : R - R₀ ≤ ‖z - ρ‖ := norm_sub_ge_of_inner_outer hz (hin ρ hρ)
    rw [heq, sub_self, norm_zero] at hsep
    linarith
  rw [log_norm_prod_sub_zpow m c hcne, log_norm_prod_sub_zpow m z hzne, ← Finset.sum_sub_distrib]
  have hstep : ∑ ρ ∈ s, ((m ρ : ℝ) * Real.log ‖c - ρ‖ - (m ρ : ℝ) * Real.log ‖z - ρ‖)
      = ∑ ρ ∈ s, (m ρ : ℝ) * (Real.log ‖c - ρ‖ - Real.log ‖z - ρ‖) :=
    Finset.sum_congr rfl (fun ρ _ => by ring)
  rw [hstep]
  exact sum_log_norm_ratio_le hR0 hR0R hz s (fun ρ => (m ρ : ℝ))
    (fun ρ hρ => by exact_mod_cast hm ρ hρ) hin

end ZeroFreeBridge

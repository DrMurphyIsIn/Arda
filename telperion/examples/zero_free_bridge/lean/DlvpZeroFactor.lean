/- PHASE 4 (dVP frontier, ζ boundary growth — ZERO-FACTOR bound (2), crux): the two-scale
   geometric separation and the per-zero log bound.

   The zero-factor is `P z = ∏_ρ (z-ρ)^{m_ρ}`, so `log‖P c‖ - log‖P z‖ = Σ_ρ m_ρ (log‖c-ρ‖ -
   log‖z-ρ‖)`.  The classical dVP two-scale trick: factor only zeros in an INNER disk
   `closedBall c R₀` and evaluate `P` on the OUTER sphere `sphere c R` (`R₀ < R`).  Then every
   factored zero is bounded AWAY from the sphere — `‖z-ρ‖ ≥ R-R₀ > 0` — so the per-zero log ratio
   is bounded by an absolute constant, and the sum is (that constant) × (#zeros) = O(L).

   This file supplies the enabling geometry:
     * `norm_sub_ge_of_inner_outer` — the separation `R - R₀ ≤ ‖z - ρ‖`;
     * `log_norm_ratio_le_of_two_scale` — per-zero `log‖c-ρ‖ - log‖z-ρ‖ ≤ log R₀ - log(R-R₀)`.

   Summing over the zero support (× multiplicity, count = O(L) via `zeta_zero_count_unconditional`)
   then feeds `Aζ + AP` into `norm_logDeriv_le_of_boundary_split`.  Function-agnostic in the point
   set.  conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

open Complex Metric

namespace ZeroFreeBridge

/-- **Two-scale separation.**  A point `ρ` in the inner disk `closedBall c R₀` and a point `z` on
    the outer sphere `sphere c R` are separated: `R - R₀ ≤ ‖z - ρ‖`. -/
theorem norm_sub_ge_of_inner_outer {c z ρ : ℂ} {R R₀ : ℝ}
    (hz : z ∈ sphere c R) (hρ : ρ ∈ closedBall c R₀) : R - R₀ ≤ ‖z - ρ‖ := by
  rw [mem_sphere_iff_norm] at hz
  rw [mem_closedBall_iff_norm] at hρ
  calc R - R₀ ≤ ‖z - c‖ - ‖ρ - c‖ := by rw [hz]; linarith
    _ ≤ ‖(z - c) - (ρ - c)‖ := norm_sub_norm_le _ _
    _ = ‖z - ρ‖ := by rw [sub_sub_sub_cancel_right]

/-- **Per-zero log bound.**  For `ρ` in the inner disk (radius `R₀ ≥ 1`) and `z` on the outer
    sphere (radius `R > R₀`), `log‖c-ρ‖ - log‖z-ρ‖ ≤ log R₀ - log(R - R₀)` — an absolute constant
    independent of the zero `ρ`.  (`R₀ ≥ 1` keeps `log R₀ ≥ 0`, absorbing the `ρ = c` edge case
    where `‖c-ρ‖ = 0`.) -/
theorem log_norm_ratio_le_of_two_scale {c z ρ : ℂ} {R R₀ : ℝ}
    (hR0 : 1 ≤ R₀) (hR0R : R₀ < R)
    (hz : z ∈ sphere c R) (hρ : ρ ∈ closedBall c R₀) :
    Real.log ‖c - ρ‖ - Real.log ‖z - ρ‖ ≤ Real.log R₀ - Real.log (R - R₀) := by
  have hRR0 : (0 : ℝ) < R - R₀ := by linarith
  have hcρ : ‖c - ρ‖ ≤ R₀ := by
    rw [mem_closedBall_iff_norm] at hρ
    rw [norm_sub_rev]; exact hρ
  have hzρ : R - R₀ ≤ ‖z - ρ‖ := norm_sub_ge_of_inner_outer hz hρ
  have hlog1 : Real.log ‖c - ρ‖ ≤ Real.log R₀ := by
    rcases eq_or_lt_of_le (norm_nonneg (c - ρ)) with h0 | hpos
    · rw [← h0, Real.log_zero]; exact Real.log_nonneg hR0
    · exact Real.log_le_log hpos hcρ
  have hlog2 : Real.log (R - R₀) ≤ Real.log ‖z - ρ‖ := Real.log_le_log hRR0 hzρ
  linarith

/-- **Zero-factor bound (2), summed.**  For a finite set of inner-disk zeros with nonnegative
    multiplicities `m`, the total log-ratio is bounded by the total multiplicity times the per-zero
    constant: `Σ_ρ m ρ · (log‖c-ρ‖ - log‖z-ρ‖) ≤ (Σ_ρ m ρ) · (log R₀ - log(R-R₀))`.  Since
    `Σ_ρ m ρ = O(L)` (the zero count) and the constant is `O(1)`, the sum is `O(L)` — this is
    `AP` for `norm_logDeriv_le_of_boundary_split` once `log‖P‖ = Σ_ρ m ρ · log‖·-ρ‖` is wired in. -/
theorem sum_log_norm_ratio_le {c z : ℂ} {R R₀ : ℝ} (hR0 : 1 ≤ R₀) (hR0R : R₀ < R)
    (hz : z ∈ sphere c R) (s : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ ρ ∈ s, 0 ≤ m ρ)
    (hin : ∀ ρ ∈ s, ρ ∈ closedBall c R₀) :
    ∑ ρ ∈ s, m ρ * (Real.log ‖c - ρ‖ - Real.log ‖z - ρ‖)
      ≤ (∑ ρ ∈ s, m ρ) * (Real.log R₀ - Real.log (R - R₀)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun ρ hρ => ?_)
  exact mul_le_mul_of_nonneg_left
    (log_norm_ratio_le_of_two_scale hR0 hR0R hz (hin ρ hρ)) (hm ρ hρ)

end ZeroFreeBridge

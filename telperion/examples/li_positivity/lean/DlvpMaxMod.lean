/- PHASE 4 (dVP frontier, obligation (i-b') → SPHERE): reduce the entire-part bound to a bound on
   `log‖g‖` on the BOUNDARY sphere, via the maximum-modulus principle.

   `DlvpEntireBound.norm_logDeriv_le_of_log_norm_le` needs `log‖g z‖ - log‖g c‖ ≤ M'` throughout the
   OPEN disk.  But `log‖g‖ = Re(log g)` is harmonic, so its sup over the disk is attained on the
   boundary: `‖g‖ ≤ sup_{sphere}‖g‖` on the whole closed disk (`Complex.norm_le_of_forall_mem_frontier
   _norm_le`, max modulus for `g`).  Hence a bound on `log‖g‖` on the SPHERE propagates to the disk.

   This isolates the sole ζ-specific input as a SPHERE bound — exactly where `zeta_sphere_bound`
   (already proved) lives: `‖ζ z‖` bounded uniformly on spheres ⟹ `log‖ζ‖ = O(L)`.  Feeding
   `M' = A·L` gives `‖E‖ = O(L)`.  Function-agnostic max-modulus atom + ζ-ready composition.
   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpEntireBound

open Complex Metric

namespace ZeroFreeBridge

/-- **Maximum-modulus reduction.**  If `g` is holomorphic on `ball c R` and continuous up to the
    boundary (`DiffContOnCl`), then a uniform bound `‖g‖ ≤ B` on the sphere `sphere c R` propagates
    to the whole open disk. -/
theorem norm_le_on_ball_of_sphere {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : R ≠ 0)
    (hd : DiffContOnCl ℂ f (ball c R)) (hB : ∀ z ∈ sphere c R, ‖f z‖ ≤ B) :
    ∀ z ∈ ball c R, ‖f z‖ ≤ B := by
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_
    (subset_closure hz)
  rw [frontier_ball c hR]
  exact hB

/-- **(i-b') via a sphere bound.**  For `g` holomorphic (up to the boundary) and zero-free on
    `ball c R`, a bound on the boundary oscillation of `log‖g‖`, `log‖g z‖ - log‖g c‖ ≤ M'`
    (`M' > 0`) for all `z ∈ sphere c R`, controls the entire part at the centre:
    `‖logDeriv g c‖ ≤ 2 M'/(R - r)` for any `0 < r < R`.  (The bound propagates from the sphere to
    the disk by maximum modulus.) -/
theorem norm_logDeriv_le_of_sphere_log_norm_le {g : ℂ → ℂ} {c : ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM' : 0 < M')
    (hd : DiffContOnCl ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hsphere : ∀ z ∈ sphere c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g c‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  set B : ℝ := Real.exp (M' + Real.log ‖g c‖) with hB_def
  -- sphere bound on ‖g‖ from the log bound.
  have hgz_le : ∀ z ∈ sphere c R, ‖g z‖ ≤ B := by
    intro z hz
    rcases eq_or_lt_of_le (norm_nonneg (g z)) with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · calc ‖g z‖ = Real.exp (Real.log ‖g z‖) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (M' + Real.log ‖g c‖) := Real.exp_le_exp.mpr (by linarith [hsphere z hz])
        _ = B := rfl
  -- propagate to the disk by maximum modulus.
  have hball_le : ∀ z ∈ ball c R, ‖g z‖ ≤ B := norm_le_on_ball_of_sphere hR.ne' hd hgz_le
  -- back to a log bound on the disk.
  have hlog : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M' := by
    intro z hz
    have hgz_pos : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z hz)
    have hle : Real.log ‖g z‖ ≤ Real.log B := Real.log_le_log hgz_pos (hball_le z hz)
    rw [hB_def, Real.log_exp] at hle
    linarith
  exact norm_logDeriv_le_of_log_norm_le hr hrR hM' hd.differentiableOn hne hlog

end ZeroFreeBridge

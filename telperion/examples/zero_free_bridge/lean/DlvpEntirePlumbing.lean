/- PHASE 4 (dVP frontier, entire-part PLUMBING): the two mechanical lemmas that connect the
   interior-point bound (`DlvpBCDerivInterior`) to the Blaschke BC-SUM (`bc_sum_blaschke`).

   (a) `norm_logDeriv_le_of_sphere_log_norm_le_interior` — the interior entire-part bound driven by a
       SPHERE oscillation bound (not the whole ball): `log‖g‖ = Re(log g)` is harmonic, so a boundary
       bound propagates to the disk by maximum modulus (`DlvpMaxMod.norm_le_on_ball_of_sphere`, via
       `exp`), and the resulting ball bound feeds `norm_logDeriv_le_of_log_norm_le_interior`.  This is
       exactly the shape available for ζ's Blaschke `g`, whose boundary `log‖g‖` equals `log‖ζ‖`
       (Blaschke factors have modulus 1 on the sphere).

   (b) `logDeriv_comp_const_add` — the RECENTRING: `bc_sum_blaschke` lives on `ball 0 R`, so ζ enters as
       `f(w) = ζ(c + w)`; its log-derivative is ζ's, shifted: `logDeriv (fun w => ζ(c+w)) z =
       logDeriv ζ (c+z)` (chain rule, `deriv (c+·) = 1`).

   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpMaxMod
import DlvpBCDerivInterior

open Complex Metric

namespace ZeroFreeBridge

/-- **(a) Interior entire-part bound from a SPHERE oscillation bound.**  For `g` holomorphic (up to the
    boundary) and zero-free on `ball c R`, a boundary bound `log‖g z‖ - log‖g c‖ ≤ M'` on `sphere c R`
    controls the log-derivative at any interior point `z₀`: `‖logDeriv g z₀‖ ≤ 4M'(R+ρ)/(R-ρ)²`,
    `ρ = ‖z₀-c‖`.  (Boundary bound → disk bound by maximum modulus → interior Cauchy.) -/
theorem norm_logDeriv_le_of_sphere_log_norm_le_interior {g : ℂ → ℂ} {c z₀ : ℂ} {R M' : ℝ}
    (hM' : 0 < M') (hρ : ‖z₀ - c‖ < R)
    (hd : DiffContOnCl ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hsphere : ∀ z ∈ sphere c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g z₀‖ ≤ 4 * M' * (R + ‖z₀ - c‖) / (R - ‖z₀ - c‖) ^ 2 := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hρ
  -- boundary bound on ‖g‖ from the log bound, then maximum modulus to the disk, then back to log
  set B : ℝ := Real.exp (M' + Real.log ‖g c‖) with hB_def
  have hgz_le : ∀ z ∈ sphere c R, ‖g z‖ ≤ B := by
    intro z hz
    rcases eq_or_lt_of_le (norm_nonneg (g z)) with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · calc ‖g z‖ = Real.exp (Real.log ‖g z‖) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (M' + Real.log ‖g c‖) := Real.exp_le_exp.mpr (by linarith [hsphere z hz])
        _ = B := rfl
  have hball_le : ∀ z ∈ ball c R, ‖g z‖ ≤ B := norm_le_on_ball_of_sphere hR.ne' hd hgz_le
  have hlog : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M' := by
    intro z hz
    have hgz_pos : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z hz)
    have hle : Real.log ‖g z‖ ≤ Real.log B := Real.log_le_log hgz_pos (hball_le z hz)
    rw [hB_def, Real.log_exp] at hle
    linarith
  exact norm_logDeriv_le_of_log_norm_le_interior hM' hρ hd.differentiableOn hne hlog

/-- **(b) Recentring the log-derivative.**  `logDeriv (fun w => f (c + w)) z = logDeriv f (c + z)`
    (chain rule; `deriv (c + ·) = 1`).  Sends ζ's log-derivative into `bc_sum_blaschke`'s `ball 0 R`
    coordinates. -/
theorem logDeriv_comp_const_add (f : ℂ → ℂ) (c z : ℂ) (hf : DifferentiableAt ℂ f (c + z)) :
    logDeriv (fun w => f (c + w)) z = logDeriv f (c + z) := by
  have hg : DifferentiableAt ℂ (fun w => c + w) z := by fun_prop
  have := logDeriv_comp hf hg
  simp only [Function.comp_def] at this
  rw [this]
  simp

end ZeroFreeBridge

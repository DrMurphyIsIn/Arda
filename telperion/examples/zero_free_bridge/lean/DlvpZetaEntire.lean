/- PHASE 4 (dVP frontier, the entire-part bound for ζ's Blaschke g — item 2): produce `hg_bound`,
   `‖logDeriv g z₀‖ ≤ Bg`, for the CanonicalDecomp quotient `g` of the recentred ζ.

   The Blaschke factors have modulus 1 on the sphere (`canonicalDecomp_norm_eq_on_sphere`: `‖f z‖ = ‖g z‖`
   on `sphere 0 R`, `f = ζ(c₀+·)`), so the boundary oscillation of `log‖g‖` equals that of `log‖ζ‖`,
   bounded by `zeta_sphere_log_bound` (`Aζ = log U - log(2-π²/6) = O(L)`) — PROVIDED the centre value is
   controlled: `log‖g 0‖ ≥ log‖ζ c₀‖` (i.e. `‖B 0‖ ≤ 1`, the Blaschke-centre relation, taken here as the
   single hypothesis `hfg0`).  Feeding this sphere oscillation into the interior entire-part bound
   `norm_logDeriv_le_of_sphere_log_norm_le_interior` gives `hg_bound`.

   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpCanonicalNorm
import DlvpZetaSphereLog
import DlvpEntirePlumbing

open Complex Metric

namespace ZeroFreeBridge

/-- **Boundary oscillation of `log‖g‖` for the recentred-ζ Blaschke quotient.**  On `sphere 0 R`,
    `log‖g z‖ - log‖g 0‖ ≤ Aζ` with `Aζ = log U - log(2-π²/6)` the ζ oscillation, given the Blaschke-
    centre relation `‖ζ c₀‖ ≤ ‖g 0‖`. -/
theorem g_sphere_log_osc {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hcR : R + 1 < c₀.re)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont : ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R))
    (hg_cont : ContinuousOn g (sphere 0 R))
    (hfg0 : ‖riemannZeta c₀‖ ≤ ‖g 0‖) :
    ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖g z‖ - Real.log ‖g 0‖
      ≤ Real.log ((‖c₀‖ + R) / (c₀.re - R - 1) + (‖c₀‖ + R) / (c₀.re - R))
          - Real.log (2 - Real.pi ^ 2 / 6) := by
  intro z hz
  -- ‖g z‖ = ‖ζ(c₀+z)‖ on the sphere (Blaschke modulus 1)
  have hgf : ‖g z‖ = ‖riemannZeta (c₀ + z)‖ :=
    (canonicalDecomp_norm_eq_on_sphere hR D hf_cont hg_cont hz).symm
  -- c₀ + z lies on sphere c₀ R
  have hzc₀ : c₀ + z ∈ sphere c₀ R := by
    rw [mem_sphere_iff_norm, add_sub_cancel_left]
    rwa [mem_sphere_iff_norm, sub_zero] at hz
  -- ζ sphere log bound at centre c₀
  have hζ := zeta_sphere_log_bound c₀ R hR hcR hc2 hzc₀
  -- centre control: log‖ζ c₀‖ ≤ log‖g 0‖
  have hζc₀pos : (0 : ℝ) < ‖riemannZeta c₀‖ := by
    have : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta c₀‖ := zeta_norm_ge_two_sub hc2
    linarith [two_sub_pi_sq_div_six_pos]
  have hlogc₀ : Real.log ‖riemannZeta c₀‖ ≤ Real.log ‖g 0‖ := Real.log_le_log hζc₀pos hfg0
  rw [hgf]
  linarith

/-- **`hg_bound` for the recentred-ζ Blaschke quotient.**  The interior entire-part bound driven by the
    `g` sphere oscillation: `‖logDeriv g z₀‖ ≤ 4 Aζ (R+‖z₀‖)/(R-‖z₀‖)²`, `Aζ = log U - log(2-π²/6) =
    O(L)`.  Given the Blaschke-centre relation `‖ζ c₀‖ ≤ ‖g 0‖`. -/
theorem norm_logDeriv_g_le {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hcR : R + 1 < c₀.re)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont : ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R))
    (hg_cont : ContinuousOn g (sphere 0 R))
    (hg_dcc : DiffContOnCl ℂ g (ball 0 R)) (hg_ne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0)
    (hfg0 : ‖riemannZeta c₀‖ ≤ ‖g 0‖) {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * (Real.log ((‖c₀‖ + R) / (c₀.re - R - 1) + (‖c₀‖ + R) / (c₀.re - R))
              - Real.log (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by
  have hd1 : 0 < c₀.re - R - 1 := by linarith
  have hd2 : 0 < c₀.re - R := by linarith
  have hcre : c₀.re ≤ ‖c₀‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm c₀)
  have hU1 : (1 : ℝ) ≤ (‖c₀‖ + R) / (c₀.re - R - 1) + (‖c₀‖ + R) / (c₀.re - R) := by
    have ht1 : (0 : ℝ) ≤ (‖c₀‖ + R) / (c₀.re - R - 1) := by positivity
    have ht2 : (1 : ℝ) ≤ (‖c₀‖ + R) / (c₀.re - R) := by
      rw [le_div_iff₀ hd2]; nlinarith [norm_nonneg c₀]
    linarith
  have hAζpos : 0 < Real.log ((‖c₀‖ + R) / (c₀.re - R - 1) + (‖c₀‖ + R) / (c₀.re - R))
      - Real.log (2 - Real.pi ^ 2 / 6) := by
    have h1 : 0 ≤ Real.log ((‖c₀‖ + R) / (c₀.re - R - 1) + (‖c₀‖ + R) / (c₀.re - R)) :=
      Real.log_nonneg hU1
    have h2 : Real.log (2 - Real.pi ^ 2 / 6) < 0 :=
      Real.log_neg two_sub_pi_sq_div_six_pos (by nlinarith [Real.pi_gt_three])
    linarith
  have hρ : ‖z₀ - 0‖ < R := by rwa [sub_zero]
  exact norm_logDeriv_le_of_sphere_log_norm_le_interior hAζpos hρ hg_dcc hg_ne
    (g_sphere_log_osc hR hc2 hcR D hf_cont hg_cont hfg0)

end ZeroFreeBridge

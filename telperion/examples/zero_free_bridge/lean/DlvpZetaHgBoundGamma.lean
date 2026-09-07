/- PHASE 4 (dVP frontier, item (A) — the explicit height-γ entire-part bound `hg_bound₁`): combine
   `norm_logDeriv_g_le_wired` (item 1, the fully-wired O(L) entire-part bound) with
   `Azeta_le_of_c0_2_gamma` (item 2ii, `Aζ'' ≤ log((2|γ|+11)/(2-π²/6))`) into the explicit `Bg` that
   `bc_sum_concrete` consumes for the concrete centre `c₀ = 2+iγ`.  This is the last analytic
   assembling step for the height-γ half; discharging `hc2/hRlt/himc` at `c₀=2+iγ` (via `simp` on
   `re`/`im`) and monotonicity (`gcongr`) in the oscillation constant.  conjecture1_proved = False.
-/
import DlvpZetaGBound
import DlvpZetaAzeta
open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **Explicit O(log|γ|) entire-part bound for c₀ = 2+iγ.**  Combines `norm_logDeriv_g_le_wired`
    (item 1) with `Azeta_le_of_c0_2_gamma` (item 2): the `Bg` that `bc_sum_concrete` consumes,
    with the sphere-oscillation constant replaced by its explicit `log((2|γ|+11)/(2-π²/6))` bound. -/
theorem hg_bound_gamma {γ R : ℝ} {g : ℂ → ℂ} (hR : 0 < R) (hR2 : R < 3/2) (hγ : R + 2 ≤ |γ|)
    (D : CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by
  have hc2 : (2 : ℝ) ≤ ((2 : ℂ) + (γ : ℂ) * I).re := by simp
  have hRlt : R < ((2 : ℂ) + (γ : ℂ) * I).re - 1 / 2 := by simp; linarith
  have himc : R + 2 ≤ |((2 : ℂ) + (γ : ℂ) * I).im| := by simp; exact hγ
  have hw := norm_logDeriv_g_le_wired hR hc2 hRlt himc D hz₀
  refine hw.trans ?_
  have hρ : ‖z₀ - 0‖ < R := by rwa [sub_zero]
  have hRz : (0:ℝ) < R - ‖z₀ - 0‖ := sub_pos.mpr hρ
  gcongr
  exact Azeta_le_of_c0_2_gamma γ R hR hR2 hγ

end ZeroFreeBridge

/- PHASE 4 (dVP frontier, item 2(ii) — Bg = O(L) via Aζ'' = O(log|γ|)): the sphere-oscillation
   constant `Aζ''` for the concrete centre `c₀ = 2+iγ` is O(log|γ|), so the entire-part bound
   `Bg = 4·Aζ''·(R+‖z₀‖)/(R-‖z₀‖)²` (`norm_logDeriv_g_le_wired`) is O(L), `L = log|γ|` — the second
   O(L) input `hAL_concrete` consumes (`hBg`).

   Crux: `U'' = (‖c₀‖+R)/(|γ|-R) + (‖c₀‖+R)/(2-R) = O(|γ|)` (the 2nd term (‖c₀‖+R)/(2-R) dominates,
   since c₀.re=2 and R<3/2 ⟹ 2-R>1/2).  `U_le_of_c0_2_gamma`: `U'' ≤ 2|γ|+11` (‖c₀‖≤2+|γ| via
   `norm_add_le`; first term ≤ 7/2, second ≤ 2|γ|+15/2, by `div_le_iff₀` + `nlinarith`).
   `Azeta_le_of_c0_2_gamma`: `Aζ'' = log U'' - log(2-π²/6) ≤ log((2|γ|+11)/(2-π²/6))` (log monotone
   on the U'' bound + `Real.log_div`).  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaLower
open Complex

namespace ZeroFreeBridge

/-- U'' = O(|γ|) for c₀ = 2+iγ: the sphere-oscillation numerator obeys the clean rational bound
    `U'' ≤ 2|γ| + 11` when `R < 3/2` and `|γ| ≥ R+2`. (Second term (‖c₀‖+R)/(2-R) dominates.) -/
theorem U_le_of_c0_2_gamma (γ R : ℝ) (hR : 0 < R) (hR2 : R < 3/2) (hγ : R + 2 ≤ |γ|) :
    (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
      + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R)
      ≤ 2 * |γ| + 11 := by
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : |((2 : ℂ) + (γ : ℂ) * I).im| = |γ| := by simp
  have hnorm : ‖(2 : ℂ) + (γ : ℂ) * I‖ ≤ 2 + |γ| := by
    calc ‖(2 : ℂ) + (γ : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(γ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |γ| := by
          rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            show ‖(2 : ℂ)‖ = 2 by simp]
  rw [hc0re, hc0im]
  have hd1 : (0 : ℝ) < |γ| - R := by linarith
  have hd2 : (0 : ℝ) < 2 - R := by linarith
  have hnn : (0 : ℝ) ≤ ‖(2 : ℂ) + (γ : ℂ) * I‖ := norm_nonneg _
  -- first term ≤ 7/2
  have hfirst : (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|γ| - R) ≤ 7 / 2 := by
    rw [div_le_iff₀ hd1]; nlinarith [hnorm, hγ, hR2]
  -- second term ≤ 2|γ| + 15/2
  have hsecond : (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (2 - R) ≤ 2 * |γ| + 15 / 2 := by
    rw [div_le_iff₀ hd2]; nlinarith [hnorm, hR2, abs_nonneg γ]
  linarith [hfirst, hsecond]

/-- **Aζ'' = O(log|γ|) for c₀ = 2+iγ.**  The sphere-oscillation constant obeys the explicit bound
    `Aζ'' ≤ log((2|γ|+11)/(2-π²/6))`, giving the `Bg = O(L)` (`L = log|γ|`) input for `hAL_concrete`. -/
theorem Azeta_le_of_c0_2_gamma (γ R : ℝ) (hR : 0 < R) (hR2 : R < 3/2) (hγ : R + 2 ≤ |γ|) :
    Real.log ((‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
        + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R))
      - Real.log (2 - Real.pi ^ 2 / 6)
      ≤ Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : |((2 : ℂ) + (γ : ℂ) * I).im| = |γ| := by simp
  have hd1 : (0 : ℝ) < |γ| - R := by linarith
  have hd2 : (0 : ℝ) < 2 - R := by linarith
  have hnn : (0 : ℝ) ≤ ‖(2 : ℂ) + (γ : ℂ) * I‖ := norm_nonneg _
  -- U'' > 0
  have hUpos : (0 : ℝ) < (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
      + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R) := by
    rw [hc0re, hc0im]
    have h1 : (0 : ℝ) < (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|γ| - R) := by positivity
    have h2 : (0 : ℝ) < (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (2 - R) := by positivity
    linarith
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hlogU : Real.log ((‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
        + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R))
      ≤ Real.log (2 * |γ| + 11) :=
    Real.log_le_log hUpos (U_le_of_c0_2_gamma γ R hR hR2 hγ)
  rw [Real.log_div (by positivity) (ne_of_gt hpi)]
  linarith [hlogU]

end ZeroFreeBridge

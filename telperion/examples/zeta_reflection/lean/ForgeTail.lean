/-  ForgeTail.lean -- ANDÚRIL cert-forge STAGE 2: the EM order-3 tail number at N = 50, t ∈ {14,15}.

    `em_zeta_critical_line3_number` (EMZetaTail) proves the tail ≤ 1/1000 at t=14, N=200.  The forge
    uses N = 50 (49-term Dirichlet sum, 4× fewer trig certs), whose tail is still comfortably small
    (≤ ~1.1e-3 < the 2e-2 ζ-box budget).  This file discharges the envelope numeric bound at N=50 for
    BOTH grid heights, via the parametric `em_zeta_critical_line3_enclosure` -- the same pattern as
    `em_tail3_envelope_le`, with the factor-norm bound 15 (t=14) / 16 (t=15) and `50^{-5/2} ≤ 1/17677`.

    conjecture1_proved = False.
-/
import EMZetaTail

open Complex ZetaReflection

namespace ForgeTail

/-- `‖(a:ℂ)+b·I‖ ≤ R` whenever `a² + b² ≤ R²`, `0 ≤ R`. -/
private theorem norm_le {a b R : ℝ} (hR : 0 ≤ R) (hab : a ^ 2 + b ^ 2 ≤ R ^ 2) :
    ‖(a : ℂ) + b * Complex.I‖ ≤ R := by
  rw [Complex.norm_add_mul_I,
    show R = Real.sqrt (R ^ 2) by rw [Real.sqrt_sq hR]]
  exact Real.sqrt_le_sqrt hab

/-- `50^{-5/2} ≤ 1/17675` (`√50 ≥ 7.07`, `50²·√50 = 2500·√50 ≥ 2500·7.07 = 17675`). -/
private theorem pow50_le : (50 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 / 17675 := by
  have hsqrt : (7.07 : ℝ) ≤ (50 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow,
      show (7.07 : ℝ) = Real.sqrt (7.07 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  rw [Real.rpow_neg (by norm_num), show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num), Real.rpow_two]
  have hden_ge : (17675 : ℝ) ≤ (50 : ℝ) ^ 2 * (50 : ℝ) ^ (1 / 2 : ℝ) := by
    calc (17675 : ℝ) = 2500 * 7.07 := by norm_num
      _ ≤ (50 : ℝ) ^ 2 * (50 : ℝ) ^ (1 / 2 : ℝ) := by gcongr <;> norm_num
  calc ((50 : ℝ) ^ 2 * (50 : ℝ) ^ (1 / 2 : ℝ))⁻¹
      ≤ (17675 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hden_ge
    _ = 1 / 17675 := by rw [one_div]

/-- The ζ box number at `t = 14`, `N = 50`: `‖ζ(1/2+14i) − emZetaFinite3 (1/2+14i) 50‖ ≤ 1/1000`. -/
theorem zeta_tail_t14 :
    ‖riemannZeta ((1 / 2 : ℂ) + 14 * Complex.I)
        - emZetaFinite3 ((1 / 2 : ℂ) + 14 * Complex.I) 50‖ ≤ (13 : ℝ) / 10000 := by
  have henc := em_zeta_critical_line3_enclosure 14 (N := 50) (by norm_num)
  refine le_trans henc ?_
  have hexpeq : (-(1 / 2 + (3 : ℝ) - 1) : ℝ) = -(5 / 2 : ℝ) := by norm_num
  have hdeneq : ((1 / 2 : ℝ) + 3 - 1) = (5 / 2 : ℝ) := by norm_num
  rw [hexpeq, hdeneq]
  have hn0 : ‖((1 / 2 : ℂ) + 14 * Complex.I)‖ ≤ 15 := by
    rw [show ((1 / 2 : ℂ) + 14 * Complex.I) = ((1/2 : ℝ) : ℂ) + (14 : ℝ) * Complex.I by push_cast; ring]
    exact norm_le (by norm_num) (by norm_num)
  have hn1 : ‖((1 / 2 : ℂ) + 14 * Complex.I + 1)‖ ≤ 15 := by
    rw [show ((1 / 2 : ℂ) + 14 * Complex.I + 1) = ((3/2 : ℝ) : ℂ) + (14 : ℝ) * Complex.I by push_cast; ring]
    exact norm_le (by norm_num) (by norm_num)
  have hn2 : ‖((1 / 2 : ℂ) + 14 * Complex.I + 2)‖ ≤ 15 := by
    rw [show ((1 / 2 : ℂ) + 14 * Complex.I + 2) = ((5/2 : ℝ) : ℂ) + (14 : ℝ) * Complex.I by push_cast; ring]
    exact norm_le (by norm_num) (by norm_num)
  have hnorm : ‖((1 / 2 : ℂ) + 14 * Complex.I) * ((1 / 2 : ℂ) + 14 * Complex.I + 1)
        * ((1 / 2 : ℂ) + 14 * Complex.I + 2)‖ ≤ 3375 := by
    calc ‖_ * _ * _‖ = ‖((1 / 2 : ℂ) + 14 * Complex.I)‖ * ‖((1 / 2 : ℂ) + 14 * Complex.I + 1)‖
            * ‖((1 / 2 : ℂ) + 14 * Complex.I + 2)‖ := by rw [norm_mul, norm_mul]
      _ ≤ 15 * 15 * 15 := by gcongr
      _ = 3375 := by norm_num
  have hpownn : (0 : ℝ) ≤ (50 : ℝ) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc (1 / 12) * ‖_ * _ * _‖ * (50 : ℝ) ^ (-(5 / 2 : ℝ)) / (5 / 2) / 6
      ≤ (1 / 12) * 3375 * (1 / 17675) / (5 / 2) / 6 := by
        gcongr
        · exact hnorm
        · exact pow50_le
    _ ≤ 13 / 10000 := by norm_num

/-- The ζ box number at `t = 15`, `N = 50`: `‖ζ(1/2+15i) − emZetaFinite3 (1/2+15i) 50‖ ≤ 1/1000`.
    Factor-norm bound 16 (a²+b² for `s+2` is 231.25 > 225), giving `16³ = 4096`. -/
theorem zeta_tail_t15 :
    ‖riemannZeta ((1 / 2 : ℂ) + 15 * Complex.I)
        - emZetaFinite3 ((1 / 2 : ℂ) + 15 * Complex.I) 50‖ ≤ (15 : ℝ) / 10000 := by
  have henc := em_zeta_critical_line3_enclosure 15 (N := 50) (by norm_num)
  refine le_trans henc ?_
  have hexpeq : (-(1 / 2 + (3 : ℝ) - 1) : ℝ) = -(5 / 2 : ℝ) := by norm_num
  have hdeneq : ((1 / 2 : ℝ) + 3 - 1) = (5 / 2 : ℝ) := by norm_num
  rw [hexpeq, hdeneq]
  have hn0 : ‖((1 / 2 : ℂ) + 15 * Complex.I)‖ ≤ 16 := by
    rw [show ((1 / 2 : ℂ) + 15 * Complex.I) = ((1/2 : ℝ) : ℂ) + (15 : ℝ) * Complex.I by push_cast; ring]
    exact norm_le (by norm_num) (by norm_num)
  have hn1 : ‖((1 / 2 : ℂ) + 15 * Complex.I + 1)‖ ≤ 16 := by
    rw [show ((1 / 2 : ℂ) + 15 * Complex.I + 1) = ((3/2 : ℝ) : ℂ) + (15 : ℝ) * Complex.I by push_cast; ring]
    exact norm_le (by norm_num) (by norm_num)
  have hn2 : ‖((1 / 2 : ℂ) + 15 * Complex.I + 2)‖ ≤ 16 := by
    rw [show ((1 / 2 : ℂ) + 15 * Complex.I + 2) = ((5/2 : ℝ) : ℂ) + (15 : ℝ) * Complex.I by push_cast; ring]
    exact norm_le (by norm_num) (by norm_num)
  have hnorm : ‖((1 / 2 : ℂ) + 15 * Complex.I) * ((1 / 2 : ℂ) + 15 * Complex.I + 1)
        * ((1 / 2 : ℂ) + 15 * Complex.I + 2)‖ ≤ 4096 := by
    calc ‖_ * _ * _‖ = ‖((1 / 2 : ℂ) + 15 * Complex.I)‖ * ‖((1 / 2 : ℂ) + 15 * Complex.I + 1)‖
            * ‖((1 / 2 : ℂ) + 15 * Complex.I + 2)‖ := by rw [norm_mul, norm_mul]
      _ ≤ 16 * 16 * 16 := by gcongr
      _ = 4096 := by norm_num
  have hpownn : (0 : ℝ) ≤ (50 : ℝ) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc (1 / 12) * ‖_ * _ * _‖ * (50 : ℝ) ^ (-(5 / 2 : ℝ)) / (5 / 2) / 6
      ≤ (1 / 12) * 4096 * (1 / 17675) / (5 / 2) / 6 := by
        gcongr
        · exact hnorm
        · exact pow50_le
    _ ≤ 15 / 10000 := by norm_num

end ForgeTail

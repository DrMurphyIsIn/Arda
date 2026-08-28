/- Generated: a COMPLETED in-kernel bracket of the deep transcendental
   Gamma(1/2) = sqrt(pi) (GammaHalfBracketCertificate). -/
import Mathlib

namespace GammaHalf

theorem gamma_half_bracket :
    (17 : ℝ) / 10 ≤ Real.Gamma (1/2)
      ∧ Real.Gamma (1/2) ≤ (2 : ℝ) := by
  rw [Real.Gamma_one_half_eq]
  constructor
  · calc (17 : ℝ) / 10
        = Real.sqrt (((17 : ℝ) / 10) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  · calc Real.sqrt Real.pi
        ≤ Real.sqrt ((2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])
      _ = (2 : ℝ) := Real.sqrt_sq (by norm_num)

end GammaHalf

/- Generated: a COMPLETED in-kernel bracket of the deep transcendental
   Gamma(1/2) = sqrt(pi) (GammaHalfBracketCertificate). -/
import Mathlib

namespace GammaHalf

theorem gamma_half_bracket :
    (443 : ℝ) / 250 ≤ Real.Gamma (1/2)
      ∧ Real.Gamma (1/2) ≤ (71 : ℝ) / 40 := by
  rw [Real.Gamma_one_half_eq]
  constructor
  · calc (443 : ℝ) / 250
        = Real.sqrt (((443 : ℝ) / 250) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_314])
  · calc Real.sqrt Real.pi
        ≤ Real.sqrt (((71 : ℝ) / 40) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_315])
      _ = (71 : ℝ) / 40 := Real.sqrt_sq (by norm_num)

end GammaHalf

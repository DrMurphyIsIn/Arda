/- Generated transcendental sample (PiBracketCertificate). -/
import Mathlib

namespace PiBracket

theorem pi_bracket :
    (314 : ℝ) / 100 < Real.pi ∧ Real.pi < (315 : ℝ) / 100 := by
  refine ⟨?_, ?_⟩
  · first
      | linarith [Real.pi_gt_314]
      | linarith [Real.pi_gt_3141592]
      | linarith [Real.pi_gt_three]
  · first
      | linarith [Real.pi_lt_315]
      | linarith [Real.pi_lt_3141593]

end PiBracket

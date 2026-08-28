/- Generated transcendental sample (PiBracketCertificate). -/
import Mathlib

namespace PiBracket

theorem pi_bracket :
    (3 : ℝ) < Real.pi ∧ Real.pi < (4 : ℝ) :=
  ⟨Real.pi_gt_three, Real.pi_lt_four⟩

end PiBracket

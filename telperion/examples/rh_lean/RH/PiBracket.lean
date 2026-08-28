/- Generated transcendental sample (PiBracketCertificate). -/
import Mathlib

namespace PiBracket

theorem pi_bracket :
    (3.141592 : ℝ) < Real.pi ∧ Real.pi < (3.141593 : ℝ) :=
  ⟨Real.pi_gt_3141592, Real.pi_lt_3141593⟩

end PiBracket

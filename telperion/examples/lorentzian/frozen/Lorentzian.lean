/- telperion 0.1.4 | family Lorentzian | input-hash 7cbfa489a8c1a13b
   2 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Lorentzian

-- hodge_riemann_e2_n3: Hodge-Riemann / reverse Cauchy-Schwarz for a Lorentzian
-- form (signature (1,n-1)): (vᵀHw)² - (vᵀHv)(wᵀHw) = SOS ≥ 0.  This is
-- the NON-SEPARABLE inequality (couples distinct children).
theorem hodge_riemann_e2_n3 : ∀ w1 w2 w3 : ℝ, (0:ℝ) ≤ 4*w1^2 - 4*w1*w2 - 4*w1*w3 + 4*w2^2 - 4*w2*w3 + 4*w3^2 := by
  intro w1 w2 w3
  have hsos : (4*w1^2 - 4*w1*w2 - 4*w1*w3 + 4*w2^2 - 4*w2*w3 + 4*w3^2 : ℝ) = (4) * (w1 - w2/2 - w3/2)^2 + (3) * (w2 - w3)^2 := by ring
  rw [hsos]; positivity

-- hodge_riemann_e2_n4: Hodge-Riemann / reverse Cauchy-Schwarz for a Lorentzian
-- form (signature (1,n-1)): (vᵀHw)² - (vᵀHv)(wᵀHw) = SOS ≥ 0.  This is
-- the NON-SEPARABLE inequality (couples distinct children).
theorem hodge_riemann_e2_n4 : ∀ w1 w2 w3 w4 : ℝ, (0:ℝ) ≤ 9*w1^2 - 6*w1*w2 - 6*w1*w3 - 6*w1*w4 + 9*w2^2 - 6*w2*w3 - 6*w2*w4 + 9*w3^2 - 6*w3*w4 + 9*w4^2 := by
  intro w1 w2 w3 w4
  have hsos : (9*w1^2 - 6*w1*w2 - 6*w1*w3 - 6*w1*w4 + 9*w2^2 - 6*w2*w3 - 6*w2*w4 + 9*w3^2 - 6*w3*w4 + 9*w4^2 : ℝ) = (9) * (w1 - w2/3 - w3/3 - w4/3)^2 + (8) * (w2 - w3/2 - w4/2)^2 + (6) * (w3 - w4)^2 := by ring
  rw [hsos]; positivity

end Lorentzian
end G1

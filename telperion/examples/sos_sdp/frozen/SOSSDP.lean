/- telperion 0.1.3 | family SOSSDP | input-hash d85e500767a4294f
   1 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace SOSSDP

-- sdp_sos_interior_tie: SDP-SOS certificate (PSD Gram, off-diagonal coupling).
-- Complementary slackness / tight variety (p = 0 iff): -x/2 - y/2 + 1 = 0 ∧ x - y = 0
theorem sdp_sos_interior_tie : ∀ x y : ℝ, (0:ℝ) ≤ 2*x^2 - 2*x*y - 2*x + 2*y^2 - 2*y + 2 := by
  intro x y
  have hsos : (2*x^2 - 2*x*y - 2*x + 2*y^2 - 2*y + 2 : ℝ) = (2) * (-x/2 - y/2 + 1)^2 + (3/2) * (x - y)^2 := by ring
  rw [hsos]; positivity

end SOSSDP
end G1

/- telperion 0.1.6 | family Interlacing | input-hash 895bdd154afa7c7c
   2 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Interlacing

-- interlace_x2m1_x: p, q real-rooted and interlacing  <=>  Wronskian (p' * q - p * q') sign-definite (Hermite-Kakeya-Obreschkoff).
theorem interlace_x2m1_x : ∀ x : ℝ, (0:ℝ) ≤ x^2 + 1 := by
  intro x
  have hsos : (x^2 + 1 : ℝ) = (x)^2 + 1 := by ring
  rw [hsos]; positivity

-- interlace_matching_P3_P2: p, q real-rooted and interlacing  <=>  Wronskian (p' * q - p * q') sign-definite (Hermite-Kakeya-Obreschkoff).
theorem interlace_matching_P3_P2 : ∀ x : ℝ, (0:ℝ) ≤ x^4 - x^2 + 2 := by
  intro x
  have hsos : (x^4 - x^2 + 2 : ℝ) = (x^2 - 1/2)^2 + 7/4 := by ring
  rw [hsos]; positivity

end Interlacing
end G1

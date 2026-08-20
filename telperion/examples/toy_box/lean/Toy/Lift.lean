/- telperion 0.1.6 | family ToyLift | input-hash 3595a5d55ea1d7ec
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace Toy

theorem toy_lift_a1 (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (1 + u ^ 3) / ((1 + u) * (1 + u)) := by
  have hd1 : (1 + u : ℝ) ≠ 0 := by positivity
  have hkey : (1 + u ^ 3) / ((1 + u) * (1 + u))
      = (1 + u ^ 3)
        / ((1 + u) * (1 + u)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_lift_a2 (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (2 + u + u ^ 3) / ((1 + u) * (1 + u)) := by
  have hd1 : (1 + u : ℝ) ≠ 0 := by positivity
  have hkey : (2 + u + u ^ 3) / ((1 + u) * (1 + u))
      = (2 + u + u ^ 3)
        / ((1 + u) * (1 + u)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

end Toy

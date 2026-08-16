/- telperion 0.1.0 | family ToyDirect | input-hash 862b8580c8e85cd5
   3 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace Toy

theorem toy_direct_a1 (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (1 + u) / ((2 + u)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hkey : (1 + u) / ((2 + u))
      = (1 + u)
        / ((2 + u)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_direct_a2 (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (2 + 2 * u + u ^ 2) / ((1 + u) * (2 + u)) := by
  have hd1 : (1 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + u : ℝ) ≠ 0 := by positivity
  have hkey : (2 + 2 * u + u ^ 2) / ((1 + u) * (2 + u))
      = (2 + 2 * u + u ^ 2)
        / ((1 + u) * (2 + u)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_direct_a3 (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (3 + 2 * u + u ^ 2) / ((1 + u) * (2 + u)) := by
  have hd1 : (1 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + u : ℝ) ≠ 0 := by positivity
  have hkey : (3 + 2 * u + u ^ 2) / ((1 + u) * (2 + u))
      = (3 + 2 * u + u ^ 2)
        / ((1 + u) * (2 + u)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

end Toy

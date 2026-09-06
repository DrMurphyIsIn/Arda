/- telperion 0.1.6 | family TwoScaleSeparation | input-hash 97b67cde0e7caaf5
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace TwoScaleSeparation

open Metric

/-- Two-scale separation: `ρ` in the inner disk `closedBall c 1` and `z` on the
    outer sphere `sphere c (3 / 2)` are separated by `(3 / 2) - 1 ≤ ‖z - ρ‖`. -/
theorem two_scale_3half_one (c z ρ : ℂ)
    (hz : z ∈ sphere c ((3 / 2) : ℝ)) (hρ : ρ ∈ closedBall c (1 : ℝ)) :
    ((3 / 2) : ℝ) - 1 ≤ ‖z - ρ‖ := by
  rw [mem_sphere_iff_norm] at hz
  rw [mem_closedBall_iff_norm] at hρ
  calc ((3 / 2) : ℝ) - 1 ≤ ‖z - c‖ - ‖ρ - c‖ := by rw [hz]; linarith
    _ ≤ ‖(z - c) - (ρ - c)‖ := norm_sub_norm_le _ _
    _ = ‖z - ρ‖ := by rw [sub_sub_sub_cancel_right]
/-- Two-scale separation: `ρ` in the inner disk `closedBall c (1 / 2)` and `z` on the
    outer sphere `sphere c 2` are separated by `2 - (1 / 2) ≤ ‖z - ρ‖`. -/
theorem two_scale_two_half (c z ρ : ℂ)
    (hz : z ∈ sphere c (2 : ℝ)) (hρ : ρ ∈ closedBall c ((1 / 2) : ℝ)) :
    (2 : ℝ) - (1 / 2) ≤ ‖z - ρ‖ := by
  rw [mem_sphere_iff_norm] at hz
  rw [mem_closedBall_iff_norm] at hρ
  calc (2 : ℝ) - (1 / 2) ≤ ‖z - c‖ - ‖ρ - c‖ := by rw [hz]; linarith
    _ ≤ ‖(z - c) - (ρ - c)‖ := norm_sub_norm_le _ _
    _ = ‖z - ρ‖ := by rw [sub_sub_sub_cancel_right]

end TwoScaleSeparation

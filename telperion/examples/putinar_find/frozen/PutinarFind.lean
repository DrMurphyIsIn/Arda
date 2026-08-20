/- telperion 0.1.6 | family PutinarFind | input-hash ca1bd5445f57180a
   3 theorems, 9 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace PutinarFind

-- putinar_found_1mx2: Putinar certificate  p = σ_0 + Σ σ_i·g_i (SOS multipliers) on the constraint set.
theorem putinar_found_1mx2 : ∀ x y : ℝ, (0:ℝ) ≤ 1 - x → (0:ℝ) ≤ 1 + x → (0:ℝ) ≤ 1 - x ^ 2 := by
  intro x y h1 h2
  have t1 : (0:ℝ) ≤ ((1 / 2) * (1 + x)^2) * (1 - x) := mul_nonneg (by positivity) h1
  have t2 : (0:ℝ) ≤ ((1 / 2) * (1 + (-1) * x)^2) * (1 + x) := mul_nonneg (by positivity) h2
  have hid : (1 - x ^ 2 : ℝ) = ((1 / 2) * (1 + x)^2) * (1 - x) + ((1 / 2) * (1 + (-1) * x)^2) * (1 + x) := by ring
  rw [hid]; linarith

-- putinar_found_x2y: Putinar certificate  p = σ_0 + Σ σ_i·g_i (SOS multipliers) on the constraint set.
theorem putinar_found_x2y : ∀ x y : ℝ, (0:ℝ) ≤ y → (0:ℝ) ≤ y + x ^ 2 * y := by
  intro x y hy
  have t1 : (0:ℝ) ≤ (1 * (1)^2 + 1 * (x)^2) * (y) := mul_nonneg (by positivity) hy
  have hid : (y + x ^ 2 * y : ℝ) = (1 * (1)^2 + 1 * (x)^2) * (y) := by ring
  rw [hid]; linarith

-- putinar_found_x_2mx: Putinar certificate  p = σ_0 + Σ σ_i·g_i (SOS multipliers) on the constraint set.
theorem putinar_found_x_2mx : ∀ x y : ℝ, (0:ℝ) ≤ x → (0:ℝ) ≤ 2 - x → (0:ℝ) ≤ 2 * x - x ^ 2 := by
  intro x y hx hz
  have t1 : (0:ℝ) ≤ (2 * (1 + -1 * x / 2)^2) * (x) := mul_nonneg (by positivity) hx
  have t2 : (0:ℝ) ≤ ((1 / 2) * (x)^2) * (2 - x) := mul_nonneg (by positivity) hz
  have hid : (2 * x - x ^ 2 : ℝ) = (2 * (1 + -1 * x / 2)^2) * (x) + ((1 / 2) * (x)^2) * (2 - x) := by ring
  rw [hid]; linarith

end PutinarFind
end G1

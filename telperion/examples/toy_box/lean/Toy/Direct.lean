/- telperion 0.1.0 | family ToyDirect | input-hash 375c2b07e24c3822
   7 theorems, 3 generation-time self-checks passed.
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

theorem toy_direct_a1_nat (n : ℕ) (h1 : 1 ≤ n) :
    0 ≤ (1 + ((n : ℝ) - 1)) / ((2 + ((n : ℝ) - 1))) := by
  have e : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [e]
  have himg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  exact toy_direct_a1 ((n - 1 : ℕ) : ℝ) himg

theorem toy_direct_a2_nat (n : ℕ) (h1 : 1 ≤ n) :
    0 ≤ (2 + 2 * ((n : ℝ) - 1) + ((n : ℝ) - 1) ^ 2) / ((1 + ((n : ℝ) - 1)) * (2 + ((n : ℝ) - 1))) := by
  have e : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [e]
  have himg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  exact toy_direct_a2 ((n - 1 : ℕ) : ℝ) himg

theorem toy_direct_a3_nat (n : ℕ) (h1 : 1 ≤ n) :
    0 ≤ (3 + 2 * ((n : ℝ) - 1) + ((n : ℝ) - 1) ^ 2) / ((1 + ((n : ℝ) - 1)) * (2 + ((n : ℝ) - 1))) := by
  have e : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [e]
  have himg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  exact toy_direct_a3 ((n - 1 : ℕ) : ℝ) himg

theorem toy_direct_all (a : ℕ) (h1 : 1 ≤ a) (h3 : a ≤ 3) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ ((a : ℝ) + u) / (u + 1) - (a : ℝ) / (u + 2) := by
  interval_cases a
  · push_cast
    have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
    have hkey : (1 + u) / (u + 1) - 1 / (u + 2)
        = (1 + u)
          / ((2 + u)) := by
      field_simp
      try ring
    rw [hkey]
    positivity
  · push_cast
    have hd1 : (1 + u : ℝ) ≠ 0 := by positivity
    have hd2 : (2 + u : ℝ) ≠ 0 := by positivity
    have hkey : (2 + u) / (u + 1) - 2 / (u + 2)
        = (2 + 2 * u + u ^ 2)
          / ((1 + u) * (2 + u)) := by
      field_simp
      try ring
    rw [hkey]
    positivity
  · push_cast
    have hd1 : (1 + u : ℝ) ≠ 0 := by positivity
    have hd2 : (2 + u : ℝ) ≠ 0 := by positivity
    have hkey : (3 + u) / (u + 1) - 3 / (u + 2)
        = (3 + 2 * u + u ^ 2)
          / ((1 + u) * (2 + u)) := by
      field_simp
      try ring
    rw [hkey]
    positivity

end Toy

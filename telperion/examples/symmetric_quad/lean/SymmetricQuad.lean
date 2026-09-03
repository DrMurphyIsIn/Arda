/- telperion 0.1.6 | family SymmetricQuad | input-hash b260aba60a1de6d4
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SymmetricQuad

-- SYMBOLIC-IN-n level-1 moment-matrix PSD (subsetForm_d1 shape):
-- Φ = f0·A² + 2·f1·A·X + f2·X² + (f1−f2)·Q
--   = f0·(A + (f1/f0)·X)² + cCS·(N·Q − X²),  cCS = (f1−f2)/N.
-- ONE certificate, ALL N ≥ 3.  A=x_∅, X=Σxᵢ, Q=Σxᵢ²; hCS is Cauchy–Schwarz.
theorem sq_moment_d1_knapsack (N : ℝ) (hN : (3 : ℝ) ≤ N)
    (A X Q : ℝ) (hCS : X^2 ≤ N * Q) :
    (0:ℝ) ≤ (1 : ℝ) * A^2 + 2 * ((1 : ℝ) / (2 : ℝ)) * A * X + ((N - 2 : ℝ) / (4*N - 4 : ℝ)) * X^2 + (((1 : ℝ) / (2 : ℝ)) - ((N - 2 : ℝ) / (4*N - 4 : ℝ))) * Q := by
  have hNpos : (0:ℝ) < N := by linarith
  have hden0 : (0:ℝ) < (N - 1 : ℝ) := by linarith
  have hid : (1 : ℝ) * A^2 + 2 * ((1 : ℝ) / (2 : ℝ)) * A * X + ((N - 2 : ℝ) / (4*N - 4 : ℝ)) * X^2 + (((1 : ℝ) / (2 : ℝ)) - ((N - 2 : ℝ) / (4*N - 4 : ℝ))) * Q
      = (1 : ℝ) * (A + ((1 : ℝ) / (2 : ℝ)) * X)^2 + ((1 : ℝ) / (4*N - 4 : ℝ)) * (N * Q - X^2) := by
    field_simp [ne_of_gt hden0]
    ring
  have hsq : (0:ℝ) ≤ (1 : ℝ) * (A + ((1 : ℝ) / (2 : ℝ)) * X)^2 := by positivity
  have hcs : (0:ℝ) ≤ ((1 : ℝ) / (4*N - 4 : ℝ)) * (N * Q - X^2) := by
    have hrem : (0:ℝ) ≤ N * Q - X^2 := by linarith
    have hcsden : (0:ℝ) < (4*N - 4 : ℝ) := by linarith
    have hcoeff : (0:ℝ) ≤ ((1 : ℝ) / (4*N - 4 : ℝ)) :=
      div_nonneg (by positivity) (le_of_lt hcsden)
    exact mul_nonneg hcoeff hrem
  rw [hid]; linarith
-- SYMBOLIC-IN-n level-1 moment-matrix PSD (subsetForm_d1 shape):
-- Φ = f0·A² + 2·f1·A·X + f2·X² + (f1−f2)·Q
--   = f0·(A + (f1/f0)·X)² + cCS·(N·Q − X²),  cCS = (f1−f2)/N.
-- ONE certificate, ALL N ≥ 3.  A=x_∅, X=Σxᵢ, Q=Σxᵢ²; hCS is Cauchy–Schwarz.
theorem sq_moment_d1_scaled (N : ℝ) (hN : (3 : ℝ) ≤ N)
    (A X Q : ℝ) (hCS : X^2 ≤ N * Q) :
    (0:ℝ) ≤ (2 : ℝ) * A^2 + 2 * (1 : ℝ) * A * X + ((N - 2 : ℝ) / (2*N - 2 : ℝ)) * X^2 + ((1 : ℝ) - ((N - 2 : ℝ) / (2*N - 2 : ℝ))) * Q := by
  have hNpos : (0:ℝ) < N := by linarith
  have hden0 : (0:ℝ) < (N - 1 : ℝ) := by linarith
  have hid : (2 : ℝ) * A^2 + 2 * (1 : ℝ) * A * X + ((N - 2 : ℝ) / (2*N - 2 : ℝ)) * X^2 + ((1 : ℝ) - ((N - 2 : ℝ) / (2*N - 2 : ℝ))) * Q
      = (2 : ℝ) * (A + ((1 : ℝ) / (2 : ℝ)) * X)^2 + ((1 : ℝ) / (2*N - 2 : ℝ)) * (N * Q - X^2) := by
    field_simp [ne_of_gt hden0]
    ring
  have hsq : (0:ℝ) ≤ (2 : ℝ) * (A + ((1 : ℝ) / (2 : ℝ)) * X)^2 := by positivity
  have hcs : (0:ℝ) ≤ ((1 : ℝ) / (2*N - 2 : ℝ)) * (N * Q - X^2) := by
    have hrem : (0:ℝ) ≤ N * Q - X^2 := by linarith
    have hcsden : (0:ℝ) < (2*N - 2 : ℝ) := by linarith
    have hcoeff : (0:ℝ) ≤ ((1 : ℝ) / (2*N - 2 : ℝ)) :=
      div_nonneg (by positivity) (le_of_lt hcsden)
    exact mul_nonneg hcoeff hrem
  rw [hid]; linarith

end SymmetricQuad

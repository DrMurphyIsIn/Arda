/- telperion 0.1.6 | family SymmetricQuadD2 | input-hash 2e7033f43be03b57
   1 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SymmetricQuadD2

-- SYMBOLIC-IN-n level-2 moment-matrix PSD (the d=2 subset form).
-- Q2 = (A + f1·s1 + f2·s2)²  +  pcoef·(T2 − s1²/N)  +  a·N2,
--   pcoef = N/(4(N−1)) ≥ 0,  a = μ₂ = N(N−2)/(16(N−3)(N−1)) > 0 (N>3).
-- T2 = Σtᵢ² (centered CS: s1² ≤ N·T2); N2 = level-2 J(N,2) norm ≥ 0.
-- ONE certificate, ALL N ≥ 4.  See D2_CERTIFICATE.md.
theorem sq_moment_d2_knapsack (N : ℝ) (hN : (4 : ℝ) ≤ N)
    (A s1 s2 QY P W CYz T2 N2 : ℝ)
    (hT2 : T2 = ((4*CYz*N + 4*N*QY + N*W - 8*s1*s2 - 4*s2^2 : ℝ) / (4*N : ℝ)))
    (hN2def : N2 = ((N^2*P - 3*N*P - N*W + 2*P + W + 2*s2^2 : ℝ) / ((N - 2)*(N - 1) : ℝ)))
    (hCSt : s1^2 ≤ N * T2)
    (hN2 : (0:ℝ) ≤ N2) :
    (0:ℝ) ≤ (1 : ℝ) * A^2 + 2 * ((1 : ℝ) / (2 : ℝ)) * A * s1 + 2 * ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * A * s2 + ((1 : ℝ) / (2 : ℝ)) * QY + ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * (s1^2 - QY) + 2 * ((N - 4 : ℝ) / (8*(N - 1) : ℝ)) * s1 * s2 + 2 * (((N - 2 : ℝ) / (4*(N - 1) : ℝ)) - ((N - 4 : ℝ) / (8*(N - 1) : ℝ))) * CYz + ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * P + ((N - 4 : ℝ) / (8*(N - 1) : ℝ)) * (W - 2 * P) + ((N^2 - 10*N + 24 : ℝ) / (16*(N - 3)*(N - 1) : ℝ)) * (s2^2 - W + P) := by
  have hNpos : (0:ℝ) < N := by linarith
  have hden0 : (0:ℝ) < (N - 1 : ℝ) := by linarith
  have hden1 : (0:ℝ) < (N - 3 : ℝ) := by linarith
  have hden2 : (0:ℝ) < (N : ℝ) := by linarith
  have hden3 : (0:ℝ) < (N - 2 : ℝ) := by linarith
  -- the exact three-piece completing-the-square congruence (in N):
  have hid : (1 : ℝ) * A^2 + 2 * ((1 : ℝ) / (2 : ℝ)) * A * s1 + 2 * ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * A * s2 + ((1 : ℝ) / (2 : ℝ)) * QY + ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * (s1^2 - QY) + 2 * ((N - 4 : ℝ) / (8*(N - 1) : ℝ)) * s1 * s2 + 2 * (((N - 2 : ℝ) / (4*(N - 1) : ℝ)) - ((N - 4 : ℝ) / (8*(N - 1) : ℝ))) * CYz + ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * P + ((N - 4 : ℝ) / (8*(N - 1) : ℝ)) * (W - 2 * P) + ((N^2 - 10*N + 24 : ℝ) / (16*(N - 3)*(N - 1) : ℝ)) * (s2^2 - W + P)
      = (A + ((1 : ℝ) / (2 : ℝ)) * s1 + ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * s2)^2 + ((N : ℝ) / (4*(N - 1) : ℝ)) * (T2 - s1^2 / N) + ((N^2 - 2*N : ℝ) / (16*(N - 3)*(N - 1) : ℝ)) * N2 := by
    subst hT2; subst hN2def
    field_simp [ne_of_gt hden0, ne_of_gt hden1, ne_of_gt hden2, ne_of_gt hden3]
    ring
  -- piece 1: a square.
  have h1 : (0:ℝ) ≤ (A + ((1 : ℝ) / (2 : ℝ)) * s1 + ((N - 2 : ℝ) / (4*(N - 1) : ℝ)) * s2)^2 := by positivity
  -- piece 2: pcoef ≥ 0 times the centered CS remainder T2 − s1²/N ≥ 0.
  have hpden : (0:ℝ) < (4*(N - 1) : ℝ) := by linarith
  have hpnum : (0:ℝ) ≤ (N : ℝ) := by linarith
  have hpcoef : (0:ℝ) ≤ ((N : ℝ) / (4*(N - 1) : ℝ)) := div_nonneg hpnum (le_of_lt hpden)
  have hrem : (0:ℝ) ≤ T2 - s1^2 / N := by
    have hsq : s1^2 / N ≤ T2 := by
      rw [div_le_iff₀ hNpos]
      linarith [hCSt]
    linarith
  have h2 : (0:ℝ) ≤ ((N : ℝ) / (4*(N - 1) : ℝ)) * (T2 - s1^2 / N) := mul_nonneg hpcoef hrem
  -- piece 3: a = μ₂ > 0 times the level-2 positivity N2 ≥ 0.
  have haden : (0:ℝ) < (16*(N - 3)*(N - 1) : ℝ) := by positivity
  have hanum : (0:ℝ) ≤ (N^2 - 2*N : ℝ) := by nlinarith [sq_nonneg N, hN]
  have ha : (0:ℝ) ≤ ((N^2 - 2*N : ℝ) / (16*(N - 3)*(N - 1) : ℝ)) := div_nonneg hanum (le_of_lt haden)
  have h3 : (0:ℝ) ≤ ((N^2 - 2*N : ℝ) / (16*(N - 3)*(N - 1) : ℝ)) * N2 := mul_nonneg ha hN2
  rw [hid]; linarith

end SymmetricQuadD2

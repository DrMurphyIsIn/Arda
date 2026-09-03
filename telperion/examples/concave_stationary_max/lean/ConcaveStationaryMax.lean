/- telperion 0.1.6 | family ConcaveStationaryMax | input-hash b4e7288a4df8aaa1
   4 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace ConcaveStationaryMax

-- Concave-stationary-max (Kelly optimality): g(f) = wr·ln(1+f·b) + (1−wr)·ln(1−f) on (0,1), wr=11/20, b=2, f*=13/40.
-- Two load-bearing facts; the unique-max conclusion g(f) < g(f*) (f ≠ f*) follows classically.
-- FOC: g'(f*) = wr·b/(1+f*·b) − (1−wr)/(1−f*) = 0.
theorem csm_kelly_wr55_b2_foc : ((11 / 20) * 2 / (1 + (13 / 40) * 2) - (1 - (11 / 20)) / (1 - (13 / 40)) : ℝ) = 0 := by norm_num
-- strict concavity: −g''(f) = wr·b²/(1+f·b)² + (1−wr)/(1−f)² > 0 on (0,1).
theorem csm_kelly_wr55_b2_concave : ∀ f ∈ Set.Ioo (0:ℝ) 1, (0:ℝ) < (11 / 20) * 2 ^ 2 / (1 + f * 2) ^ 2 + (1 - (11 / 20)) / (1 - f) ^ 2 := by
  intro f hf
  obtain ⟨hf0, hf1⟩ := hf
  have hb : (0:ℝ) < 2 := by norm_num
  have hden1 : (0:ℝ) < 1 + f * 2 := by nlinarith
  have hden2 : (0:ℝ) < 1 - f := by linarith
  positivity
-- Concave-stationary-max (Kelly optimality): g(f) = wr·ln(1+f·b) + (1−wr)·ln(1−f) on (0,1), wr=3/5, b=3/2, f*=1/3.
-- Two load-bearing facts; the unique-max conclusion g(f) < g(f*) (f ≠ f*) follows classically.
-- FOC: g'(f*) = wr·b/(1+f*·b) − (1−wr)/(1−f*) = 0.
theorem csm_kelly_wr60_b15_foc : ((3 / 5) * (3 / 2) / (1 + (1 / 3) * (3 / 2)) - (1 - (3 / 5)) / (1 - (1 / 3)) : ℝ) = 0 := by norm_num
-- strict concavity: −g''(f) = wr·b²/(1+f·b)² + (1−wr)/(1−f)² > 0 on (0,1).
theorem csm_kelly_wr60_b15_concave : ∀ f ∈ Set.Ioo (0:ℝ) 1, (0:ℝ) < (3 / 5) * (3 / 2) ^ 2 / (1 + f * (3 / 2)) ^ 2 + (1 - (3 / 5)) / (1 - f) ^ 2 := by
  intro f hf
  obtain ⟨hf0, hf1⟩ := hf
  have hb : (0:ℝ) < (3 / 2) := by norm_num
  have hden1 : (0:ℝ) < 1 + f * (3 / 2) := by nlinarith
  have hden2 : (0:ℝ) < 1 - f := by linarith
  positivity

end ConcaveStationaryMax

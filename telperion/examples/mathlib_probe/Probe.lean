/- Nonneg cosine polynomial emitter (zero-free-region family), 4 instances, manifest SOS. -/
import Mathlib
open scoped Real

/-- Nonnegative cosine polynomial (zero-free-region certificate family):
    0 <= (3 : ℝ) + (4 : ℝ) * Real.cos θ + Real.cos (2 * θ).  Markov-Lukacs manifest form on x = cos θ. Proves nothing about RH. -/
theorem trig_nonneg_mertens_3_4_1 (θ : ℝ) : 0 ≤ (3 : ℝ) + (4 : ℝ) * Real.cos θ + Real.cos (2 * θ) := by
  have h1 : (0:ℝ) ≤ 1 + Real.cos θ := by nlinarith [Real.neg_one_le_cos θ]
  have h1' : (0:ℝ) ≤ 1 - Real.cos θ := by nlinarith [Real.cos_le_one θ]
  have key : (3 : ℝ) + (4 : ℝ) * Real.cos θ + Real.cos (2 * θ) = (2 : ℝ) * (1 + Real.cos θ) * (1 + Real.cos θ) := by rw [Real.cos_two_mul]; ring
  rw [key]
  exact (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2 : ℝ)) h1) h1)

/-- Nonnegative cosine polynomial (zero-free-region certificate family):
    0 <= (3 : ℝ) + (4 : ℝ) * Real.cos θ + (2 : ℝ) * Real.cos (2 * θ).  Markov-Lukacs manifest form on x = cos θ. Proves nothing about RH. -/
theorem trig_nonneg_sq_2cos_1 (θ : ℝ) : 0 ≤ (3 : ℝ) + (4 : ℝ) * Real.cos θ + (2 : ℝ) * Real.cos (2 * θ) := by
  have h1 : (0:ℝ) ≤ 1 + Real.cos θ := by nlinarith [Real.neg_one_le_cos θ]
  have h1' : (0:ℝ) ≤ 1 - Real.cos θ := by nlinarith [Real.cos_le_one θ]
  have key : (3 : ℝ) + (4 : ℝ) * Real.cos θ + (2 : ℝ) * Real.cos (2 * θ) = ((2 : ℝ) * Real.cos θ + (1 : ℝ)) ^ 2 := by rw [Real.cos_two_mul]; ring
  rw [key]
  exact (sq_nonneg ((2 : ℝ) * Real.cos θ + (1 : ℝ)))

/-- Nonnegative cosine polynomial (zero-free-region certificate family):
    0 <= (6 : ℝ) + (8 : ℝ) * Real.cos θ + (4 : ℝ) * Real.cos (2 * θ) + (2 : ℝ) * Real.cos (3 * θ).  Markov-Lukacs manifest form on x = cos θ. Proves nothing about RH. -/
theorem trig_nonneg_cubic_6_8_4_2 (θ : ℝ) : 0 ≤ (6 : ℝ) + (8 : ℝ) * Real.cos θ + (4 : ℝ) * Real.cos (2 * θ) + (2 : ℝ) * Real.cos (3 * θ) := by
  have h1 : (0:ℝ) ≤ 1 + Real.cos θ := by nlinarith [Real.neg_one_le_cos θ]
  have h1' : (0:ℝ) ≤ 1 - Real.cos θ := by nlinarith [Real.cos_le_one θ]
  have key : (6 : ℝ) + (8 : ℝ) * Real.cos θ + (4 : ℝ) * Real.cos (2 * θ) + (2 : ℝ) * Real.cos (3 * θ) = (2 : ℝ) * (1 + Real.cos θ) * ((4 : ℝ) * (Real.cos θ) ^ 2 + (1 : ℝ)) := by rw [Real.cos_two_mul, Real.cos_three_mul]; ring
  rw [key]
  exact (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2 : ℝ)) h1) (by positivity : (0:ℝ) ≤ (4 : ℝ) * (Real.cos θ) ^ 2 + (1 : ℝ)))

/-- Nonnegative cosine polynomial (zero-free-region certificate family):
    0 <= (8 : ℝ) + (12 : ℝ) * Real.cos θ + (6 : ℝ) * Real.cos (2 * θ) + (2 : ℝ) * Real.cos (3 * θ).  Markov-Lukacs manifest form on x = cos θ. Proves nothing about RH. -/
theorem trig_nonneg_cubic_8_12_6_2 (θ : ℝ) : 0 ≤ (8 : ℝ) + (12 : ℝ) * Real.cos θ + (6 : ℝ) * Real.cos (2 * θ) + (2 : ℝ) * Real.cos (3 * θ) := by
  have h1 : (0:ℝ) ≤ 1 + Real.cos θ := by nlinarith [Real.neg_one_le_cos θ]
  have h1' : (0:ℝ) ≤ 1 - Real.cos θ := by nlinarith [Real.cos_le_one θ]
  have key : (8 : ℝ) + (12 : ℝ) * Real.cos θ + (6 : ℝ) * Real.cos (2 * θ) + (2 : ℝ) * Real.cos (3 * θ) = (2 : ℝ) * (1 + Real.cos θ) * ((4 : ℝ) * (Real.cos θ + ((1 : ℝ) / 4)) ^ 2 + ((3 : ℝ) / 4)) := by rw [Real.cos_two_mul, Real.cos_three_mul]; ring
  rw [key]
  exact (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2 : ℝ)) h1) (by positivity : (0:ℝ) ≤ (4 : ℝ) * (Real.cos θ + ((1 : ℝ) / 4)) ^ 2 + ((3 : ℝ) / 4)))

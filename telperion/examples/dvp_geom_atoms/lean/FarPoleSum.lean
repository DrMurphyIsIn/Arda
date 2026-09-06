/- telperion 0.1.6 | family FarPoleSum | input-hash a3db8557ff502d35
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace FarPoleSum

open Metric

/-- Far-pole sum bound on the disk of radius `(3 / 2)`: the poles `(3 / 2)²/conj u` lie
    outside the disk, so `‖Σ_u (n u)·conj u/((3 / 2)² - conj u·z)‖ ≤ (Σ|n u|)/((3 / 2) - ‖z‖)`.
    A concrete-radius copy of `norm_correction_sum_le`. -/
theorem far_pole_3half (n : ℂ → ℤ) (s : Finset ℂ)
    (hsupp : ∀ u ∈ s, u ∈ ball (0 : ℂ) ((3 / 2) : ℝ)) {z : ℂ} (hz : ‖z‖ < ((3 / 2) : ℝ)) :
    ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / (((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
      ≤ (∑ u ∈ s, |(n u : ℝ)|) / (((3 / 2) : ℝ) - ‖z‖) := by
  have hR : (0 : ℝ) < (3 / 2) := by norm_num
  have hRz : 0 < ((3 / 2) : ℝ) - ‖z‖ := by linarith
  have hterm : ∀ u ∈ s,
      ‖(n u : ℂ) * (starRingEnd ℂ) u / (((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
        ≤ |(n u : ℝ)| / (((3 / 2) : ℝ) - ‖z‖) := by
    intro u hu
    have huR : ‖u‖ < ((3 / 2) : ℝ) := by rw [← mem_ball_zero_iff]; exact hsupp u hu
    have hden_ge : ((3 / 2) : ℝ) * ((3 / 2) - ‖z‖)
        ≤ ‖((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by
      calc ((3 / 2) : ℝ) * ((3 / 2) - ‖z‖) = (3 / 2) ^ 2 - (3 / 2) * ‖z‖ := by ring
        _ ≤ (3 / 2) ^ 2 - ‖u‖ * ‖z‖ := by nlinarith [norm_nonneg z, norm_nonneg u]
        _ = ‖(((3 / 2) : ℂ) ^ 2)‖ - ‖(starRingEnd ℂ) u * z‖ := by
            rw [norm_mul, RCLike.norm_conj]; norm_num
        _ ≤ ‖((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := norm_sub_norm_le _ _
    have hden_pos : 0 < ‖((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
      lt_of_lt_of_le (by positivity) hden_ge
    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_intCast]
    rw [div_le_div_iff₀ hden_pos hRz]
    calc |(n u : ℝ)| * ‖u‖ * ((3 / 2) - ‖z‖) ≤ |(n u : ℝ)| * (3 / 2) * ((3 / 2) - ‖z‖) := by
            apply mul_le_mul_of_nonneg_right _ hRz.le
            apply mul_le_mul_of_nonneg_left huR.le (abs_nonneg _)
      _ = |(n u : ℝ)| * (((3 / 2) : ℝ) * ((3 / 2) - ‖z‖)) := by ring
      _ ≤ |(n u : ℝ)| * ‖((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
            mul_le_mul_of_nonneg_left hden_ge (abs_nonneg _)
  calc ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / (((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
      ≤ ∑ u ∈ s, ‖(n u : ℂ) * (starRingEnd ℂ) u / (((3 / 2) : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ u ∈ s, |(n u : ℝ)| / (((3 / 2) : ℝ) - ‖z‖) := Finset.sum_le_sum hterm
    _ = (∑ u ∈ s, |(n u : ℝ)|) / (((3 / 2) : ℝ) - ‖z‖) := by rw [Finset.sum_div]
/-- Far-pole sum bound on the disk of radius `2`: the poles `2²/conj u` lie
    outside the disk, so `‖Σ_u (n u)·conj u/(2² - conj u·z)‖ ≤ (Σ|n u|)/(2 - ‖z‖)`.
    A concrete-radius copy of `norm_correction_sum_le`. -/
theorem far_pole_two (n : ℂ → ℤ) (s : Finset ℂ)
    (hsupp : ∀ u ∈ s, u ∈ ball (0 : ℂ) (2 : ℝ)) {z : ℂ} (hz : ‖z‖ < (2 : ℝ)) :
    ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / ((2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
      ≤ (∑ u ∈ s, |(n u : ℝ)|) / ((2 : ℝ) - ‖z‖) := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hRz : 0 < (2 : ℝ) - ‖z‖ := by linarith
  have hterm : ∀ u ∈ s,
      ‖(n u : ℂ) * (starRingEnd ℂ) u / ((2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
        ≤ |(n u : ℝ)| / ((2 : ℝ) - ‖z‖) := by
    intro u hu
    have huR : ‖u‖ < (2 : ℝ) := by rw [← mem_ball_zero_iff]; exact hsupp u hu
    have hden_ge : (2 : ℝ) * (2 - ‖z‖)
        ≤ ‖(2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by
      calc (2 : ℝ) * (2 - ‖z‖) = 2 ^ 2 - 2 * ‖z‖ := by ring
        _ ≤ 2 ^ 2 - ‖u‖ * ‖z‖ := by nlinarith [norm_nonneg z, norm_nonneg u]
        _ = ‖((2 : ℂ) ^ 2)‖ - ‖(starRingEnd ℂ) u * z‖ := by
            rw [norm_mul, RCLike.norm_conj]; norm_num
        _ ≤ ‖(2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := norm_sub_norm_le _ _
    have hden_pos : 0 < ‖(2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
      lt_of_lt_of_le (by positivity) hden_ge
    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_intCast]
    rw [div_le_div_iff₀ hden_pos hRz]
    calc |(n u : ℝ)| * ‖u‖ * (2 - ‖z‖) ≤ |(n u : ℝ)| * 2 * (2 - ‖z‖) := by
            apply mul_le_mul_of_nonneg_right _ hRz.le
            apply mul_le_mul_of_nonneg_left huR.le (abs_nonneg _)
      _ = |(n u : ℝ)| * ((2 : ℝ) * (2 - ‖z‖)) := by ring
      _ ≤ |(n u : ℝ)| * ‖(2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
            mul_le_mul_of_nonneg_left hden_ge (abs_nonneg _)
  calc ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / ((2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
      ≤ ∑ u ∈ s, ‖(n u : ℂ) * (starRingEnd ℂ) u / ((2 : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ u ∈ s, |(n u : ℝ)| / ((2 : ℝ) - ‖z‖) := Finset.sum_le_sum hterm
    _ = (∑ u ∈ s, |(n u : ℝ)|) / ((2 : ℝ) - ‖z‖) := by rw [Finset.sum_div]

end FarPoleSum

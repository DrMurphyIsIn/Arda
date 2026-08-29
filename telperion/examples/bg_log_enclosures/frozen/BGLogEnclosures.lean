/- TightLogCertificate wired into BG: the sweep-constant log enclosures of
   R3Cert/Sweep.lean (log_three_half_enclosure, log_four_third_enclosure).
   Tight rational enclosures of log(3/2), log(4/3) over the {log 2, log 3} basis,
   from Mathlib's Real.log_{two,three}_{gt,lt}_d9 decimal constants + nlinarith --
   BG's exact /1000 windows, regenerated + kernel-checkable. -/
import Mathlib

namespace BGLogEnclosures

theorem log_three_half_enclosure :
    (405 : ℝ) / 1000 < Real.log ((3 : ℝ) / 2)
      ∧ Real.log ((3 : ℝ) / 2) < (406 : ℝ) / 1000 := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hN : Real.log (3 : ℝ) = (0 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 := by
    rw [show (3 : ℝ) = (2 : ℝ) ^ (0 : ℕ) * (3 : ℝ) ^ (1 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hD : Real.log (2 : ℝ) = (1 : ℝ) * Real.log 2 + (0 : ℝ) * Real.log 3 := by
    rw [show (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) * (3 : ℝ) ^ (0 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have e : Real.log ((3 : ℝ) / 2) = (-1 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hN, hD]; push_cast; ring
  rw [e]
  refine ⟨by nlinarith [h2lo, h2hi, h3lo, h3hi], by nlinarith [h2lo, h2hi, h3lo, h3hi]⟩

theorem log_four_third_enclosure :
    (287 : ℝ) / 1000 < Real.log ((4 : ℝ) / 3)
      ∧ Real.log ((4 : ℝ) / 3) < (288 : ℝ) / 1000 := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hN : Real.log (4 : ℝ) = (2 : ℝ) * Real.log 2 + (0 : ℝ) * Real.log 3 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) * (3 : ℝ) ^ (0 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hD : Real.log (3 : ℝ) = (0 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 := by
    rw [show (3 : ℝ) = (2 : ℝ) ^ (0 : ℕ) * (3 : ℝ) ^ (1 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have e : Real.log ((4 : ℝ) / 3) = (2 : ℝ) * Real.log 2 + (-1 : ℝ) * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hN, hD]; push_cast; ring
  rw [e]
  refine ⟨by nlinarith [h2lo, h2hi, h3lo, h3hi], by nlinarith [h2lo, h2hi, h3lo, h3hi]⟩

end BGLogEnclosures

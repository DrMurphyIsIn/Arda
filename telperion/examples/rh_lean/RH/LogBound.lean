/- Generated transcendental samples (LogBoundCertificate). -/
import Mathlib

namespace LogBound

theorem log_two :
    (1 - (1 : ℝ) / 2) ≤ Real.log ((2 : ℝ) / 1)
      ∧ Real.log ((2 : ℝ) / 1) ≤ (2 : ℝ) / 1 - 1 := by
  have hpos : (0 : ℝ) < (2 : ℝ) / 1 := by norm_num
  have hupper : Real.log ((2 : ℝ) / 1) ≤ (2 : ℝ) / 1 - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have hinvpos : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hlow' : Real.log ((1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - 1 :=
    Real.log_le_sub_one_of_pos hinvpos
  have hne : ((2 : ℝ) / 1)⁻¹ = (1 : ℝ) / 2 := by norm_num
  have hneg : Real.log ((1 : ℝ) / 2) = - Real.log ((2 : ℝ) / 1) := by
    rw [← hne, Real.log_inv]
  constructor
  · nlinarith [hlow', hneg]
  · exact hupper

theorem log_three_halves :
    (1 - (2 : ℝ) / 3) ≤ Real.log ((3 : ℝ) / 2)
      ∧ Real.log ((3 : ℝ) / 2) ≤ (3 : ℝ) / 2 - 1 := by
  have hpos : (0 : ℝ) < (3 : ℝ) / 2 := by norm_num
  have hupper : Real.log ((3 : ℝ) / 2) ≤ (3 : ℝ) / 2 - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have hinvpos : (0 : ℝ) < (2 : ℝ) / 3 := by norm_num
  have hlow' : Real.log ((2 : ℝ) / 3) ≤ (2 : ℝ) / 3 - 1 :=
    Real.log_le_sub_one_of_pos hinvpos
  have hne : ((3 : ℝ) / 2)⁻¹ = (2 : ℝ) / 3 := by norm_num
  have hneg : Real.log ((2 : ℝ) / 3) = - Real.log ((3 : ℝ) / 2) := by
    rw [← hne, Real.log_inv]
  constructor
  · nlinarith [hlow', hneg]
  · exact hupper

theorem log_ten :
    (1 - (1 : ℝ) / 10) ≤ Real.log ((10 : ℝ) / 1)
      ∧ Real.log ((10 : ℝ) / 1) ≤ (10 : ℝ) / 1 - 1 := by
  have hpos : (0 : ℝ) < (10 : ℝ) / 1 := by norm_num
  have hupper : Real.log ((10 : ℝ) / 1) ≤ (10 : ℝ) / 1 - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have hinvpos : (0 : ℝ) < (1 : ℝ) / 10 := by norm_num
  have hlow' : Real.log ((1 : ℝ) / 10) ≤ (1 : ℝ) / 10 - 1 :=
    Real.log_le_sub_one_of_pos hinvpos
  have hne : ((10 : ℝ) / 1)⁻¹ = (1 : ℝ) / 10 := by norm_num
  have hneg : Real.log ((1 : ℝ) / 10) = - Real.log ((10 : ℝ) / 1) := by
    rw [← hne, Real.log_inv]
  constructor
  · nlinarith [hlow', hneg]
  · exact hupper

end LogBound

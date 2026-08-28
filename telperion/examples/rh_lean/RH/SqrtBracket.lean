/- Generated transcendental samples (SqrtBracketCertificate). -/
import Mathlib

namespace SqrtBracket

theorem sqrt_two :
    (1414213562373 : ℝ) / 1000000000000 ≤ Real.sqrt ((2 : ℝ) / 1)
      ∧ Real.sqrt ((2 : ℝ) / 1) ≤ (14142135623731 : ℝ) / 10000000000000 := by
  constructor
  · calc ((1414213562373 : ℝ) / 1000000000000)
        = Real.sqrt (((1414213562373 : ℝ) / 1000000000000) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt ((2 : ℝ) / 1) := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt ((2 : ℝ) / 1)
        ≤ Real.sqrt (((14142135623731 : ℝ) / 10000000000000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (14142135623731 : ℝ) / 10000000000000 := Real.sqrt_sq (by norm_num)

theorem sqrt_three :
    (2165063509461 : ℝ) / 1250000000000 ≤ Real.sqrt ((3 : ℝ) / 1)
      ∧ Real.sqrt ((3 : ℝ) / 1) ≤ (17320508075689 : ℝ) / 10000000000000 := by
  constructor
  · calc ((2165063509461 : ℝ) / 1250000000000)
        = Real.sqrt (((2165063509461 : ℝ) / 1250000000000) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt ((3 : ℝ) / 1) := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt ((3 : ℝ) / 1)
        ≤ Real.sqrt (((17320508075689 : ℝ) / 10000000000000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (17320508075689 : ℝ) / 10000000000000 := Real.sqrt_sq (by norm_num)

theorem sqrt_ten :
    (31622776601683 : ℝ) / 10000000000000 ≤ Real.sqrt ((10 : ℝ) / 1)
      ∧ Real.sqrt ((10 : ℝ) / 1) ≤ (7905694150421 : ℝ) / 2500000000000 := by
  constructor
  · calc ((31622776601683 : ℝ) / 10000000000000)
        = Real.sqrt (((31622776601683 : ℝ) / 10000000000000) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt ((10 : ℝ) / 1) := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt ((10 : ℝ) / 1)
        ≤ Real.sqrt (((7905694150421 : ℝ) / 2500000000000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (7905694150421 : ℝ) / 2500000000000 := Real.sqrt_sq (by norm_num)

end SqrtBracket

/- Weil-form positive-definiteness (3-dim test basis) via Sylvester + WorstCorner. -/
import Mathlib
open scoped Real

/- Weil-form positive-definiteness on a 3-dim test basis, via Sylvester:
   every symmetric matrix with entries in the given brackets has all leading
   principal minors D_r > 0, hence is positive-definite.  The Weil matrix (entries
   from the explicit formula: digamma + prime sum) lies in the box, so the Weil form
   is PSD on this basis -- a NECESSARY condition for RH (never a proof). -/

set_option maxHeartbeats 400000 in
theorem weil_psd_3_minor1 {g0 : ℝ} (a0 : ((660071 : ℝ) / 312500) ≤ g0) (b0 : g0 ≤ ((2640309 : ℝ) / 1250000)) :
    0 < (1 : ℝ)*g0 := by
  have n0 : (0 : ℝ) ≤ g0 := le_trans (by norm_num) a0
  have M0 : (((660071 : ℝ) / 312500)) ≤ g0 := a0
  linarith [M0]

set_option maxHeartbeats 400000 in
theorem weil_psd_3_minor2 {g0 g1 g3 : ℝ} (a0 : ((660071 : ℝ) / 312500) ≤ g0) (b0 : g0 ≤ ((2640309 : ℝ) / 1250000)) (a1 : ((14339803 : ℝ) / 5000000) ≤ g1) (b1 : g1 ≤ ((14339903 : ℝ) / 5000000)) (a3 : ((20892799 : ℝ) / 5000000) ≤ g3) (b3 : g3 ≤ ((20892899 : ℝ) / 5000000)) :
    0 < (1 : ℝ)*g0*g3 - (1 : ℝ)*g1*g1 := by
  have n0 : (0 : ℝ) ≤ g0 := le_trans (by norm_num) a0
  have n1 : (0 : ℝ) ≤ g1 := le_trans (by norm_num) a1
  have n3 : (0 : ℝ) ≤ g3 := le_trans (by norm_num) a3
  have M0 : (((660071 : ℝ) / 312500))*(((20892799 : ℝ) / 5000000)) ≤ g0*g3 := (mul_le_mul a0 a3 (by norm_num) n0)
  have M1 : g1*g1 ≤ (((14339903 : ℝ) / 5000000))*(((14339903 : ℝ) / 5000000)) := (mul_le_mul b1 b1 n1 (le_trans n1 b1))
  linarith [M0, M1]

set_option maxHeartbeats 800000 in
theorem weil_psd_3_minor3 {g0 g1 g2 g3 g4 g5 : ℝ} (a0 : ((660071 : ℝ) / 312500) ≤ g0) (b0 : g0 ≤ ((2640309 : ℝ) / 1250000)) (a1 : ((14339803 : ℝ) / 5000000) ≤ g1) (b1 : g1 ≤ ((14339903 : ℝ) / 5000000)) (a2 : ((16876089 : ℝ) / 5000000) ≤ g2) (b2 : g2 ≤ ((16876189 : ℝ) / 5000000)) (a3 : ((20892799 : ℝ) / 5000000) ≤ g3) (b3 : g3 ≤ ((20892899 : ℝ) / 5000000)) (a4 : ((51732853 : ℝ) / 10000000) ≤ g4) (b4 : g4 ≤ ((51733053 : ℝ) / 10000000)) (a5 : ((16682737 : ℝ) / 2500000) ≤ g5) (b5 : g5 ≤ ((16682787 : ℝ) / 2500000)) :
    0 < (1 : ℝ)*g0*g3*g5 - (1 : ℝ)*g0*g4*g4 - (1 : ℝ)*g1*g1*g5 + (2 : ℝ)*g1*g2*g4 - (1 : ℝ)*g2*g2*g3 := by
  have n0 : (0 : ℝ) ≤ g0 := le_trans (by norm_num) a0
  have n1 : (0 : ℝ) ≤ g1 := le_trans (by norm_num) a1
  have n2 : (0 : ℝ) ≤ g2 := le_trans (by norm_num) a2
  have n3 : (0 : ℝ) ≤ g3 := le_trans (by norm_num) a3
  have n4 : (0 : ℝ) ≤ g4 := le_trans (by norm_num) a4
  have n5 : (0 : ℝ) ≤ g5 := le_trans (by norm_num) a5
  have M0 : (((660071 : ℝ) / 312500))*(((20892799 : ℝ) / 5000000))*(((16682737 : ℝ) / 2500000)) ≤ g0*g3*g5 := (mul_le_mul (mul_le_mul a0 a3 (by norm_num) n0) a5 (by norm_num) (mul_nonneg n0 n3))
  have M1 : g0*g4*g4 ≤ (((2640309 : ℝ) / 1250000))*(((51733053 : ℝ) / 10000000))*(((51733053 : ℝ) / 10000000)) := (mul_le_mul (mul_le_mul b0 b4 n4 (le_trans n0 b0)) b4 n4 (mul_nonneg (le_trans n0 b0) (le_trans n4 b4)))
  have M2 : g1*g1*g5 ≤ (((14339903 : ℝ) / 5000000))*(((14339903 : ℝ) / 5000000))*(((16682787 : ℝ) / 2500000)) := (mul_le_mul (mul_le_mul b1 b1 n1 (le_trans n1 b1)) b5 n5 (mul_nonneg (le_trans n1 b1) (le_trans n1 b1)))
  have M3 : (((14339803 : ℝ) / 5000000))*(((16876089 : ℝ) / 5000000))*(((51732853 : ℝ) / 10000000)) ≤ g1*g2*g4 := (mul_le_mul (mul_le_mul a1 a2 (by norm_num) n1) a4 (by norm_num) (mul_nonneg n1 n2))
  have M4 : g2*g2*g3 ≤ (((16876189 : ℝ) / 5000000))*(((16876189 : ℝ) / 5000000))*(((20892899 : ℝ) / 5000000)) := (mul_le_mul (mul_le_mul b2 b2 n2 (le_trans n2 b2)) b3 n3 (mul_nonneg (le_trans n2 b2) (le_trans n2 b2)))
  linarith [M0, M1, M2, M3, M4]

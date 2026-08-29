/- Robin criterion probe: sigma(n) < e^gamma n loglog n, conditional on two rational
   brackets (E_lo<=e^gamma, LL_lo<=loglog n). Validates the arithmetic positivity
   assembly; bracket-discharge (from Mathlib gamma>1/2 + log2 d9) is separate. -/
import Mathlib
open scoped Real

/-- Robin's inequality at n=5041: sigma(5041)=5113 < e^gamma * 5041 * log log 5041.  Consumes E_lo <= e^gamma and LL_lo <= log log n; the arithmetic sigma < E_lo*n*LL_lo is exact. -/
theorem robin_n5041
    (hγ : ((1648721 : ℝ) / 1000000) ≤ Real.exp Real.eulerMascheroniConstant)
    (hll : ((20794415409 : ℝ) / 10000000000) ≤ Real.log (Real.log (5041 : ℝ))) :
    (5113 : ℝ) < Real.exp Real.eulerMascheroniConstant * (5041 : ℝ) * Real.log (Real.log (5041 : ℝ)) := by
  have hE : (0:ℝ) < ((1648721 : ℝ) / 1000000) := by norm_num
  have hLL : (0:ℝ) < ((20794415409 : ℝ) / 10000000000) := by norm_num
  have hn : (0:ℝ) < (5041 : ℝ) := by norm_num
  have hg : (0:ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (5113 : ℝ) < ((1648721 : ℝ) / 1000000) * (5041 : ℝ) * ((20794415409 : ℝ) / 10000000000) := by norm_num
  nlinarith [hγ, hll, hE, hLL, hn, hg,
    mul_le_mul hγ (le_refl (5041 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hll (le_of_lt (mul_pos hg hn))]

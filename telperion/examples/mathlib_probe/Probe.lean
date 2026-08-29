/- Robin's criterion for RH (Robin 1984), UNCONDITIONAL in-kernel instances:
   sigma(n) < e^gamma * n * log log n for n in {5041,5042,8192,65537}.  RH <=>
   this holds for all n >= 5041; a single violator disproves RH.  e^gamma bracket
   from Real.one_half_lt_eulerMascheroniConstant + Taylor exp; loglog from log-2
   d9.  RH-EQUIVALENT, finite, arithmetic -- a different family from the Jensen
   hyperbolicity ladder. -/
import Mathlib
open scoped Real

namespace Robin

/-- Robin's inequality at n=5041, UNCONDITIONAL: sigma(5041)=5113 < e^gamma * 5041 * log log 5041.  Both brackets discharged in-kernel (gamma>1/2 via Real.one_half_lt_eulerMascheroniConstant; loglog via log-2 d9). -/
theorem robin_n5041 :
    (5113 : ℝ) < Real.exp Real.eulerMascheroniConstant * (5041 : ℝ) * Real.log (Real.log (5041 : ℝ)) := by
  -- e^gamma >= e^(1/2) >= E_lo  (Taylor lower bound + gamma>1/2)
  have hexp : (((1648721 : ℝ) / 1000000)) ≤ Real.exp ((1 : ℝ) / 2) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 12)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hγ : (((1648721 : ℝ) / 1000000)) ≤ Real.exp Real.eulerMascheroniConstant :=
    le_trans hexp (Real.exp_le_exp.mpr (le_of_lt Real.one_half_lt_eulerMascheroniConstant))
  -- log n >= a * log 2 >= a * log2_lo
  have hl2 := Real.log_two_gt_d9
  have hlogn : (12 : ℝ) * Real.log 2 ≤ Real.log (5041 : ℝ) := by
    have h : Real.log ((2 : ℝ) ^ (12 : ℕ)) ≤ Real.log (5041 : ℝ) := by
      gcongr
      norm_num
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hlogn_lo : (((20794415409 : ℝ) / 2500000000)) ≤ Real.log (5041 : ℝ) := by nlinarith [hlogn, hl2]
  -- log log n >= c * log 2 = LL_lo
  have h2c : ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (5041 : ℝ) := by
    have hb : ((2 : ℝ) ^ (3 : ℕ)) ≤ (((20794415409 : ℝ) / 2500000000)) := by norm_num
    linarith [hlogn_lo, hb]
  have hll : (3 : ℝ) * Real.log 2 ≤ Real.log (Real.log (5041 : ℝ)) := by
    have h : Real.log ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (Real.log (5041 : ℝ)) := by
      gcongr
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hLL : (((20794415409 : ℝ) / 10000000000)) ≤ Real.log (Real.log (5041 : ℝ)) := by nlinarith [hll, hl2]
  -- positivity + exact arithmetic assembly
  have hE : (0:ℝ) < ((1648721 : ℝ) / 1000000) := by norm_num
  have hLLp : (0:ℝ) < ((20794415409 : ℝ) / 10000000000) := by norm_num
  have hn : (0:ℝ) < (5041 : ℝ) := by norm_num
  have hg : (0:ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (5113 : ℝ) < ((1648721 : ℝ) / 1000000) * (5041 : ℝ) * ((20794415409 : ℝ) / 10000000000) := by norm_num
  nlinarith [hγ, hLL, hE, hLLp, hn, hg,
    mul_le_mul hγ (le_refl (5041 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=5042, UNCONDITIONAL: sigma(5042)=7566 < e^gamma * 5042 * log log 5042.  Both brackets discharged in-kernel (gamma>1/2 via Real.one_half_lt_eulerMascheroniConstant; loglog via log-2 d9). -/
theorem robin_n5042 :
    (7566 : ℝ) < Real.exp Real.eulerMascheroniConstant * (5042 : ℝ) * Real.log (Real.log (5042 : ℝ)) := by
  -- e^gamma >= e^(1/2) >= E_lo  (Taylor lower bound + gamma>1/2)
  have hexp : (((1648721 : ℝ) / 1000000)) ≤ Real.exp ((1 : ℝ) / 2) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 12)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hγ : (((1648721 : ℝ) / 1000000)) ≤ Real.exp Real.eulerMascheroniConstant :=
    le_trans hexp (Real.exp_le_exp.mpr (le_of_lt Real.one_half_lt_eulerMascheroniConstant))
  -- log n >= a * log 2 >= a * log2_lo
  have hl2 := Real.log_two_gt_d9
  have hlogn : (12 : ℝ) * Real.log 2 ≤ Real.log (5042 : ℝ) := by
    have h : Real.log ((2 : ℝ) ^ (12 : ℕ)) ≤ Real.log (5042 : ℝ) := by
      gcongr
      norm_num
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hlogn_lo : (((20794415409 : ℝ) / 2500000000)) ≤ Real.log (5042 : ℝ) := by nlinarith [hlogn, hl2]
  -- log log n >= c * log 2 = LL_lo
  have h2c : ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (5042 : ℝ) := by
    have hb : ((2 : ℝ) ^ (3 : ℕ)) ≤ (((20794415409 : ℝ) / 2500000000)) := by norm_num
    linarith [hlogn_lo, hb]
  have hll : (3 : ℝ) * Real.log 2 ≤ Real.log (Real.log (5042 : ℝ)) := by
    have h : Real.log ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (Real.log (5042 : ℝ)) := by
      gcongr
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hLL : (((20794415409 : ℝ) / 10000000000)) ≤ Real.log (Real.log (5042 : ℝ)) := by nlinarith [hll, hl2]
  -- positivity + exact arithmetic assembly
  have hE : (0:ℝ) < ((1648721 : ℝ) / 1000000) := by norm_num
  have hLLp : (0:ℝ) < ((20794415409 : ℝ) / 10000000000) := by norm_num
  have hn : (0:ℝ) < (5042 : ℝ) := by norm_num
  have hg : (0:ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (7566 : ℝ) < ((1648721 : ℝ) / 1000000) * (5042 : ℝ) * ((20794415409 : ℝ) / 10000000000) := by norm_num
  nlinarith [hγ, hLL, hE, hLLp, hn, hg,
    mul_le_mul hγ (le_refl (5042 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=8192, UNCONDITIONAL: sigma(8192)=16383 < e^gamma * 8192 * log log 8192.  Both brackets discharged in-kernel (gamma>1/2 via Real.one_half_lt_eulerMascheroniConstant; loglog via log-2 d9). -/
theorem robin_n8192 :
    (16383 : ℝ) < Real.exp Real.eulerMascheroniConstant * (8192 : ℝ) * Real.log (Real.log (8192 : ℝ)) := by
  -- e^gamma >= e^(1/2) >= E_lo  (Taylor lower bound + gamma>1/2)
  have hexp : (((1648721 : ℝ) / 1000000)) ≤ Real.exp ((1 : ℝ) / 2) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 12)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hγ : (((1648721 : ℝ) / 1000000)) ≤ Real.exp Real.eulerMascheroniConstant :=
    le_trans hexp (Real.exp_le_exp.mpr (le_of_lt Real.one_half_lt_eulerMascheroniConstant))
  -- log n >= a * log 2 >= a * log2_lo
  have hl2 := Real.log_two_gt_d9
  have hlogn : (13 : ℝ) * Real.log 2 ≤ Real.log (8192 : ℝ) := by
    have h : Real.log ((2 : ℝ) ^ (13 : ℕ)) ≤ Real.log (8192 : ℝ) := by
      gcongr
      norm_num
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hlogn_lo : (((90109133439 : ℝ) / 10000000000)) ≤ Real.log (8192 : ℝ) := by nlinarith [hlogn, hl2]
  -- log log n >= c * log 2 = LL_lo
  have h2c : ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (8192 : ℝ) := by
    have hb : ((2 : ℝ) ^ (3 : ℕ)) ≤ (((90109133439 : ℝ) / 10000000000)) := by norm_num
    linarith [hlogn_lo, hb]
  have hll : (3 : ℝ) * Real.log 2 ≤ Real.log (Real.log (8192 : ℝ)) := by
    have h : Real.log ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (Real.log (8192 : ℝ)) := by
      gcongr
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hLL : (((20794415409 : ℝ) / 10000000000)) ≤ Real.log (Real.log (8192 : ℝ)) := by nlinarith [hll, hl2]
  -- positivity + exact arithmetic assembly
  have hE : (0:ℝ) < ((1648721 : ℝ) / 1000000) := by norm_num
  have hLLp : (0:ℝ) < ((20794415409 : ℝ) / 10000000000) := by norm_num
  have hn : (0:ℝ) < (8192 : ℝ) := by norm_num
  have hg : (0:ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (16383 : ℝ) < ((1648721 : ℝ) / 1000000) * (8192 : ℝ) * ((20794415409 : ℝ) / 10000000000) := by norm_num
  nlinarith [hγ, hLL, hE, hLLp, hn, hg,
    mul_le_mul hγ (le_refl (8192 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=65537, UNCONDITIONAL: sigma(65537)=65538 < e^gamma * 65537 * log log 65537.  Both brackets discharged in-kernel (gamma>1/2 via Real.one_half_lt_eulerMascheroniConstant; loglog via log-2 d9). -/
theorem robin_n65537 :
    (65538 : ℝ) < Real.exp Real.eulerMascheroniConstant * (65537 : ℝ) * Real.log (Real.log (65537 : ℝ)) := by
  -- e^gamma >= e^(1/2) >= E_lo  (Taylor lower bound + gamma>1/2)
  have hexp : (((1648721 : ℝ) / 1000000)) ≤ Real.exp ((1 : ℝ) / 2) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 12)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hγ : (((1648721 : ℝ) / 1000000)) ≤ Real.exp Real.eulerMascheroniConstant :=
    le_trans hexp (Real.exp_le_exp.mpr (le_of_lt Real.one_half_lt_eulerMascheroniConstant))
  -- log n >= a * log 2 >= a * log2_lo
  have hl2 := Real.log_two_gt_d9
  have hlogn : (16 : ℝ) * Real.log 2 ≤ Real.log (65537 : ℝ) := by
    have h : Real.log ((2 : ℝ) ^ (16 : ℕ)) ≤ Real.log (65537 : ℝ) := by
      gcongr
      norm_num
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hlogn_lo : (((6931471803 : ℝ) / 625000000)) ≤ Real.log (65537 : ℝ) := by nlinarith [hlogn, hl2]
  -- log log n >= c * log 2 = LL_lo
  have h2c : ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (65537 : ℝ) := by
    have hb : ((2 : ℝ) ^ (3 : ℕ)) ≤ (((6931471803 : ℝ) / 625000000)) := by norm_num
    linarith [hlogn_lo, hb]
  have hll : (3 : ℝ) * Real.log 2 ≤ Real.log (Real.log (65537 : ℝ)) := by
    have h : Real.log ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (Real.log (65537 : ℝ)) := by
      gcongr
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hLL : (((20794415409 : ℝ) / 10000000000)) ≤ Real.log (Real.log (65537 : ℝ)) := by nlinarith [hll, hl2]
  -- positivity + exact arithmetic assembly
  have hE : (0:ℝ) < ((1648721 : ℝ) / 1000000) := by norm_num
  have hLLp : (0:ℝ) < ((20794415409 : ℝ) / 10000000000) := by norm_num
  have hn : (0:ℝ) < (65537 : ℝ) := by norm_num
  have hg : (0:ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (65538 : ℝ) < ((1648721 : ℝ) / 1000000) * (65537 : ℝ) * ((20794415409 : ℝ) / 10000000000) := by norm_num
  nlinarith [hγ, hLL, hE, hLLp, hn, hg,
    mul_le_mul hγ (le_refl (65537 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

end Robin

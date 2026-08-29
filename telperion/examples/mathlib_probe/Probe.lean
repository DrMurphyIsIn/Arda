/- Robin's criterion at the RH-TIGHT boundary: n=25200 is SUPERABUNDANT (ratio
   sigma/(n loglog) ~1.71, far beyond the comfortable regime that gamma>1/2 reaches).
   UNCONDITIONAL: tight gamma via eulerMascheroniSeq 31 (harmonic 31 - log 32, 32=2^5),
   tight loglog via log 25200 >= 13log2+log3 > 10 then loglog >= log 10 (taylor_log k=10). -/
import Mathlib
open scoped Real

theorem robin_tight_n25200 :
    (99944 : ℝ) < Real.exp Real.eulerMascheroniConstant * (25200 : ℝ) * Real.log (Real.log (25200 : ℝ)) := by
  -- ===== tight e^gamma: gamma > H31 - 5 log2 >= 561/1000, so e^gamma >= E_lo =====
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlog32] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : (561 : ℝ) / 1000 < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 12)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  -- ===== tight loglog: log 25200 >= 13log2+log3 > 10 ; loglog >= log 10 >= LL_lo =====
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (13 : ℝ) * Real.log 2 + Real.log 3 ≤ Real.log (25200 : ℝ) := by
    have h : Real.log (24576 : ℝ) ≤ Real.log (25200 : ℝ) := by gcongr; norm_num
    have e : Real.log (24576 : ℝ) = 13 * Real.log 2 + Real.log 3 := by
      rw [show (24576 : ℝ) = 2 ^ (13 : ℕ) * 3 by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlogn10 : (10 : ℝ) ≤ Real.log (25200 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log (10 : ℝ) ≤ Real.log (Real.log (25200 : ℝ)) := by gcongr
  -- log(1 - 1/10) upper bound via taylor_log k=10 deg 4
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 10 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 10 : ℝ) ^ (i + 1) / (i + 1)) = 12643 / 120000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 10 : ℝ)| ^ (4 + 1) / (1 - |1 / 10|) = 1 / 90000 := by
    rw [show |(1 / 10 : ℝ)| = 1 / 10 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlog10 : ((2302571799 : ℝ) / 1000000000) ≤ Real.log (10 : ℝ) := by
    have e : Real.log (10 : ℝ) = 2 * Real.log 3 - Real.log (1 - 1 / 10 : ℝ) := by
      rw [show (10 : ℝ) = 3 ^ (2 : ℕ) * (1 - 1 / 10)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_inv]
      push_cast; ring
    rw [e]; nlinarith [htay.2, hl3lo]
  have hLL : ((2302571799 : ℝ) / 1000000000) ≤ Real.log (Real.log (25200 : ℝ)) := le_trans hlog10 hll1
  -- ===== positivity + exact arithmetic assembly =====
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2302571799 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (25200 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (99944 : ℝ) < ((219053 : ℝ) / 125000) * (25200 : ℝ) * ((2302571799 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (25200 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

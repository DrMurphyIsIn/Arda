/- Robin's criterion for RH (Robin 1984), UNCONDITIONAL in-kernel instances:
   sigma(n) < e^gamma * n * log log n for n in {5041,5042,8192,65537} (comfortable)
   and for ALL 13 SUPERABUNDANT numbers in (5040, 2*10^6] (RH-tight regime).  RH <=>
   this holds for all n >= 5041; a single violator disproves RH -- so each is a finite
   check consistent with (never a proof of) RH.  Comfortable n: e^gamma from
   Real.one_half_lt_eulerMascheroniConstant + Taylor exp, loglog from log-2 d9.
   Superabundant n: tight e^gamma from eulerMascheroniSeq, tight loglog from taylor_log.
   See ROBIN_REDUCTION_D3.md for the reduction scope (this does NOT prove all n <= X). -/
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

/-- Robin's inequality at n=10080 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(10080)=39312 < e^gamma * 10080 * log log 10080.  Tight gamma via
    eulerMascheroniSeq 63 (harmonic 63 - log 64); tight loglog via
    log 10080 >= 10log2+2log3 > 639/70, loglog >= log 639/70. -/
theorem robin_tight_n10080 :
    (39312 : ℝ) < Real.exp Real.eulerMascheroniConstant * (10080 : ℝ) * Real.log (Real.log (10080 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 63
  have hharm : (harmonic 63 : ℚ) = 310559566510213034489743057 / 65681493561267903750631200 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 63 = ((310559566510213034489743057 : ℝ) / 65681493561267903750631200) - Real.log 64 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((569 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((1766499 : ℝ) / 1000000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((1766499 : ℝ) / 1000000) ≤ Real.exp ((569 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (10 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 ≤ Real.log (10080 : ℝ) := by
    have h : Real.log ((9216 : ℝ)) ≤ Real.log (10080 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((9216 : ℝ)) = (10 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 := by
      rw [show ((9216 : ℝ)) = 2 ^ (10 : ℕ) * 3 ^ (2 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((639 : ℝ) / 70) ≤ Real.log (10080 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((639 : ℝ) / 70) ≤ Real.log (Real.log (10080 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 71 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 71 : ℝ) ^ (i + 1) / (i + 1)) = 4325465 / 304940172 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 71 : ℝ)| ^ (4 + 1) / (1 - |1 / 71|) = 1 / 1778817670 := by
    rw [show |(1 / 71 : ℝ)| = 1 / 71 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((2211409211 : ℝ) / 1000000000) ≤ Real.log ((639 : ℝ) / 70) := by
    have e : Real.log ((639 : ℝ) / 70) = (0 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 - Real.log (1 - 1 / 71 : ℝ) := by
      rw [show ((639 : ℝ) / 70) = 2 ^ (0 : ℕ) * 3 ^ (2 : ℕ) * (1 - 1 / 71)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((2211409211 : ℝ) / 1000000000) ≤ Real.log (Real.log (10080 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((1766499 : ℝ) / 1000000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2211409211 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (10080 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (39312 : ℝ) < ((1766499 : ℝ) / 1000000) * (10080 : ℝ) * ((2211409211 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (10080 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=15120 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(15120)=59520 < e^gamma * 15120 * log log 15120.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 15120 >= 9log2+3log3 > 162/17, loglog >= log 162/17. -/
theorem robin_tight_n15120 :
    (59520 : ℝ) < Real.exp Real.eulerMascheroniConstant * (15120 : ℝ) * Real.log (Real.log (15120 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (9 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 ≤ Real.log (15120 : ℝ) := by
    have h : Real.log ((13824 : ℝ)) ≤ Real.log (15120 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((13824 : ℝ)) = (9 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 := by
      rw [show ((13824 : ℝ)) = 2 ^ (9 : ℕ) * 3 ^ (3 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((162 : ℝ) / 17) ≤ Real.log (15120 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((162 : ℝ) / 17) ≤ Real.log (Real.log (15120 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 18 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 18 : ℝ) ^ (i + 1) / (i + 1)) = 24001 / 419904 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 18 : ℝ)| ^ (4 + 1) / (1 - |1 / 18|) = 1 / 1784592 := by
    rw [show |(1 / 18 : ℝ)| = 1 / 18 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((2254382319 : ℝ) / 1000000000) ≤ Real.log ((162 : ℝ) / 17) := by
    have e : Real.log ((162 : ℝ) / 17) = (0 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 - Real.log (1 - 1 / 18 : ℝ) := by
      rw [show ((162 : ℝ) / 17) = 2 ^ (0 : ℕ) * 3 ^ (2 : ℕ) * (1 - 1 / 18)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((2254382319 : ℝ) / 1000000000) ≤ Real.log (Real.log (15120 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2254382319 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (15120 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (59520 : ℝ) < ((219053 : ℝ) / 125000) * (15120 : ℝ) * ((2254382319 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (15120 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=25200 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(25200)=99944 < e^gamma * 25200 * log log 25200.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 25200 >= 13log2+1log3 > 10, loglog >= log 10. -/
theorem robin_tight_n25200 :
    (99944 : ℝ) < Real.exp Real.eulerMascheroniConstant * (25200 : ℝ) * Real.log (Real.log (25200 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (13 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 ≤ Real.log (25200 : ℝ) := by
    have h : Real.log ((24576 : ℝ)) ≤ Real.log (25200 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((24576 : ℝ)) = (13 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 := by
      rw [show ((24576 : ℝ)) = 2 ^ (13 : ℕ) * 3 ^ (1 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : (10 : ℝ) ≤ Real.log (25200 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log (10 : ℝ) ≤ Real.log (Real.log (25200 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 10 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 10 : ℝ) ^ (i + 1) / (i + 1)) = 12643 / 120000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 10 : ℝ)| ^ (4 + 1) / (1 - |1 / 10|) = 1 / 90000 := by
    rw [show |(1 / 10 : ℝ)| = 1 / 10 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((2302571799 : ℝ) / 1000000000) ≤ Real.log (10 : ℝ) := by
    have e : Real.log (10 : ℝ) = (0 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 - Real.log (1 - 1 / 10 : ℝ) := by
      rw [show (10 : ℝ) = 2 ^ (0 : ℕ) * 3 ^ (2 : ℕ) * (1 - 1 / 10)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((2302571799 : ℝ) / 1000000000) ≤ Real.log (Real.log (25200 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2302571799 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (25200 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (99944 : ℝ) < ((219053 : ℝ) / 125000) * (25200 : ℝ) * ((2302571799 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (25200 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=27720 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(27720)=112320 < e^gamma * 27720 * log log 27720.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 27720 >= 10log2+3log3 > 81/8, loglog >= log 81/8. -/
theorem robin_tight_n27720 :
    (112320 : ℝ) < Real.exp Real.eulerMascheroniConstant * (27720 : ℝ) * Real.log (Real.log (27720 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (10 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 ≤ Real.log (27720 : ℝ) := by
    have h : Real.log ((27648 : ℝ)) ≤ Real.log (27720 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((27648 : ℝ)) = (10 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 := by
      rw [show ((27648 : ℝ)) = 2 ^ (10 : ℕ) * 3 ^ (3 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((81 : ℝ) / 8) ≤ Real.log (27720 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((81 : ℝ) / 8) ≤ Real.log (Real.log (27720 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 9 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 9 : ℝ) ^ (i + 1) / (i + 1)) = 3091 / 26244 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 9 : ℝ)| ^ (4 + 1) / (1 - |1 / 9|) = 1 / 52488 := by
    rw [show |(1 / 9 : ℝ)| = 1 / 9 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((1157492413 : ℝ) / 500000000) ≤ Real.log ((81 : ℝ) / 8) := by
    have e : Real.log ((81 : ℝ) / 8) = (0 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 - Real.log (1 - 1 / 9 : ℝ) := by
      rw [show ((81 : ℝ) / 8) = 2 ^ (0 : ℕ) * 3 ^ (2 : ℕ) * (1 - 1 / 9)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((1157492413 : ℝ) / 500000000) ≤ Real.log (Real.log (27720 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((1157492413 : ℝ) / 500000000) := by norm_num
  have hn : (0 : ℝ) < (27720 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (112320 : ℝ) < ((219053 : ℝ) / 125000) * (27720 : ℝ) * ((1157492413 : ℝ) / 500000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (27720 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=55440 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(55440)=232128 < e^gamma * 55440 * log log 55440.  Tight gamma via
    eulerMascheroniSeq 63 (harmonic 63 - log 64); tight loglog via
    log 55440 >= 11log2+3log3 > 54/5, loglog >= log 54/5. -/
theorem robin_tight_n55440 :
    (232128 : ℝ) < Real.exp Real.eulerMascheroniConstant * (55440 : ℝ) * Real.log (Real.log (55440 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 63
  have hharm : (harmonic 63 : ℚ) = 310559566510213034489743057 / 65681493561267903750631200 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 63 = ((310559566510213034489743057 : ℝ) / 65681493561267903750631200) - Real.log 64 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((569 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((1766499 : ℝ) / 1000000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((1766499 : ℝ) / 1000000) ≤ Real.exp ((569 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (11 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 ≤ Real.log (55440 : ℝ) := by
    have h : Real.log ((55296 : ℝ)) ≤ Real.log (55440 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((55296 : ℝ)) = (11 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 := by
      rw [show ((55296 : ℝ)) = 2 ^ (11 : ℕ) * 3 ^ (3 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((54 : ℝ) / 5) ≤ Real.log (55440 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((54 : ℝ) / 5) ≤ Real.log (Real.log (55440 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 6 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 6 : ℝ) ^ (i + 1) / (i + 1)) = 35 / 192 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 6 : ℝ)| ^ (4 + 1) / (1 - |1 / 6|) = 1 / 6480 := by
    rw [show |(1 / 6 : ℝ)| = 1 / 6 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((1189680961 : ℝ) / 500000000) ≤ Real.log ((54 : ℝ) / 5) := by
    have e : Real.log ((54 : ℝ) / 5) = (0 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 - Real.log (1 - 1 / 6 : ℝ) := by
      rw [show ((54 : ℝ) / 5) = 2 ^ (0 : ℕ) * 3 ^ (2 : ℕ) * (1 - 1 / 6)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((1189680961 : ℝ) / 500000000) ≤ Real.log (Real.log (55440 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((1766499 : ℝ) / 1000000) := by norm_num
  have hLLpos : (0 : ℝ) < ((1189680961 : ℝ) / 500000000) := by norm_num
  have hn : (0 : ℝ) < (55440 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (232128 : ℝ) < ((1766499 : ℝ) / 1000000) * (55440 : ℝ) * ((1189680961 : ℝ) / 500000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (55440 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=110880 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(110880)=471744 < e^gamma * 110880 * log log 110880.  Tight gamma via
    eulerMascheroniSeq 63 (harmonic 63 - log 64); tight loglog via
    log 110880 >= 12log2+3log3 > 45/4, loglog >= log 45/4. -/
theorem robin_tight_n110880 :
    (471744 : ℝ) < Real.exp Real.eulerMascheroniConstant * (110880 : ℝ) * Real.log (Real.log (110880 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 63
  have hharm : (harmonic 63 : ℚ) = 310559566510213034489743057 / 65681493561267903750631200 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 63 = ((310559566510213034489743057 : ℝ) / 65681493561267903750631200) - Real.log 64 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((569 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((1766499 : ℝ) / 1000000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((1766499 : ℝ) / 1000000) ≤ Real.exp ((569 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (12 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 ≤ Real.log (110880 : ℝ) := by
    have h : Real.log ((110592 : ℝ)) ≤ Real.log (110880 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((110592 : ℝ)) = (12 : ℝ) * Real.log 2 + (3 : ℝ) * Real.log 3 := by
      rw [show ((110592 : ℝ)) = 2 ^ (12 : ℕ) * 3 ^ (3 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((45 : ℝ) / 4) ≤ Real.log (110880 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((45 : ℝ) / 4) ≤ Real.log (Real.log (110880 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 5 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 5 : ℝ) ^ (i + 1) / (i + 1)) = 1673 / 7500 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 5 : ℝ)| ^ (4 + 1) / (1 - |1 / 5|) = 1 / 2500 := by
    rw [show |(1 / 5 : ℝ)| = 1 / 5 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((2419891243 : ℝ) / 1000000000) ≤ Real.log ((45 : ℝ) / 4) := by
    have e : Real.log ((45 : ℝ) / 4) = (0 : ℝ) * Real.log 2 + (2 : ℝ) * Real.log 3 - Real.log (1 - 1 / 5 : ℝ) := by
      rw [show ((45 : ℝ) / 4) = 2 ^ (0 : ℕ) * 3 ^ (2 : ℕ) * (1 - 1 / 5)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((2419891243 : ℝ) / 1000000000) ≤ Real.log (Real.log (110880 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((1766499 : ℝ) / 1000000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2419891243 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (110880 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (471744 : ℝ) < ((1766499 : ℝ) / 1000000) * (110880 : ℝ) * ((2419891243 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (110880 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=166320 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(166320)=714240 < e^gamma * 166320 * log log 166320.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 166320 >= 11log2+4log3 > 1262/105, loglog >= log 1262/105. -/
theorem robin_tight_n166320 :
    (714240 : ℝ) < Real.exp Real.eulerMascheroniConstant * (166320 : ℝ) * Real.log (Real.log (166320 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (11 : ℝ) * Real.log 2 + (4 : ℝ) * Real.log 3 ≤ Real.log (166320 : ℝ) := by
    have h : Real.log ((165888 : ℝ)) ≤ Real.log (166320 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((165888 : ℝ)) = (11 : ℝ) * Real.log 2 + (4 : ℝ) * Real.log 3 := by
      rw [show ((165888 : ℝ)) = 2 ^ (11 : ℕ) * 3 ^ (4 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((1262 : ℝ) / 105) ≤ Real.log (166320 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((1262 : ℝ) / 105) ≤ Real.log (Real.log (166320 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 631 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 631 : ℝ) ^ (i + 1) / (i + 1)) = 3017266585 / 1902386183052 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 631 : ℝ)| ^ (4 + 1) / (1 - |1 / 631|) = 1 / 99875274610230 := by
    rw [show |(1 / 631 : ℝ)| = 1 / 631 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((621623173 : ℝ) / 250000000) ≤ Real.log ((1262 : ℝ) / 105) := by
    have e : Real.log ((1262 : ℝ) / 105) = (2 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 - Real.log (1 - 1 / 631 : ℝ) := by
      rw [show ((1262 : ℝ) / 105) = 2 ^ (2 : ℕ) * 3 ^ (1 : ℕ) * (1 - 1 / 631)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((621623173 : ℝ) / 250000000) ≤ Real.log (Real.log (166320 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((621623173 : ℝ) / 250000000) := by norm_num
  have hn : (0 : ℝ) < (166320 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (714240 : ℝ) < ((219053 : ℝ) / 125000) * (166320 : ℝ) * ((621623173 : ℝ) / 250000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (166320 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=277200 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(277200)=1199328 < e^gamma * 277200 * log log 277200.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 277200 >= 18log2+0log3 > 162/13, loglog >= log 162/13. -/
theorem robin_tight_n277200 :
    (1199328 : ℝ) < Real.exp Real.eulerMascheroniConstant * (277200 : ℝ) * Real.log (Real.log (277200 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (18 : ℝ) * Real.log 2 + (0 : ℝ) * Real.log 3 ≤ Real.log (277200 : ℝ) := by
    have h : Real.log ((262144 : ℝ)) ≤ Real.log (277200 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((262144 : ℝ)) = (18 : ℝ) * Real.log 2 + (0 : ℝ) * Real.log 3 := by
      rw [show ((262144 : ℝ)) = 2 ^ (18 : ℕ) * 3 ^ (0 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((162 : ℝ) / 13) ≤ Real.log (277200 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((162 : ℝ) / 13) ≤ Real.log (Real.log (277200 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 27 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 27 : ℝ) ^ (i + 1) / (i + 1)) = 80227 / 2125764 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 27 : ℝ)| ^ (4 + 1) / (1 - |1 / 27|) = 1 / 13817466 := by
    rw [show |(1 / 27 : ℝ)| = 1 / 27 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((252264689 : ℝ) / 100000000) ≤ Real.log ((162 : ℝ) / 13) := by
    have e : Real.log ((162 : ℝ) / 13) = (2 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 - Real.log (1 - 1 / 27 : ℝ) := by
      rw [show ((162 : ℝ) / 13) = 2 ^ (2 : ℕ) * 3 ^ (1 : ℕ) * (1 - 1 / 27)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((252264689 : ℝ) / 100000000) ≤ Real.log (Real.log (277200 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((252264689 : ℝ) / 100000000) := by norm_num
  have hn : (0 : ℝ) < (277200 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (1199328 : ℝ) < ((219053 : ℝ) / 125000) * (277200 : ℝ) * ((252264689 : ℝ) / 100000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (277200 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=332640 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(332640)=1451520 < e^gamma * 332640 * log log 332640.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 332640 >= 12log2+4log3 > 216/17, loglog >= log 216/17. -/
theorem robin_tight_n332640 :
    (1451520 : ℝ) < Real.exp Real.eulerMascheroniConstant * (332640 : ℝ) * Real.log (Real.log (332640 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (12 : ℝ) * Real.log 2 + (4 : ℝ) * Real.log 3 ≤ Real.log (332640 : ℝ) := by
    have h : Real.log ((331776 : ℝ)) ≤ Real.log (332640 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((331776 : ℝ)) = (12 : ℝ) * Real.log 2 + (4 : ℝ) * Real.log 3 := by
      rw [show ((331776 : ℝ)) = 2 ^ (12 : ℕ) * 3 ^ (4 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((216 : ℝ) / 17) ≤ Real.log (332640 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((216 : ℝ) / 17) ≤ Real.log (Real.log (332640 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 18 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 18 : ℝ) ^ (i + 1) / (i + 1)) = 24001 / 419904 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 18 : ℝ)| ^ (4 + 1) / (1 - |1 / 18|) = 1 / 1784592 := by
    rw [show |(1 / 18 : ℝ)| = 1 / 18 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((2542064391 : ℝ) / 1000000000) ≤ Real.log ((216 : ℝ) / 17) := by
    have e : Real.log ((216 : ℝ) / 17) = (2 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 - Real.log (1 - 1 / 18 : ℝ) := by
      rw [show ((216 : ℝ) / 17) = 2 ^ (2 : ℕ) * 3 ^ (1 : ℕ) * (1 - 1 / 18)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((2542064391 : ℝ) / 1000000000) ≤ Real.log (Real.log (332640 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2542064391 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (332640 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (1451520 : ℝ) < ((219053 : ℝ) / 125000) * (332640 : ℝ) * ((2542064391 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (332640 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=554400 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(554400)=2437344 < e^gamma * 554400 * log log 554400.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 554400 >= 0log2+12log3 > 144/11, loglog >= log 144/11. -/
theorem robin_tight_n554400 :
    (2437344 : ℝ) < Real.exp Real.eulerMascheroniConstant * (554400 : ℝ) * Real.log (Real.log (554400 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (0 : ℝ) * Real.log 2 + (12 : ℝ) * Real.log 3 ≤ Real.log (554400 : ℝ) := by
    have h : Real.log ((531441 : ℝ)) ≤ Real.log (554400 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((531441 : ℝ)) = (0 : ℝ) * Real.log 2 + (12 : ℝ) * Real.log 3 := by
      rw [show ((531441 : ℝ)) = 2 ^ (0 : ℕ) * 3 ^ (12 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((144 : ℝ) / 11) ≤ Real.log (554400 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((144 : ℝ) / 11) ≤ Real.log (Real.log (554400 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 12 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 12 : ℝ) ^ (i + 1) / (i + 1)) = 7217 / 82944 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 12 : ℝ)| ^ (4 + 1) / (1 - |1 / 12|) = 1 / 228096 := by
    rw [show |(1 / 12 : ℝ)| = 1 / 12 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((1285956389 : ℝ) / 500000000) ≤ Real.log ((144 : ℝ) / 11) := by
    have e : Real.log ((144 : ℝ) / 11) = (2 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 - Real.log (1 - 1 / 12 : ℝ) := by
      rw [show ((144 : ℝ) / 11) = 2 ^ (2 : ℕ) * 3 ^ (1 : ℕ) * (1 - 1 / 12)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((1285956389 : ℝ) / 500000000) ≤ Real.log (Real.log (554400 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((1285956389 : ℝ) / 500000000) := by norm_num
  have hn : (0 : ℝ) < (554400 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (2437344 : ℝ) < ((219053 : ℝ) / 125000) * (554400 : ℝ) * ((1285956389 : ℝ) / 500000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (554400 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=665280 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(665280)=2926080 < e^gamma * 665280 * log log 665280.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 665280 >= 13log2+4log3 > 40/3, loglog >= log 40/3. -/
theorem robin_tight_n665280 :
    (2926080 : ℝ) < Real.exp Real.eulerMascheroniConstant * (665280 : ℝ) * Real.log (Real.log (665280 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (13 : ℝ) * Real.log 2 + (4 : ℝ) * Real.log 3 ≤ Real.log (665280 : ℝ) := by
    have h : Real.log ((663552 : ℝ)) ≤ Real.log (665280 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((663552 : ℝ)) = (13 : ℝ) * Real.log 2 + (4 : ℝ) * Real.log 3 := by
      rw [show ((663552 : ℝ)) = 2 ^ (13 : ℕ) * 3 ^ (4 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((40 : ℝ) / 3) ≤ Real.log (665280 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((40 : ℝ) / 3) ≤ Real.log (Real.log (665280 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 10 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 10 : ℝ) ^ (i + 1) / (i + 1)) = 12643 / 120000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 10 : ℝ)| ^ (4 + 1) / (1 - |1 / 10|) = 1 / 90000 := by
    rw [show |(1 / 10 : ℝ)| = 1 / 10 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((2590253871 : ℝ) / 1000000000) ≤ Real.log ((40 : ℝ) / 3) := by
    have e : Real.log ((40 : ℝ) / 3) = (2 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 - Real.log (1 - 1 / 10 : ℝ) := by
      rw [show ((40 : ℝ) / 3) = 2 ^ (2 : ℕ) * 3 ^ (1 : ℕ) * (1 - 1 / 10)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((2590253871 : ℝ) / 1000000000) ≤ Real.log (Real.log (665280 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2590253871 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (665280 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (2926080 : ℝ) < ((219053 : ℝ) / 125000) * (665280 : ℝ) * ((2590253871 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (665280 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=720720 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(720720)=3249792 < e^gamma * 720720 * log log 720720.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 720720 >= 2log2+11log3 > 40/3, loglog >= log 40/3. -/
theorem robin_tight_n720720 :
    (3249792 : ℝ) < Real.exp Real.eulerMascheroniConstant * (720720 : ℝ) * Real.log (Real.log (720720 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (2 : ℝ) * Real.log 2 + (11 : ℝ) * Real.log 3 ≤ Real.log (720720 : ℝ) := by
    have h : Real.log ((708588 : ℝ)) ≤ Real.log (720720 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((708588 : ℝ)) = (2 : ℝ) * Real.log 2 + (11 : ℝ) * Real.log 3 := by
      rw [show ((708588 : ℝ)) = 2 ^ (2 : ℕ) * 3 ^ (11 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : ((40 : ℝ) / 3) ≤ Real.log (720720 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log ((40 : ℝ) / 3) ≤ Real.log (Real.log (720720 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 10 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 10 : ℝ) ^ (i + 1) / (i + 1)) = 12643 / 120000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 10 : ℝ)| ^ (4 + 1) / (1 - |1 / 10|) = 1 / 90000 := by
    rw [show |(1 / 10 : ℝ)| = 1 / 10 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((2590253871 : ℝ) / 1000000000) ≤ Real.log ((40 : ℝ) / 3) := by
    have e : Real.log ((40 : ℝ) / 3) = (2 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 - Real.log (1 - 1 / 10 : ℝ) := by
      rw [show ((40 : ℝ) / 3) = 2 ^ (2 : ℕ) * 3 ^ (1 : ℕ) * (1 - 1 / 10)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((2590253871 : ℝ) / 1000000000) ≤ Real.log (Real.log (720720 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((2590253871 : ℝ) / 1000000000) := by norm_num
  have hn : (0 : ℝ) < (720720 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (3249792 : ℝ) < ((219053 : ℝ) / 125000) * (720720 : ℝ) * ((2590253871 : ℝ) / 1000000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (720720 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

/-- Robin's inequality at n=1441440 (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:
    sigma(1441440)=6604416 < e^gamma * 1441440 * log log 1441440.  Tight gamma via
    eulerMascheroniSeq 31 (harmonic 31 - log 32); tight loglog via
    log 1441440 >= 3log2+11log3 > 14, loglog >= log 14. -/
theorem robin_tight_n1441440 :
    (6604416 : ℝ) < Real.exp Real.eulerMascheroniConstant * (1441440 : ℝ) * Real.log (Real.log (1441440 : ℝ)) := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hharm : (harmonic 31 : ℚ) = 290774257297357 / 72201776446800 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hval : Real.eulerMascheroniSeq 31 = ((290774257297357 : ℝ) / 72201776446800) - Real.log 32 := by
    unfold Real.eulerMascheroniSeq
    rw [hharm]; push_cast; norm_num
  rw [hval] at hseq
  have hlogp : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlogp] at hseq
  have hl2hi := Real.log_two_lt_d9
  have hgl : ((561 : ℝ) / 1000) < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]
  have hE : ((219053 : ℝ) / 125000) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hexp : ((219053 : ℝ) / 125000) ≤ Real.exp ((561 : ℝ) / 1000) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))
  have hl2lo := Real.log_two_gt_d9
  have hl3lo := Real.log_three_gt_d9
  have hlogn : (3 : ℝ) * Real.log 2 + (11 : ℝ) * Real.log 3 ≤ Real.log (1441440 : ℝ) := by
    have h : Real.log ((1417176 : ℝ)) ≤ Real.log (1441440 : ℝ) := by
      gcongr
      norm_num
    have e : Real.log ((1417176 : ℝ)) = (3 : ℝ) * Real.log 2 + (11 : ℝ) * Real.log 3 := by
      rw [show ((1417176 : ℝ)) = 2 ^ (3 : ℕ) * 3 ^ (11 : ℕ) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
    rwa [e] at h
  have hlognT : (14 : ℝ) ≤ Real.log (1441440 : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]
  have hll1 : Real.log (14 : ℝ) ≤ Real.log (Real.log (1441440 : ℝ)) := by gcongr
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 7 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 7 : ℝ) ^ (i + 1) / (i + 1)) = 4441 / 28812 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 7 : ℝ)| ^ (4 + 1) / (1 - |1 / 7|) = 1 / 14406 := by
    rw [show |(1 / 7 : ℝ)| = 1 / 7 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  have hlogT : ((1319487199 : ℝ) / 500000000) ≤ Real.log (14 : ℝ) := by
    have e : Real.log (14 : ℝ) = (2 : ℝ) * Real.log 2 + (1 : ℝ) * Real.log 3 - Real.log (1 - 1 / 7 : ℝ) := by
      rw [show (14 : ℝ) = 2 ^ (2 : ℕ) * 3 ^ (1 : ℕ) * (1 - 1 / 7)⁻¹ by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]
  have hLL : ((1319487199 : ℝ) / 500000000) ≤ Real.log (Real.log (1441440 : ℝ)) := le_trans hlogT hll1
  have hEpos : (0 : ℝ) < ((219053 : ℝ) / 125000) := by norm_num
  have hLLpos : (0 : ℝ) < ((1319487199 : ℝ) / 500000000) := by norm_num
  have hn : (0 : ℝ) < (1441440 : ℝ) := by norm_num
  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have harith : (6604416 : ℝ) < ((219053 : ℝ) / 125000) * (1441440 : ℝ) * ((1319487199 : ℝ) / 500000000) := by norm_num
  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,
    mul_le_mul hE (le_refl (1441440 : ℝ)) (le_of_lt hn) (le_of_lt hg),
    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]

end Robin

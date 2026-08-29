/- D3 batch: G-monotonicity reduction lemma + generalized tight SA certs (n=10080 b2=0 k=71; n=166320 b2=2 k=631). -/
import Mathlib
open scoped Real

/-- G-monotonicity reduction lemma (heart of the SA/CA reduction; proves nothing about RH). -/
theorem robin_G_monotone
    {sm sn m n : ℝ} (hsm : 0 ≤ sm / m)
    (habund : sn / n ≤ sm / m)
    (hLm : 0 < Real.log (Real.log m))
    (hLmn : Real.log (Real.log m) ≤ Real.log (Real.log n)) :
    sn / (n * Real.log (Real.log n)) ≤ sm / (m * Real.log (Real.log m)) := by
  rw [← div_div, ← div_div]
  gcongr

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

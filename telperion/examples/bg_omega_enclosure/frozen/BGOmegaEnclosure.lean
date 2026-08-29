/- Taylor-log + d9 wired into BG: the omega enclosure of R3Cert/Sweep.lean.
   omega = 3/11 log 3 - 5/11 log 2 - 2/11 log(1 - 1/24), enclosed in BG's /10000
   window via Mathlib's Real.log_{two,three}_d9 + a degree-4 Taylor bracket of
   log(1-1/24) (Real.abs_log_sub_add_sum_range_le).  Regenerated + kernel-checkable. -/
import Mathlib

namespace BGOmegaEnclosure

theorem bg_omega_enclosure :
    (-78 : ℝ) / 10000 < 3 / 11 * Real.log 3 - 5 / 11 * Real.log 2 - 2 / 11 * Real.log (1 - 1 / 24)
      ∧ 3 / 11 * Real.log 3 - 5 / 11 * Real.log 2 - 2 / 11 * Real.log (1 - 1 / 24) < (-77 : ℝ) / 10000 := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 24 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 24 : ℝ) ^ (i + 1) / (i + 1)) = 18827 / 442368 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 24 : ℝ)| ^ (4 + 1) / (1 - |1 / 24|) = 1 / 7630848 := by
    rw [show |(1 / 24 : ℝ)| = 1 / 24 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  refine ⟨by nlinarith [h2lo, h2hi, h3lo, h3hi, htay.1, htay.2],
    by nlinarith [h2lo, h2hi, h3lo, h3hi, htay.1, htay.2]⟩

end BGOmegaEnclosure

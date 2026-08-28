/- zeta-numerics: zeta(2) LANDED; zeta(3) conversion LANDED; need the correct
   partial-sum <= tsum lemma name (sum_le_tsum / Finset.sum_le_tsum both absent). -/
import Mathlib
open scoped Real

theorem riemannZeta_two_re_bounds :
    (3 : ℝ) / 2 < (riemannZeta 2).re ∧ (riemannZeta 2).re < 8 / 3 := by
  have h : riemannZeta 2 = ((π ^ 2 / 6 : ℝ) : ℂ) := by
    rw [riemannZeta_two]; push_cast; ring
  rw [h, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_three, Real.pi_pos]
  · nlinarith [Real.pi_lt_four, Real.pi_pos]

theorem riemannZeta_three_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

-- probe: the correct partial-sum <= tsum (and tail-split) lemma names
#check @le_tsum
#check @le_tsum'
#check @tsum_le_tsum
#check @Summable.sum_le_tsum
#check @sum_add_tsum_nat_add
#check @Summable.sum_add_tsum_nat_add
#check @tsum_eq_sum_add_tsum_nat_add
#check @Finset.sum_le_tsum

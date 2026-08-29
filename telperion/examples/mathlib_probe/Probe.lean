/- Tight upper bound zeta(3) < 5/4 (two-sided Apery with zeta(3) >= 9/8).
   Tail 1/(n+3)^3 <= g(n)-g(n+1) with g n = 1/(2(n+2)(n+3)); partial sums
   telescope to g 0 - g N <= 1/12; tsum_le_of_sum_range_le closes it. -/
import Mathlib
open scoped Real

theorem riemannZeta_three_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

theorem riemannZeta_three_re_le : (riemannZeta 3).re < 5 / 4 := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsplit := hf.sum_add_tsum_nat_add 3
  have h3 : (∑ i ∈ Finset.range 3, 1 / (i : ℝ) ^ 3) = 9 / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  set g : ℕ → ℝ := fun i => 1 / (2 * ((i : ℝ) + 2) * ((i : ℝ) + 3)) with hg
  have hterm : ∀ i : ℕ, 1 / ((i : ℝ) + 3) ^ 3 ≤ g i - g (i + 1) := by
    intro i
    have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    have h3' : ((i : ℝ) + 3) ≠ 0 := by positivity
    have h4 : ((i : ℝ) + 4) ≠ 0 := by positivity
    have e : g i - g (i + 1) = 1 / (((i : ℝ) + 2) * ((i : ℝ) + 3) * ((i : ℝ) + 4)) := by
      simp only [hg]; push_cast; field_simp; ring
    rw [e, div_le_div_iff (by positivity) (by positivity)]
    nlinarith [(by positivity : (0 : ℝ) ≤ (i : ℝ) + 3)]
  have htail : (∑' i : ℕ, 1 / ((i : ℝ) + 3) ^ 3) ≤ 1 / 12 := by
    apply tsum_le_of_sum_range_le
    intro N
    calc ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 3) ^ 3
        ≤ ∑ i ∈ Finset.range N, (g i - g (i + 1)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = g 0 - g N := Finset.sum_range_sub' g N
      _ ≤ 1 / 12 := by
          have hgN : (0 : ℝ) ≤ g N := by simp only [hg]; positivity
          simp only [hg] at hgN ⊢
          norm_num
          linarith [hgN]
  have hfinal : (∑' n : ℕ, 1 / (n : ℝ) ^ 3) = 9 / 8 + ∑' i : ℕ, 1 / ((i : ℝ) + 3) ^ 3 := by
    rw [← hsplit, h3]; congr 1
    refine tsum_congr (fun i => ?_); push_cast; ring
  rw [hfinal]; linarith [htail]

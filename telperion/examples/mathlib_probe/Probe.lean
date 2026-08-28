/- Landing genuine zeta-numerics lemmas in Mathlib v4.32.0.
   1: zeta(2) bounds (from pi^2/6)  -- LANDED (compiled clean).
   2: zeta(3) > 9/8  -- Apery's constant, NO closed form, via the Dirichlet
      series (zeta_eq_tsum_one_div_nat_cpow) + a 3-term partial sum. -/
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

/-- zeta(3) as a real Dirichlet series (each complex term is a nonneg real cast). -/
theorem riemannZeta_three_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

/-- Apery's constant zeta(3) exceeds 9/8 (no closed form; via a 3-term partial sum). -/
theorem riemannZeta_three_re_ge : (9 : ℝ) / 8 ≤ (riemannZeta 3).re := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  calc (9 : ℝ) / 8
      = ∑ n ∈ Finset.range 3, 1 / (n : ℝ) ^ 3 := by
        simp [Finset.sum_range_succ]; norm_num
    _ ≤ ∑' n, 1 / (n : ℝ) ^ 3 :=
        Finset.sum_le_tsum _ (fun i _ => by positivity) hsum

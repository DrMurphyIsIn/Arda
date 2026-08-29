/- zeta-numerics, landed in-kernel against Mathlib v4.32.0.
   zeta(2) bounds (from pi^2/6) and zeta(3) > 9/8 (Apery's constant, NO closed
   form) via the Dirichlet series zeta_eq_tsum_one_div_nat_cpow + a partial sum. -/
import Mathlib
open scoped Real

namespace ZetaNumerics

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

/-- Apery's constant zeta(3) exceeds 9/8 (no closed form; first 3 series terms). -/
theorem riemannZeta_three_re_ge : (9 : ℝ) / 8 ≤ (riemannZeta 3).re := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h3 : (∑ n ∈ Finset.range 3, 1 / (n : ℝ) ^ 3) = 9 / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  calc (9 : ℝ) / 8 = ∑ n ∈ Finset.range 3, 1 / (n : ℝ) ^ 3 := h3.symm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 3 :=
        hsum.sum_le_tsum (Finset.range 3) (fun i _ => by positivity)

/-- zeta(4) bounds from the exact value pi^4/90 and 3 < pi < 4. -/
theorem riemannZeta_four_re_bounds :
    (9 : ℝ) / 10 < (riemannZeta 4).re ∧ (riemannZeta 4).re < 128 / 45 := by
  have h : riemannZeta 4 = ((π ^ 4 / 90 : ℝ) : ℂ) := by
    rw [riemannZeta_four]; push_cast; ring
  rw [h, Complex.ofReal_re]
  have h9 : (9 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have h16 : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hp : (0 : ℝ) < π ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [h9, hp]
  · nlinarith [h16, hp]

/-- Apery's constant zeta(3) < 5/4 (tight two-sided with zeta(3) >= 9/8): the
    Dirichlet-series tail 1/(n+3)^3 <= g n - g(n+1) telescopes to g 0 = 1/12. -/
theorem riemannZeta_three_re_le : (riemannZeta 3).re < 5 / 4 := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsplit := hf.sum_add_tsum_nat_add 3
  have h3 : (∑ i ∈ Finset.range 3, 1 / (i : ℝ) ^ 3) = 9 / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  set g : ℕ → ℝ := fun i => 1 / (2 * ((i : ℝ) + 2) * ((i : ℝ) + 3)) with hg
  have hterm : ∀ i : ℕ, (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) ≤ g i - g (i + 1) := by
    intro i
    have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    have h3' : ((i : ℝ) + 3) ≠ 0 := by positivity
    have h4 : ((i : ℝ) + 4) ≠ 0 := by positivity
    have e : g i - g (i + 1) = 1 / (((i : ℝ) + 2) * ((i : ℝ) + 3) * ((i : ℝ) + 4)) := by
      simp only [hg]; push_cast; field_simp; ring
    have hfi : (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) = 1 / ((i : ℝ) + 3) ^ 3 := by push_cast; ring
    rw [hfi, e]
    apply one_div_le_one_div_of_le (by positivity)
    have hid : ((i : ℝ) + 3) ^ 3 - (((i : ℝ) + 2) * ((i : ℝ) + 3) * ((i : ℝ) + 4)) = (i : ℝ) + 3 := by
      ring
    nlinarith [hid, (by positivity : (0 : ℝ) ≤ (i : ℝ) + 3)]
  have htailsum : Summable (fun i : ℕ => 1 / (((i + 3 : ℕ)) : ℝ) ^ 3) :=
    (summable_nat_add_iff 3).mpr hf
  have htail : (∑' i : ℕ, 1 / (((i + 3 : ℕ)) : ℝ) ^ 3) ≤ 1 / 12 := by
    apply htailsum.tsum_le_of_sum_range_le
    intro N
    calc ∑ i ∈ Finset.range N, 1 / (((i + 3 : ℕ)) : ℝ) ^ 3
        ≤ ∑ i ∈ Finset.range N, (g i - g (i + 1)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = g 0 - g N := Finset.sum_range_sub' g N
      _ ≤ 1 / 12 := by
          have hg0 : g 0 = 1 / 12 := by simp only [hg]; norm_num
          have hgN : (0 : ℝ) ≤ g N := by simp only [hg]; positivity
          rw [hg0]; linarith [hgN]
  rw [← hsplit, h3]
  linarith [htail]

end ZetaNumerics

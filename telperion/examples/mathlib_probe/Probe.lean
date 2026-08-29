/- ZetaBoundCertificate emitter test: zeta(3) and zeta(5) two-sided bounds. -/
import Mathlib
open scoped Real

namespace ZetaBoundTest

/-- zeta(3) as a real Dirichlet series (each complex term a nonneg real cast). -/
theorem zeta_three_bound_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

/-- Two-sided bound  9/8 <= zeta(3) <= 13/8  (square-telescoping tail). -/
theorem zeta_three_bound :
    (9 : ℝ) / 8 ≤ (riemannZeta 3).re
      ∧ (riemannZeta 3).re ≤ (13 : ℝ) / 8 := by
  rw [zeta_three_bound_eq_ofReal, Complex.ofReal_re]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsplit := hf.sum_add_tsum_nat_add 3
  have hlead : (∑ i ∈ Finset.range 3, 1 / (i : ℝ) ^ 3) = (9 : ℝ) / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  set g : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2) with hg
  have hts : Summable (fun i : ℕ => 1 / (((i + 3 : ℕ)) : ℝ) ^ 3) :=
    (summable_nat_add_iff 3).mpr hf
  have hterm : ∀ i : ℕ, (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) ≤ g i - g (i + 1) := by
    intro i
    have hfi : (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) = 1 / ((i : ℝ) + 3) ^ 3 := by
      push_cast; ring
    have e : g i - g (i + 1) = 1 / (((i : ℝ) + 2) * ((i : ℝ) + 3)) := by
      simp only [hg]; push_cast; field_simp; ring
    rw [hfi, e]
    have hb : (1 : ℝ) ≤ (i : ℝ) + 3 := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have step1 : 1 / ((i : ℝ) + 3) ^ 3 ≤ 1 / ((i : ℝ) + 3) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right hb (by norm_num))
    have step2 : 1 / ((i : ℝ) + 3) ^ 2 ≤ 1 / (((i : ℝ) + 2) * ((i : ℝ) + 3)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [(by positivity : (0 : ℝ) ≤ (i : ℝ) + 2)])
    exact le_trans step1 step2
  have htail : (∑' i : ℕ, 1 / (((i + 3 : ℕ)) : ℝ) ^ 3) ≤ 1 / 2 := by
    apply hts.tsum_le_of_sum_range_le
    intro N
    calc ∑ i ∈ Finset.range N, 1 / (((i + 3 : ℕ)) : ℝ) ^ 3
        ≤ ∑ i ∈ Finset.range N, (g i - g (i + 1)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = g 0 - g N := Finset.sum_range_sub' g N
      _ ≤ 1 / 2 := by
          have hg0 : g 0 = 1 / 2 := by simp only [hg]; norm_num
          have hgN : (0 : ℝ) ≤ g N := by simp only [hg]; positivity
          rw [hg0]; linarith [hgN]
  refine ⟨?_, ?_⟩
  · calc (9 : ℝ) / 8 = ∑ i ∈ Finset.range 3, 1 / (i : ℝ) ^ 3 := hlead.symm
      _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := hf.sum_le_tsum (Finset.range 3) (fun i _ => by positivity)
  · rw [← hsplit, hlead]; linarith [htail]

/-- zeta(5) as a real Dirichlet series (each complex term a nonneg real cast). -/
theorem zeta_five_bound_eq_ofReal :
    riemannZeta 5 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 5 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (5 : ℂ) = ((5 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

/-- Two-sided bound  8051/7776 <= zeta(5) <= 10643/7776  (square-telescoping tail). -/
theorem zeta_five_bound :
    (8051 : ℝ) / 7776 ≤ (riemannZeta 5).re
      ∧ (riemannZeta 5).re ≤ (10643 : ℝ) / 7776 := by
  rw [zeta_five_bound_eq_ofReal, Complex.ofReal_re]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 5) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsplit := hf.sum_add_tsum_nat_add 4
  have hlead : (∑ i ∈ Finset.range 4, 1 / (i : ℝ) ^ 5) = (8051 : ℝ) / 7776 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  set g : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 3) with hg
  have hts : Summable (fun i : ℕ => 1 / (((i + 4 : ℕ)) : ℝ) ^ 5) :=
    (summable_nat_add_iff 4).mpr hf
  have hterm : ∀ i : ℕ, (1 / (((i + 4 : ℕ)) : ℝ) ^ 5) ≤ g i - g (i + 1) := by
    intro i
    have hfi : (1 / (((i + 4 : ℕ)) : ℝ) ^ 5) = 1 / ((i : ℝ) + 4) ^ 5 := by
      push_cast; ring
    have e : g i - g (i + 1) = 1 / (((i : ℝ) + 3) * ((i : ℝ) + 4)) := by
      simp only [hg]; push_cast; field_simp; ring
    rw [hfi, e]
    have hb : (1 : ℝ) ≤ (i : ℝ) + 4 := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have step1 : 1 / ((i : ℝ) + 4) ^ 5 ≤ 1 / ((i : ℝ) + 4) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right hb (by norm_num))
    have step2 : 1 / ((i : ℝ) + 4) ^ 2 ≤ 1 / (((i : ℝ) + 3) * ((i : ℝ) + 4)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [(by positivity : (0 : ℝ) ≤ (i : ℝ) + 3)])
    exact le_trans step1 step2
  have htail : (∑' i : ℕ, 1 / (((i + 4 : ℕ)) : ℝ) ^ 5) ≤ 1 / 3 := by
    apply hts.tsum_le_of_sum_range_le
    intro N
    calc ∑ i ∈ Finset.range N, 1 / (((i + 4 : ℕ)) : ℝ) ^ 5
        ≤ ∑ i ∈ Finset.range N, (g i - g (i + 1)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = g 0 - g N := Finset.sum_range_sub' g N
      _ ≤ 1 / 3 := by
          have hg0 : g 0 = 1 / 3 := by simp only [hg]; norm_num
          have hgN : (0 : ℝ) ≤ g N := by simp only [hg]; positivity
          rw [hg0]; linarith [hgN]
  refine ⟨?_, ?_⟩
  · calc (8051 : ℝ) / 7776 = ∑ i ∈ Finset.range 4, 1 / (i : ℝ) ^ 5 := hlead.symm
      _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 5 := hf.sum_le_tsum (Finset.range 4) (fun i _ => by positivity)
  · rw [← hsplit, hlead]; linarith [htail]

end ZetaBoundTest

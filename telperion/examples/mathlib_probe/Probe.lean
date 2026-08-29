/- General square-telescoping tail (works for ANY k>=2, tightness via M leading
   terms) -- the reusable pattern for a ZetaBoundCertificate emitter.
   Test instance: zeta(3), split at M=3, tail <= 1/2. -/
import Mathlib
open scoped Real

theorem riemannZeta_three_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

theorem zeta3_general :
    (9 : ℝ) / 8 ≤ (riemannZeta 3).re ∧ (riemannZeta 3).re ≤ 9 / 8 + 1 / 2 := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsplit := hf.sum_add_tsum_nat_add 3
  have h3 : (∑ i ∈ Finset.range 3, 1 / (i : ℝ) ^ 3) = 9 / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  have hts : Summable (fun i : ℕ => 1 / (((i + 3 : ℕ)) : ℝ) ^ 3) :=
    (summable_nat_add_iff 3).mpr hf
  set g : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2) with hg
  have hterm : ∀ i : ℕ, (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) ≤ g i - g (i + 1) := by
    intro i
    have hfi : (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) = 1 / ((i : ℝ) + 3) ^ 3 := by push_cast; ring
    have e : g i - g (i + 1) = 1 / (((i : ℝ) + 2) * ((i : ℝ) + 3)) := by
      simp only [hg]; push_cast; field_simp; ring
    rw [hfi, e]
    have step1 : 1 / ((i : ℝ) + 3) ^ 3 ≤ 1 / ((i : ℝ) + 3) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith [(by positivity : (0:ℝ) ≤ (i:ℝ)+3)]
    have step2 : 1 / ((i : ℝ) + 3) ^ 2 ≤ 1 / (((i : ℝ) + 2) * ((i : ℝ) + 3)) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith [(by positivity : (0:ℝ) ≤ (i:ℝ)+2)]
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
  · rw [← hsplit, h3]; have := tsum_nonneg (fun i : ℕ => (by positivity : (0:ℝ) ≤ 1 / (((i + 3 : ℕ)) : ℝ) ^ 3)); linarith
  · rw [← hsplit, h3]; linarith [htail]

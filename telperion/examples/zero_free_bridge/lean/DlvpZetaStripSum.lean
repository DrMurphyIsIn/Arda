/- PHASE 4 (dVP frontier, strip growth bound — brick 1: the σ<1 partial Dirichlet sum).

   For `s` in the critical strip (`0 < Re s < 1`), the truncated Dirichlet sum obeys the classical
   integral-test bound `‖∑_{n=1}^N n^{-s}‖ ≤ 1 + (N^{1-σ} - 1)/(1-σ)` (`σ = Re s`).  This is the first
   analytic brick of the `ζ = O(t)` strip growth bound (the input `zeta_sphere_bound` lacks on
   `Re ∈ [3/4,1)`), obtained from `zeta_trunc` by bounding its partial-sum head.

   Proof: `‖∑ n^{-s}‖ ≤ ∑ ‖n^{-s}‖ = ∑ n^{-σ}` (`norm_sum_le`, `Complex.norm_natCast_cpow_of_pos`),
   then the head term `n=1` (`=1`) is peeled off and the tail `∑_{n=2}^N n^{-σ}` is dominated by the
   integral `∫_1^N x^{-σ} dx = (N^{1-σ}-1)/(1-σ)` via `AntitoneOn.sum_le_integral_Ico` (`x^{-σ}`
   antitone since `-σ ≤ 0`) and `integral_rpow`.  conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

open Complex MeasureTheory intervalIntegral Finset

namespace ZeroFreeBridge

/-- **Bottom-peel + reindex of an `Icc 1 N` sum.**  `∑_{n=1}^N g n = g 1 + ∑_{i=1}^{N-1} g(i+1)`. -/
private lemma sum_Icc_peel {N : ℕ} (hN : 1 ≤ N) (g : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, g n = g 1 + ∑ i ∈ Finset.Ico 1 N, g (i + 1) := by
  rw [← Finset.add_sum_erase _ g (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩), Finset.Icc_erase_left]
  congr 1
  have hIoc : Finset.Ioc 1 N = Finset.Ico 2 (N + 1) := by
    ext z; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

/-- **Critical-strip partial Dirichlet sum bound.**  For `0 < Re s < 1`,
    `‖∑_{n=1}^N n^{-s}‖ ≤ 1 + (N^{1-Re s} - 1)/(1-Re s)`. -/
theorem norm_partial_sum_le_of_lt_one {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1 + ((N : ℝ) ^ (1 - s.re) - 1) / (1 - s.re) := by
  set f : ℝ → ℝ := fun x => x ^ (-s.re) with hf
  -- ‖∑ n^{-s}‖ ≤ ∑ ‖n^{-s}‖ = ∑ n^{-σ}
  have hnorm : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ ∑ n ∈ Finset.Icc 1 N, f (n : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    exact le_of_eq (by rw [Complex.norm_natCast_cpow_of_pos hn0, neg_re])
  -- x^{-σ} antitone on [1, N]
  have hanti : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le one_pos (by exact_mod_cast hx.1)
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  -- integral test on the shifted (tail) sum
  have hcmp := hanti.sum_le_integral_Ico hN
  have hint : ∫ x in ((1 : ℕ) : ℝ)..((N : ℕ) : ℝ), f x
      = ((N : ℝ) ^ (1 - s.re) - 1) / (1 - s.re) := by
    rw [hf, integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -s.re))]
    push_cast
    rw [show (-s.re + 1) = (1 - s.re) by ring, Real.one_rpow]
  -- peel the head term (= 1) and dominate the tail by the integral
  have hpeel := sum_Icc_peel hN (fun n => f (n : ℝ))
  have hf1 : f ((1 : ℕ) : ℝ) = 1 := by simp [hf, Real.one_rpow]
  rw [hpeel, hf1] at hnorm
  rw [hint] at hcmp
  linarith [hnorm, hcmp]

end ZeroFreeBridge

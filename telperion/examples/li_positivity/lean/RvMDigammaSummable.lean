/-
RvMDigammaSummable — Phase 2 brick 4 (part 2): summability of the digamma summands.

The per-factor log-derivatives `logDeriv (wFactor n) s = 1/(s+(n+1)) − 1/(n+1)` (RvMDigammaLogDeriv)
are summable: each is `−s/((s+n+1)(n+1)) = O(1/n²)`.  This is the `Summable` hypothesis feeding
`logDeriv_tprod_eq_tsum` in the b4 assembly.  conjecture1_proved = False.
-/
import Mathlib
import RvMDigammaLogDeriv

open Complex

namespace RvMWeierstrass

set_option maxHeartbeats 2000000 in
/-- **Summability of the digamma summands.**  `∑_n (1/(s+(n+1)) − 1/(n+1))` converges;
    each term is `−s/((s+n+1)(n+1)) = O(1/n²)`. -/
theorem summable_logDeriv_wFactor {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    Summable (fun n : ℕ => logDeriv (wFactor n) s) := by
  have hterm : ∀ n : ℕ, logDeriv (wFactor n) s = 1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1) := by
    intro n
    have h : s + ((n : ℂ) + 1) ≠ 0 := by have := hs (n + 1); push_cast at this; exact this
    exact logDeriv_wFactor h
  rw [summable_congr hterm]
  apply Summable.of_norm_bounded_eventually_nat (g := fun n => ‖(2 * ‖s‖ : ℝ) / ((n : ℝ) + 1) ^ 2‖)
  · simpa only [Nat.cast_one] using summable_pow_div_add (2 * ‖s‖ : ℝ) 2 1 (by norm_num)
  · filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (2 * ‖s‖))] with n hn
    have hden : ((n : ℂ) + 1) ≠ 0 := natCast_add_one_ne_zero n
    have hnum : s + ((n : ℂ) + 1) ≠ 0 := by have := hs (n + 1); push_cast at this; exact this
    have hdiff : 1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)
        = -s / ((s + ((n : ℂ) + 1)) * ((n : ℂ) + 1)) := by
      rw [div_sub_div _ _ hnum hden, one_mul, mul_one]; congr 1; ring
    have hnb : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ)) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (2 * ‖s‖ : ℝ) ≤ (n : ℝ) + 1 := by
      have : (2 * ‖s‖ : ℝ) ≤ n := Nat.ceil_le.mp hn
      linarith
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖s + ((n : ℂ) + 1)‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖s‖ ≤ ‖s + ((n : ℂ) + 1)‖ := by
        have h2 := norm_sub_norm_le ((n : ℂ) + 1) (-s)
        rw [norm_neg, sub_neg_eq_add, add_comm ((n : ℂ) + 1) s] at h2
        exact h2
      rw [hnb] at h1; linarith
    have hposa : (0 : ℝ) < ‖s + ((n : ℂ) + 1)‖ := by nlinarith [hpos1]
    have hval : ‖1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)‖
        = ‖s‖ / (‖s + ((n : ℂ) + 1)‖ * ((n : ℝ) + 1)) := by
      rw [hdiff]; simp only [norm_div, norm_neg, norm_mul, hnb]
    rw [hval, Real.norm_of_nonneg (by positivity),
      div_le_div_iff₀ (mul_pos hposa hpos1) (by positivity)]
    have hs0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hlow hs0, hposa, hpos1, hn2, hs0]

end RvMWeierstrass

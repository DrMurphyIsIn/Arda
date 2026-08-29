/- Rung 3 (elegant, general s): per-term nonnegativity via the Mertens certificate. -/
import Mathlib
open scoped Real

theorem mertens_three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h := Real.cos_two_mul θ; nlinarith [h, sq_nonneg (Real.cos θ + 1)]

/-- Re(n^{-s}) = n^{-Re s} · cos(Im s · log n). -/
theorem cpow_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (((n : ℂ)) ^ (-s)).re = (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).re = -s.re * Real.log n := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  have him : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).im = -(s.im * Real.log n) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.exp_re, hre, him,
      Real.cos_neg, show -s.re * Real.log (n : ℝ) = Real.log (n : ℝ) * -s.re from by ring,
      ← Real.rpow_def_of_pos hnpos]

/-- Re of the vonMangoldt L-series term. -/
theorem term_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.re_ofReal_mul, cpow_re n hn s, mul_assoc]

/-- Per-term nonnegativity: the 3-4-1 combination of L-series terms is >= 0. -/
theorem term_comb_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ 3 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 4 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (2 * (t : ℂ)) * Complex.I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [LSeries.term]
  · have hn : 1 ≤ n := hpos
    rw [term_re n hn (σ : ℂ), term_re n hn ((σ : ℂ) + (t : ℂ) * Complex.I),
        term_re n hn ((σ : ℂ) + (2 * (t : ℂ)) * Complex.I)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_mul,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, Real.cos_zero]
    have hp : (0:ℝ) < (n:ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hM : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-σ) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hp.le
    nlinarith [mul_nonneg hM (mertens_three_four_one (t * Real.log n)), hM,
      Real.cos_le_one (t * Real.log n), Real.cos_le_one (2 * t * Real.log n)]

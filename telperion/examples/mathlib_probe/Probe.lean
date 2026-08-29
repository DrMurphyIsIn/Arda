/- Rung 2: Re(LSeries.term Λ (σ+it) n) = Λ(n) n^{-σ} cos(t log n), using the crux. -/
import Mathlib
open scoped Real
open Complex (I)

#check @LSeries.term_of_ne_zero
#check @Complex.re_ofReal_mul
#check @Complex.cpow_neg

theorem cpow_re (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * I))).re = (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : ((↑(Real.log (n : ℝ)) : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))).re = -σ * Real.log n := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have him : ((↑(Real.log (n : ℝ)) : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))).im = -(t * Real.log n) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.exp_re, hre, him,
      Real.cos_neg, show -σ * Real.log (n : ℝ) = Real.log (n : ℝ) * -σ from by ring,
      ← Real.rpow_def_of_pos hnpos]

theorem term_re (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : n ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul,
      cpow_re n hn σ t, mul_assoc]

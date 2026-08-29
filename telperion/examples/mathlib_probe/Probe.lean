/- Rung 3: per-term nonnegativity -- the Mertens certificate meets -zeta'/zeta, per term. -/
import Mathlib
open scoped Real
open Complex (I)

theorem mertens_three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h := Real.cos_two_mul θ; nlinarith [h, sq_nonneg (Real.cos θ + 1)]

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
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.re_ofReal_mul, cpow_re n hn σ t, mul_assoc]

theorem term_comb_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ 3 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (0 : ℂ) * I) n).re
      + 4 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n).re
      + (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [LSeries.term]
  · have hn : 1 ≤ n := hpos
    rw [show ((0:ℝ):ℂ) = ((0:ℝ):ℂ) from rfl] -- keep shape
    rw [term_re n hn σ 0, term_re n hn σ t, term_re n hn σ (2 * t),
        show (0:ℝ) * Real.log n = 0 by ring, Real.cos_zero,
        show (2 * t) * Real.log n = 2 * (t * Real.log n) by ring]
    have hp : (0:ℝ) < (n:ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hM : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-σ) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hp.le
    nlinarith [mul_nonneg hM (mertens_three_four_one (t * Real.log n)), hM]

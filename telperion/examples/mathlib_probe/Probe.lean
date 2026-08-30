/- PROBE: the ZETA corollary of the bridge -- restate the Mertens positivity literally
   about zeta's log-derivative -zeta'/zeta, via LSeries_vonMangoldt_eq_deriv_riemannZeta_div. -/
import Mathlib
open scoped Real

-- (existing, proven) the abstract-Dirichlet-series bridge, minimal re-statement:
theorem mertens_three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h := Real.cos_two_mul θ; nlinarith [h, sq_nonneg (Real.cos θ + 1)]

theorem cpow_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (((n : ℂ)) ^ (-s)).re = (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).re = -s.re * Real.log n := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have him : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).im = -(s.im * Real.log n) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.exp_re, hre, him,
      Real.cos_neg, show -s.re * Real.log (n : ℝ) = Real.log (n : ℝ) * -s.re from by ring,
      ← Real.rpow_def_of_pos hnpos]

theorem term_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.re_ofReal_mul, cpow_re n hn s, mul_assoc]

theorem term_comb_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ 3 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 4 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [LSeries.term]
  · have hn : 1 ≤ n := hpos
    rw [term_re n hn (σ : ℂ), term_re n hn ((σ : ℂ) + (t : ℂ) * Complex.I),
        term_re n hn ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, Real.cos_zero]
    rw [mul_assoc (2 : ℝ) t (Real.log (n : ℝ))]
    have hp : (0:ℝ) < (n:ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hM : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-σ) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hp.le
    nlinarith [mul_nonneg hM (mertens_three_four_one (t * Real.log n)), hM]

theorem vonMangoldt_re_comb_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)).re
      + 4 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have hf : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hg : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hh : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hA : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re) := hf.map Complex.reCLM Complex.reCLM.cont
  have hB : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re) := hg.map Complex.reCLM Complex.reCLM.cont
  have hC : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re) := hh.map Complex.reCLM Complex.reCLM.cont
  show 0 ≤ 3 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 4 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re
  rw [Complex.re_tsum hf, Complex.re_tsum hg, Complex.re_tsum hh,
      (((hA.hasSum.mul_left 3).add (hB.hasSum.mul_left 4)).add hC.hasSum).tsum_eq.symm]
  exact tsum_nonneg (fun n => term_comb_nonneg n σ t)

/- THE NEW RUNG: the same positivity, literally about zeta's log-derivative -zeta'/zeta. -/
theorem zeta_logDeriv_comb_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have e1 : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e2 : -deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e3 : -deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  rw [e1, e2, e3]
  exact vonMangoldt_re_comb_nonneg σ t hσ

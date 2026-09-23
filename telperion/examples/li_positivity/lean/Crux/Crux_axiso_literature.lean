/-
  Crux_axiso_literature.lean

  Build of the literature scout "RH for class P (degree-1 functional equation + positive
  Lambda_F). With integer frequencies class P is just {zeta}; the Beurling version is open."

  conjecture1_proved = False.  Nothing in this file bears on the Riemann Hypothesis or on
  conjecture1.  Everything here is either a certificate that some hypothesis is load-bearing
  (a negative control) or an elementary fragment of a paper argument.

  Checked with
    cd telperion/examples/li_positivity/lean && leanlock.sh lake env lean Crux/Crux_axiso_literature.lean
  (Lean v4.34.0-rc1, Mathlib de5ce8a9).  No `sorry`, no `admit`, no `native_decide`,
  no `axiom`, no `opaque`.  `#print axioms` at the end of the file.

  ESTABLISHES (kernel-checked):

  (A) Negative control  F(s) = zeta(s) * P(s),  P(s) = 1 + 4*2^{-s} + 2*4^{-s}.
      A1 `LSeries_coefF`: for Re s > 1, F is the Dirichlet series with coefficients
         a(n) = 1, 5, 7 according as v_2(n) = 0, 1, >= 2 (`coefF_eq`, `one_le_coefF`);
         `coefFA_isMultiplicative`: a is multiplicative (formal Euler product).
      A2 `Pfac_fe`: degree-0 FE 2^s P(s) = 2^{1-s} P(1-s);
         `LambdaF_one_sub`: Lambda_F(1-s) = Lambda_F(s), Lambda_F := 2^s P(s) Lambda_zeta(s);
         `LambdaF_eq`: Lambda_F(s) = 4^{s/2} Gamma_R(s) F(s) when Gamma_R(s) != 0;
         `completedF_fe`: the zeta-shape FE with conductor 4 and root number +1.
      A3 `negControl_zeros`: for every k in Z the point
         s_k = log_2(2+sqrt2) + i(2k+1)pi/log 2 has 2^{-s_k} = -1 + sqrt2/2,
         F(s_k) = 0, zeta(s_k) != 0, Re s_k > 1, the absolutely convergent Dirichlet series
         sum a(n) n^{-s_k} (coefficients in {1,5,7}) is 0, and Lambda_F vanishes at s_k and at
         1 - s_k (Re < 0): zeros off the critical line, even a zero in sigma > 1.
      A4 `vonMangoldtF_two_pow`: any L solving sum_{d|n} L(d) a(n/d) = a(n) log n (the
         defining identity of Lambda_F, i.e. -F'/F = sum L(n) n^{-s}) at n = 1,2,4,8,16 has
         L(2^k)/log 2 = 5, -11, 41, -135.  So P2 (Lambda_F >= 0) fails at n = 4.
         `vonMangoldtF_of_logDeriv`: the same values (k <= 2) for ANY Lambda whose L-series
         converges somewhere and equals -F'/F at all large real x (analytic definition).
  (B) Davenport-Heilbronn-type q = 5 mixture  a*zeta(s)(1 + sqrt5*5^{-s}) + b*L(s, chi_5),
      normalized a + b = 1 (coefficients `coefDH`; `chi5_eq_jacobiSym`: chi_5 is the Legendre
      symbol mod 5; `LSeries_coefDH`: coefDH is the coefficient sequence of the mixture, with
      L(s, chi_5) Mathlib's `DirichletCharacter.LFunction` of the quadratic character `chi5D`).
      `coefDH_nonneg`: coefficients >= 0 when |b| <= a;
      `vonMangoldtDH_36`: Lambda(4) = (2-(a-b)^2) log 2, Lambda(6) = 4ab log 6,
         Lambda(12) = -4ab(a-b) log 12, Lambda(36) = -4ab(1-3(a-b)^2) log 6;
      `vonMangoldtDH_42`: Lambda(42) = -8ab(a-b) log 42 (the scout's third cumulant);
      `vonMangoldtDH_546`: at a = b = 1/2, Lambda(546) = -2 log 546 (fourth cumulant);
      `dhMixture_P2_fails`: for every a >= |b| > 0 some n in {6, 12, 36} has Lambda(n) < 0
         (`dhMixture_P2_fails_squarefree`: the same with the scout's witnesses {6, 42, 546});
      `cumulant_pm_one`: the ring identities kappa_2 = 4ab, kappa_3 = -8ab(a-b), kappa_4 formula.
  (C) E8 normalization witness  G(s) = zeta(s/2 + 7/4) zeta(s/2 - 5/4).
      `LambdaG_one_sub`: Gamma_C(s/2+7/4) G(s) is invariant under s -> 1-s (s/2 + 7/4 not in Z);
      `Gammaℂ_shift`: Gamma_C(s/2+7/4) = 2(2pi)^{-7/4} (2pi)^{-s/2} Gamma(s/2+7/4);
      `GE8_ne_zero_on_critical_line`: G(1/2 + it) != 0 for every real t;
      `GE8_zero_of_zeta_zero`: each zeta-zero rho with 0 < Re rho < 1 gives zeros of G at
      2rho + 5/2 (5/2 < Re < 9/2) and at the mirror point 1 - (2rho + 5/2) (Re < -3/2);
      `GE8_eulerProduct`: G is a product of two Euler products for Re s > 9/2.
  (D) Elementary fragments of the paper sketches.
      `theta_eq_zero_of_nonneg_twist`: if n^{-i theta} is a nonnegative real for every
      n = 1 mod q, then theta = 0 (only n = q+1 and n = 2q+1 are used; step (1) of the
      collapse sketch, after Kaczorowski-Perelli's periodicity theorem);
      `den_eq_one_of_bounded_denominators`: a rational all of whose powers have denominators
      dividing a fixed D is an integer (last step of the uniformly-discrete argument);
      `rat_integral_is_int`: a rational algebraic integer is an integer (K = Q branch of the
      Kahane-Mandelbrojt order argument).

  DOES NOT ESTABLISH:
    * the collapse theorem (F in S^#_1, a(1) = 1, Lambda_F >= 0  ==>  F = zeta).  That is a
      paper sketch.  It rests on Kaczorowski-Perelli (Acta Math 1999) Thm 2, Pringsheim, the
      Polya-Ritt theorem (a zero-free exponential polynomial has one term) and Landau's
      theorem, none of which is formalized here;
    * Hamburger's theorem, the KP classification of S^#_1, Lev-Olevskii, Kahane-Mandelbrojt;
    * any zero of the q = 5 mixture.  Zeros in sigma > 1 (Bohr / Davenport-Heilbronn
      argument) are certified nowhere in this build; off-line zeros in 1/2 < sigma < 1 at
      height ~61 are Arb-certified (not kernel) in telperion/research/axiso_literature/;
    * the existence of a zeta-zero in the critical strip: the off-line zeros of G in (C) are
      conditional on one (the first zero is Arb-certified in research/axiso_literature/);
    * the functional equation of L(s, chi_5) (root number of the quadratic character);
    * positivity (P2) of G in the Beurling frequencies sqrt n (elementary; README);
    * anything about RH or conjecture1.
-/

import Mathlib

open Complex
open scoped LSeries.notation

namespace CruxAxisoLiterature

/-! ## (A) The negative control `F(s) = ζ(s)·(1 + 4·2^{-s} + 2·4^{-s})` -/

/-- The degree-0 factor `P(s) = 1 + 4·2^{-s} + 2·4^{-s}`. -/
noncomputable def Pfac (s : ℂ) : ℂ := 1 + 4 * (2 : ℂ) ^ (-s) + 2 * (4 : ℂ) ^ (-s)

/-- The negative control `F(s) = ζ(s)·P(s)`. -/
noncomputable def Fneg (s : ℂ) : ℂ := riemannZeta s * Pfac s

/-- The completed negative control `Λ_F(s) = 2^s·P(s)·Λ_ζ(s)`. -/
noncomputable def LambdaF (s : ℂ) : ℂ := (2 : ℂ) ^ s * Pfac s * completedRiemannZeta s

lemma four_cpow (s : ℂ) : (4 : ℂ) ^ s = (2 : ℂ) ^ s * (2 : ℂ) ^ s := by
  have h := natCast_mul_natCast_cpow 2 2 s
  push_cast at h
  norm_num at h
  exact h

lemma two_cpow_ne_zero (s : ℂ) : (2 : ℂ) ^ s ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff]; norm_num

lemma Pfac_eq (s : ℂ) : Pfac s = 1 + 4 * ((2 : ℂ) ^ s)⁻¹ + 2 * (((2 : ℂ) ^ s)⁻¹) ^ 2 := by
  rw [Pfac, cpow_neg, cpow_neg, four_cpow]; ring

lemma Pfac_eq_x (s : ℂ) : Pfac s = 1 + 4 * (2 : ℂ) ^ (-s) + 2 * ((2 : ℂ) ^ (-s)) ^ 2 := by
  rw [Pfac, four_cpow]; ring

/-- The degree-0 functional equation of the factor: `2^s P(s) = 2^{1-s} P(1-s)`
(so `4^{s/2} P(s)` is invariant under `s ↦ 1 - s`: conductor 4, root number +1). -/
theorem Pfac_fe (s : ℂ) : (2 : ℂ) ^ s * Pfac s = (2 : ℂ) ^ (1 - s) * Pfac (1 - s) := by
  have hy := two_cpow_ne_zero s
  have h1 : (2 : ℂ) ^ (1 - s) = 2 * ((2 : ℂ) ^ s)⁻¹ := by
    rw [cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0), cpow_one, div_eq_mul_inv]
  rw [Pfac_eq, Pfac_eq, h1]
  field_simp
  ring

/-- Functional equation of the completed negative control: `Λ_F(1 - s) = Λ_F(s)`. -/
theorem LambdaF_one_sub (s : ℂ) : LambdaF (1 - s) = LambdaF s := by
  unfold LambdaF
  rw [completedRiemannZeta_one_sub, ← Pfac_fe s]

/-- `Λ_F(s) = 4^{s/2}·Γ_ℝ(s)·F(s)` (the zeta-shape completion, `Γ_ℝ(s) = π^{-s/2}Γ(s/2)`). -/
theorem LambdaF_eq {s : ℂ} (hs : Gammaℝ s ≠ 0) :
    (4 : ℂ) ^ (s / 2) * Gammaℝ s * Fneg s = LambdaF s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩)
  have h4 : (4 : ℂ) ^ (s / 2) = (2 : ℂ) ^ s := by
    rw [four_cpow, ← cpow_add _ _ (two_ne_zero), add_halves]
  unfold Fneg LambdaF
  rw [riemannZeta_def_of_ne_zero hs0, h4]
  field_simp

/-- The functional equation of `F` in zeta shape: `(4/π)^{s/2} Γ(s/2) F(s)` is symmetric under
`s ↦ 1 - s` (conductor 4, root number `+1`), away from the poles of `Γ_ℝ`. -/
theorem completedF_fe {s : ℂ} (hs : Gammaℝ s ≠ 0) (hs' : Gammaℝ (1 - s) ≠ 0) :
    (4 : ℂ) ^ ((1 - s) / 2) * Gammaℝ (1 - s) * Fneg (1 - s) =
      (4 : ℂ) ^ (s / 2) * Gammaℝ s * Fneg s := by
  rw [LambdaF_eq hs, LambdaF_eq hs', LambdaF_one_sub]

/-! ### A1: the Dirichlet coefficients `1, 5, 7` and the Euler product -/

/-- Dirichlet coefficients of `F`: `a(n) = 1 + 4·[2 ∣ n] + 2·[4 ∣ n]`. -/
def coefF (n : ℕ) : ℕ := 1 + (if 2 ∣ n then 4 else 0) + (if 4 ∣ n then 2 else 0)

theorem coefF_eq (n : ℕ) : coefF n = if 4 ∣ n then 7 else if 2 ∣ n then 5 else 1 := by
  unfold coefF
  by_cases h4 : 4 ∣ n
  · have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
    simp [h4, h2]
  · by_cases h2 : 2 ∣ n <;> simp [h4, h2]

theorem one_le_coefF (n : ℕ) : 1 ≤ coefF n := by unfold coefF; omega

theorem coefF_le_seven (n : ℕ) : coefF n ≤ 7 := by
  unfold coefF; split_ifs <;> omega

/-- The finitely supported factor `c = δ₁ + 4δ₂ + 2δ₄`, whose L-series is `P`. -/
noncomputable def cfac (n : ℕ) : ℂ :=
  (if n = 1 then 1 else 0) + (if n = 2 then 4 else 0) + (if n = 4 then 2 else 0)

lemma one_conv_cfac {n : ℕ} (hn : n ≠ 0) : ((1 : ℕ → ℂ) ⍟ cfac) n = (coefF n : ℂ) := by
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, one_mul]
  have h : ∑ p ∈ n.divisorsAntidiagonal, cfac p.2 = ∑ d ∈ n.divisors, cfac d :=
    Nat.sum_divisorsAntidiagonal' (fun _ b => cfac b)
  rw [h]
  simp only [cfac, Finset.sum_add_distrib, Finset.sum_ite_eq', Nat.mem_divisors]
  simp only [coefF, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero]
  simp [hn]

lemma term_cfac_eq_zero (s : ℂ) (b : ℕ) (hb : b ∉ ({1, 2, 4} : Finset ℕ)) :
    LSeries.term cfac s b = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  obtain ⟨h1, h2, h4⟩ := hb
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  · rw [LSeries.term_of_ne_zero hb0]
    simp [cfac, h1, h2, h4]

lemma LSeriesSummable_cfac (s : ℂ) : LSeriesSummable cfac s :=
  summable_of_ne_finset_zero (term_cfac_eq_zero s)

lemma LSeries_cfac (s : ℂ) : LSeries cfac s = Pfac s := by
  rw [LSeries, tsum_eq_sum (term_cfac_eq_zero s)]
  simp [LSeries.term, cfac, Pfac, cpow_neg, div_eq_mul_inv]
  ring

/-- For `Re s > 1`, `F(s)` is the Dirichlet series `∑ a(n) n^{-s}` with `a(n) ∈ {1, 5, 7}`. -/
theorem LSeries_coefF {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (coefF n : ℂ)) s = Fneg s := by
  have h1 : LSeries (fun n => (coefF n : ℂ)) s = LSeries ((1 : ℕ → ℂ) ⍟ cfac) s :=
    LSeries_congr (fun hn => (one_conv_cfac hn).symm) s
  rw [h1, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs) (LSeriesSummable_cfac s),
    LSeries_one_eq_riemannZeta hs, LSeries_cfac]
  rfl

lemma LSeriesSummable_coefF {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coefF n : ℂ)) s := by
  have h := (LSeriesSummable_one_iff.mpr hs).convolution (LSeriesSummable_cfac s)
  exact (LSeriesSummable_congr s (fun hn => (one_conv_cfac hn).symm)).mpr h

lemma abscissa_coefF_le : LSeries.abscissaOfAbsConv (fun n => (coefF n : ℂ)) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := fun n => (coefF n : ℂ)) (x := 1)
    (fun y hy => LSeriesSummable_coefF (by simpa using hy))
  exact_mod_cast this

/-- The coefficients as an arithmetic function (value `0` at `0`). -/
def coefFA : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else coefF n
  map_zero' := rfl

lemma coefF_mul_of_odd {m n : ℕ} (hm : ¬ 2 ∣ m) : coefF (m * n) = coefF n := by
  have hc2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
  have hc4 : Nat.Coprime 4 m := by
    have := Nat.Coprime.pow_left 2 hc2
    norm_num at this
    exact this
  unfold coefF
  simp only [Nat.Coprime.dvd_mul_left hc2, Nat.Coprime.dvd_mul_left hc4]

lemma coefF_of_odd {m : ℕ} (hm : ¬ 2 ∣ m) : coefF m = 1 := by
  have h4 : ¬ 4 ∣ m := fun h => hm (dvd_trans (by norm_num) h)
  simp [coefF, hm, h4]

/-- The coefficients are multiplicative: `F` has an Euler product (local factor at 2 equal to
`(1 + 4x + 2x²)/(1 - x)`, `x = 2^{-s}`; local factor `(1 - p^{-s})^{-1}` at odd `p`). -/
theorem coefFA_isMultiplicative : ArithmeticFunction.IsMultiplicative coefFA := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by decide, ?_⟩
  intro m n hm hn hmn
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  show (if m * n = 0 then 0 else coefF (m * n)) =
    (if m = 0 then 0 else coefF m) * (if n = 0 then 0 else coefF n)
  simp only [hmn0, hm, hn, ↓reduceIte]
  by_cases h2m : 2 ∣ m
  · have h2n : ¬ 2 ∣ n := by
      intro h2n
      have := Nat.dvd_gcd h2m h2n
      rw [hmn] at this
      omega
    rw [mul_comm m n, coefF_mul_of_odd h2n, coefF_of_odd h2n, mul_one]
  · rw [coefF_mul_of_odd h2m, coefF_of_odd h2m, one_mul]

/-! ### A3: the exact zeros `s_k` -/

/-- The zero family `s_k = log_2(2 + √2) + i(2k+1)π / log 2`. -/
noncomputable def sZero (k : ℤ) : ℂ :=
  ((Real.log (2 + Real.sqrt 2) / Real.log 2 : ℝ) : ℂ) +
    (((2 * k + 1) * Real.pi / Real.log 2 : ℝ) : ℂ) * I

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem sZero_re (k : ℤ) : (sZero k).re = Real.log (2 + Real.sqrt 2) / Real.log 2 := by
  simp only [sZero, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]
  ring

theorem sZero_im (k : ℤ) : (sZero k).im = (2 * k + 1) * Real.pi / Real.log 2 := by
  simp only [sZero, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]
  ring

theorem one_lt_sZero_re (k : ℤ) : 1 < (sZero k).re := by
  rw [sZero_re, one_lt_div log_two_pos']
  apply Real.log_lt_log (by norm_num)
  have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

theorem sZero_im_ne_zero (k : ℤ) : (sZero k).im ≠ 0 := by
  rw [sZero_im]
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by
    intro h
    have h' : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast h
    omega
  exact div_ne_zero (mul_ne_zero hk Real.pi_ne_zero) log_two_pos'.ne'

lemma two_cpow_neg_sZero' (k : ℤ) :
    (2 : ℂ) ^ (-sZero k) = ((-(2 + Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast log_two_pos'.ne'
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), h2, ← ofReal_log (by norm_num)]
  have hsum : 0 < 2 + Real.sqrt 2 := by positivity
  have key : (Real.log 2 : ℂ) * -sZero k =
      -(Real.log (2 + Real.sqrt 2) : ℂ) + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) + (-(Real.pi * I)) := by
    rw [sZero]; push_cast; field_simp; ring
  rw [key, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_neg,
    Complex.exp_neg, Complex.exp_pi_mul_I, ← ofReal_exp, Real.exp_log hsum]
  push_cast
  ring

/-- `2^{-s_k} = -1 + √2/2`, a root of `1 + 4x + 2x²`. -/
theorem two_cpow_neg_sZero (k : ℤ) :
    (2 : ℂ) ^ (-sZero k) = ((-1 + Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  rw [two_cpow_neg_sZero']
  congr 1
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : (2 + Real.sqrt 2) ≠ 0 := by positivity
  field_simp
  nlinarith [h2]

theorem Pfac_sZero (k : ℤ) : Pfac (sZero k) = 0 := by
  rw [Pfac_eq_x, two_cpow_neg_sZero']
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : (2 + Real.sqrt 2) ≠ 0 := by positivity
  have hreal : (1 + 4 * (-(2 + Real.sqrt 2)⁻¹) + 2 * (-(2 + Real.sqrt 2)⁻¹) ^ 2 : ℝ) = 0 := by
    field_simp
    nlinarith [h2]
  have := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at this ⊢
  linear_combination this

theorem Pfac_one_sub_sZero (k : ℤ) : Pfac (1 - sZero k) = 0 := by
  have h := Pfac_fe (sZero k)
  rw [Pfac_sZero, mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (two_cpow_ne_zero _)

/-- **The negative-control certificate.** For every `k ∈ ℤ`:
`F(s_k) = 0` with `Re s_k = log_2(2+√2) > 1` and `ζ(s_k) ≠ 0`; the absolutely convergent
Dirichlet series with coefficients `a(n) ∈ {1, 5, 7}` vanishes at `s_k`; the completed
`Λ_F` (which satisfies the zeta-shape FE, `LambdaF_one_sub`) vanishes at `s_k` and at the
mirror point `1 - s_k`, where `Re < 0`; `F(1 - s_k) = 0` and `Im s_k ≠ 0` (not a trivial zero).
Nonnegative coefficients + Euler product + a degree-1 FE with root number `+1` do not give a
zero-free half-plane `σ > 1`, let alone RH. -/
theorem negControl_zeros (k : ℤ) :
    Fneg (sZero k) = 0 ∧ riemannZeta (sZero k) ≠ 0 ∧ 1 < (sZero k).re ∧
      LSeries (fun n => (coefF n : ℂ)) (sZero k) = 0 ∧
      LambdaF (sZero k) = 0 ∧ LambdaF (1 - sZero k) = 0 ∧ (1 - sZero k).re < 0 ∧
      Fneg (1 - sZero k) = 0 ∧ (sZero k).im ≠ 0 := by
  have hre := one_lt_sZero_re k
  have hF : Fneg (sZero k) = 0 := by unfold Fneg; rw [Pfac_sZero, mul_zero]
  refine ⟨hF, riemannZeta_ne_zero_of_one_lt_re hre, hre, ?_, ?_, ?_, ?_, ?_, sZero_im_ne_zero k⟩
  · rw [LSeries_coefF hre, hF]
  · unfold LambdaF; rw [Pfac_sZero, mul_zero, zero_mul]
  · unfold LambdaF; rw [Pfac_one_sub_sZero, mul_zero, zero_mul]
  · simp only [Complex.sub_re, Complex.one_re]; linarith
  · unfold Fneg; rw [Pfac_one_sub_sZero, mul_zero]

/-! ### A4: `Λ_F` on powers of 2 -- P2 fails at `n = 4` -/

/-- Any `Lv` satisfying the defining identity of the von Mangoldt coefficients of `F`,
`∑_{d ∣ n} Lv(d)·a(n/d) = a(n)·log n` (equivalently `-F'/F = ∑ Lv(n) n^{-s}`), at
`n = 1, 2, 4, 8, 16` has `Lv(2^k) = (5, -11, 41, -135)·log 2`.  In particular `Λ_F(4) < 0`. -/
theorem vonMangoldtF_two_pow (Lv : ℕ → ℝ)
    (hL : ∀ n ∈ ({1, 2, 4, 8, 16} : Finset ℕ),
      ∑ p ∈ n.divisorsAntidiagonal, Lv p.1 * (coefF p.2 : ℝ) = (coefF n : ℝ) * Real.log n) :
    Lv 1 = 0 ∧ Lv 2 = 5 * Real.log 2 ∧ Lv 4 = -11 * Real.log 2 ∧ Lv 8 = 41 * Real.log 2 ∧
      Lv 16 = -135 * Real.log 2 := by
  have e1 := hL 1 (by decide)
  have e2 := hL 2 (by decide)
  have e4 := hL 4 (by decide)
  have e8 := hL 8 (by decide)
  have e16 := hL 16 (by decide)
  rw [show Nat.divisorsAntidiagonal 1 = {(1,1)} from by decide] at e1
  rw [show Nat.divisorsAntidiagonal 2 = {(1,2),(2,1)} from by decide] at e2
  rw [show Nat.divisorsAntidiagonal 4 = {(1,4),(2,2),(4,1)} from by decide] at e4
  rw [show Nat.divisorsAntidiagonal 8 = {(1,8),(2,4),(4,2),(8,1)} from by decide] at e8
  rw [show Nat.divisorsAntidiagonal 16 = {(1,16),(2,8),(4,4),(8,2),(16,1)} from by decide] at e16
  have c1 : coefF 1 = 1 := by decide
  have c2 : coefF 2 = 5 := by decide
  have c4 : coefF 4 = 7 := by decide
  have c8 : coefF 8 = 7 := by decide
  have c16 : coefF 16 = 7 := by decide
  norm_num [c1, c2, c4, c8, c16] at e1 e2 e4 e8 e16
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have l16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  rw [l4] at e4
  rw [l8] at e8
  rw [l16] at e16
  have h1 : Lv 1 = 0 := by linarith
  have h2 : Lv 2 = 5 * Real.log 2 := by rw [h1] at e2; linarith
  have h4 : Lv 4 = -11 * Real.log 2 := by rw [h1, h2] at e4; linarith
  have h8 : Lv 8 = 41 * Real.log 2 := by rw [h1, h2, h4] at e8; linarith
  have h16 : Lv 16 = -135 * Real.log 2 := by rw [h1, h2, h4, h8] at e16; linarith
  exact ⟨h1, h2, h4, h8, h16⟩

/-- The hypothesis of `vonMangoldtF_two_pow` is consistent (the triangular system is solved by
the stated values), so the theorem is not vacuous. -/
theorem vonMangoldtF_two_pow_consistent :
    ∃ Lv : ℕ → ℝ, ∀ n ∈ ({1, 2, 4, 8, 16} : Finset ℕ),
      ∑ p ∈ n.divisorsAntidiagonal, Lv p.1 * (coefF p.2 : ℝ) = (coefF n : ℝ) * Real.log n := by
  refine ⟨fun n => if n = 2 then 5 * Real.log 2 else if n = 4 then -11 * Real.log 2 else
    if n = 8 then 41 * Real.log 2 else if n = 16 then -135 * Real.log 2 else 0, ?_⟩
  have c1 : coefF 1 = 1 := by decide
  have c2 : coefF 2 = 5 := by decide
  have c4 : coefF 4 = 7 := by decide
  have c8 : coefF 8 = 7 := by decide
  have c16 : coefF 16 = 7 := by decide
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have l16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · rw [show Nat.divisorsAntidiagonal 1 = {(1,1)} from by decide]
    norm_num [c1]
  · rw [show Nat.divisorsAntidiagonal 2 = {(1,2),(2,1)} from by decide]
    norm_num [c1, c2]
  · rw [show Nat.divisorsAntidiagonal 4 = {(1,4),(2,2),(4,1)} from by decide]
    norm_num [c1, c2, c4, l4]
    ring
  · rw [show Nat.divisorsAntidiagonal 8 = {(1,8),(2,4),(4,2),(8,1)} from by decide]
    norm_num [c1, c2, c4, c8, l8]
    ring
  · rw [show Nat.divisorsAntidiagonal 16 = {(1,16),(2,8),(4,4),(8,2),(16,1)} from by decide]
    norm_num [c1, c2, c4, c8, c16, l16]
    ring

/-- For real `x > 1`, `-F'(x) = L(log·a, x)`. -/
lemma neg_deriv_Fneg {x : ℝ} (hx : 1 < x) :
    -deriv Fneg x = LSeries (LSeries.logMul (fun n => (coefF n : ℂ))) x := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (x : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hx
  have heq : (fun s => LSeries (fun n => (coefF n : ℂ)) s) =ᶠ[nhds (x : ℂ)] Fneg :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => LSeries_coefF hs)
  rw [← heq.deriv_eq, LSeries_deriv, neg_neg]
  calc LSeries.abscissaOfAbsConv (fun n => (coefF n : ℂ)) ≤ 1 := abscissa_coefF_le
    _ < ((x : ℂ).re : EReal) := by
      simpa using (show ((1 : ℝ) : EReal) < (x : EReal) from by exact_mod_cast hx)

/-- **Analytic form of the P2 failure.** Let `Λ : ℕ → ℂ` be any sequence whose L-series
converges somewhere and represents `-F'/F` at all large real `x`.  Then `Λ(1) = 0`,
`Λ(2) = 5 log 2` and `Λ(4) = -11 log 2 < 0`. -/
theorem vonMangoldtF_of_logDeriv (Λ : ℕ → ℂ) (hΛ : LSeries.abscissaOfAbsConv Λ < ⊤)
    (hlog : ∀ᶠ x : ℝ in Filter.atTop, LSeries Λ x * Fneg x = -deriv Fneg x) :
    Λ 1 = 0 ∧ Λ 2 = 5 * (Real.log 2 : ℂ) ∧ Λ 4 = -11 * (Real.log 2 : ℂ) := by
  set a : ℕ → ℂ := fun n => (coefF n : ℂ) with ha
  obtain ⟨y, hy1, -⟩ := EReal.lt_iff_exists_real_btwn.mp hΛ
  have hconvAbs : LSeries.abscissaOfAbsConv (Λ ⍟ a) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_convolution_le Λ a)
      (max_lt hΛ (lt_of_le_of_lt abscissa_coefF_le (EReal.coe_lt_top 1)))
  have hlogAbs : LSeries.abscissaOfAbsConv (LSeries.logMul a) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact lt_of_le_of_lt abscissa_coefF_le (EReal.coe_lt_top 1)
  have hev : (fun x : ℝ => LSeries (Λ ⍟ a) x) =ᶠ[Filter.atTop]
      (fun x : ℝ => LSeries (LSeries.logMul a) x) := by
    filter_upwards [hlog, Filter.eventually_gt_atTop (max y 1)] with x hx hxy
    have hx1 : 1 < x := lt_of_le_of_lt (le_max_right _ _) hxy
    have hxy' : y < x := lt_of_le_of_lt (le_max_left _ _) hxy
    have hΛx : LSeries.abscissaOfAbsConv Λ < ((x : ℂ).re : EReal) := by
      simp only [ofReal_re]
      exact lt_trans hy1 (by exact_mod_cast hxy')
    have hax : LSeries.abscissaOfAbsConv a < ((x : ℂ).re : EReal) := by
      simp only [ofReal_re]
      exact lt_of_le_of_lt abscissa_coefF_le (by exact_mod_cast hx1)
    rw [LSeries_convolution hΛx hax, LSeries_coefF (by simpa using hx1), hx, neg_deriv_Fneg hx1]
  have hid : ∀ n : ℕ, n ≠ 0 → (Λ ⍟ a) n = LSeries.logMul a n :=
    fun n hn => LSeries.eq_of_LSeries_eventually_eq hconvAbs hlogAbs hev hn
  have e1 := hid 1 one_ne_zero
  have e2 := hid 2 two_ne_zero
  have e4 := hid 4 (by norm_num)
  simp only [LSeries.convolution_def, LSeries.logMul] at e1 e2 e4
  rw [show Nat.divisorsAntidiagonal 1 = {(1,1)} from by decide] at e1
  rw [show Nat.divisorsAntidiagonal 2 = {(1,2),(2,1)} from by decide] at e2
  rw [show Nat.divisorsAntidiagonal 4 = {(1,4),(2,2),(4,1)} from by decide] at e4
  have c1 : coefF 1 = 1 := by decide
  have c2 : coefF 2 = 5 := by decide
  have c4 : coefF 4 = 7 := by decide
  simp only [ha] at e1 e2 e4
  norm_num [c1, c2, c4] at e1 e2 e4
  have l4 : Complex.log 4 = 2 * (Real.log 2 : ℂ) := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← ofReal_log (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have l2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← ofReal_log (by norm_num)]
  rw [l2] at e2
  rw [l4] at e4
  have h1 : Λ 1 = 0 := e1
  have h2 : Λ 2 = 5 * (Real.log 2 : ℂ) := by
    rw [h1] at e2; linear_combination e2
  have h4 : Λ 4 = -11 * (Real.log 2 : ℂ) := by
    rw [h1, h2] at e4; linear_combination e4
  exact ⟨h1, h2, h4⟩

/-! ## (B) The Davenport–Heilbronn-type `q = 5` mixture -/

/-- The real (quadratic, even) character mod 5. -/
def chi5 (n : ℕ) : ℤ :=
  if n % 5 = 0 then 0 else if n % 5 = 1 ∨ n % 5 = 4 then 1 else -1

/-- `chi5` is the Legendre symbol `(n / 5)`. -/
theorem chi5_eq_jacobiSym (n : ℕ) : chi5 n = jacobiSym n 5 := by
  rw [jacobiSym.mod_left, ← Int.natCast_mod]
  unfold chi5
  have hlt : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = r at hlt ⊢
  interval_cases r <;> norm_num

/-- Dirichlet coefficients of `a·ζ(s)(1 + √5·5^{-s}) + b·L(s, χ₅)`. -/
noncomputable def coefDH (a b : ℝ) (n : ℕ) : ℝ :=
  a * (1 + if 5 ∣ n then Real.sqrt 5 else 0) + b * (chi5 n : ℝ)

lemma abs_chi5_le (n : ℕ) : |(chi5 n : ℝ)| ≤ 1 := by
  unfold chi5
  split_ifs <;> norm_num

/-- Nonnegative coefficients when `|b| ≤ a`. -/
theorem coefDH_nonneg {a b : ℝ} (hab : |b| ≤ a) (n : ℕ) : 0 ≤ coefDH a b n := by
  unfold coefDH
  have ha : 0 ≤ a := le_trans (abs_nonneg b) hab
  have hx : 0 ≤ (if 5 ∣ n then Real.sqrt 5 else 0) := by
    split_ifs
    · exact Real.sqrt_nonneg 5
    · exact le_refl 0
  have h1 : a ≤ a * (1 + if 5 ∣ n then Real.sqrt 5 else 0) := by nlinarith
  have h2 : -a ≤ b * (chi5 n : ℝ) := by
    have habs := abs_mul b (chi5 n : ℝ)
    have h3 : |b * (chi5 n : ℝ)| ≤ a := by
      rw [habs]
      calc |b| * |(chi5 n : ℝ)| ≤ |b| * 1 :=
            mul_le_mul_of_nonneg_left (abs_chi5_le n) (abs_nonneg b)
        _ ≤ a := by linarith
    linarith [neg_abs_le (b * (chi5 n : ℝ))]
  linarith

lemma chi5_of_plus {n : ℕ} (h5 : n % 5 = 1 ∨ n % 5 = 4) : chi5 n = 1 := by
  unfold chi5; split_ifs <;> omega

lemma chi5_of_minus {n : ℕ} (h5 : n % 5 = 2 ∨ n % 5 = 3) : chi5 n = -1 := by
  unfold chi5; split_ifs <;> omega

lemma coefDH_of_chi_one {a b : ℝ} {n : ℕ} (h5 : n % 5 = 1 ∨ n % 5 = 4) :
    coefDH a b n = a + b := by
  have h5' : ¬ 5 ∣ n := by omega
  simp [coefDH, h5', chi5_of_plus h5]

lemma coefDH_of_chi_neg {a b : ℝ} {n : ℕ} (h5 : n % 5 = 2 ∨ n % 5 = 3) :
    coefDH a b n = a - b := by
  have h5' : ¬ 5 ∣ n := by omega
  simp [coefDH, h5', chi5_of_minus h5]
  ring

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Mathlib's Dirichlet character mod 5 attached to the quadratic character of `ZMod 5`. -/
noncomputable def chi5D : DirichletCharacter ℂ 5 :=
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

theorem chi5D_apply (n : ℕ) : chi5D (n : ZMod 5) = (chi5 n : ℂ) := by
  have h1 : (quadraticChar (ZMod 5)) (n : ZMod 5) = legendreSym 5 n := by
    simp [legendreSym]
  have h2 : legendreSym 5 n = jacobiSym n 5 := jacobiSym.legendreSym.to_jacobiSym 5 n
  rw [chi5D, MulChar.ringHomComp_apply, h1, h2, ← chi5_eq_jacobiSym]
  simp

/-- The finitely supported factor `a·δ₁ + a√5·δ₅`. -/
noncomputable def dfac (a : ℝ) (n : ℕ) : ℂ :=
  (if n = 1 then (a : ℂ) else 0) + (if n = 5 then ((a * Real.sqrt 5 : ℝ) : ℂ) else 0)

lemma one_conv_dfac (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((1 : ℕ → ℂ) ⍟ dfac a) n = ((a * (1 + if 5 ∣ n then Real.sqrt 5 else 0) : ℝ) : ℂ) := by
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, one_mul]
  have h : ∑ p ∈ n.divisorsAntidiagonal, dfac a p.2 = ∑ d ∈ n.divisors, dfac a d :=
    Nat.sum_divisorsAntidiagonal' (fun _ b => dfac a b)
  rw [h]
  simp only [dfac, Finset.sum_add_distrib, Finset.sum_ite_eq', Nat.mem_divisors]
  by_cases h5 : 5 ∣ n
  · simp [hn, h5]; ring
  · simp [hn, h5]

lemma term_dfac_eq_zero (a : ℝ) (s : ℂ) (b : ℕ) (hb : b ∉ ({1, 5} : Finset ℕ)) :
    LSeries.term (dfac a) s b = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  obtain ⟨h1, h5⟩ := hb
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  · rw [LSeries.term_of_ne_zero hb0]
    simp [dfac, h1, h5]

lemma LSeries_dfac (a : ℝ) (s : ℂ) :
    LSeries (dfac a) s = a * (1 + Real.sqrt 5 * (5 : ℂ) ^ (-s)) := by
  rw [LSeries, tsum_eq_sum (term_dfac_eq_zero a s)]
  simp [LSeries.term, dfac, cpow_neg, div_eq_mul_inv]
  ring

/-- `coefDH a b` is the coefficient sequence of `a·ζ(s)(1 + √5·5^{-s}) + b·L(s, χ₅)`, with
`L(s, χ₅)` Mathlib's Dirichlet L-function of the quadratic character mod 5 (for `Re s > 1`). -/
theorem LSeries_coefDH (a b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (coefDH a b n : ℂ)) s =
      a * riemannZeta s * (1 + Real.sqrt 5 * (5 : ℂ) ^ (-s)) +
        b * DirichletCharacter.LFunction chi5D s := by
  have hsum1 : LSeriesSummable ((1 : ℕ → ℂ) ⍟ dfac a) s :=
    (LSeriesSummable_one_iff.mpr hs).convolution
      (summable_of_ne_finset_zero (term_dfac_eq_zero a s))
  have hchi_bdd : ∀ n ≠ 0, ‖(fun n => (b : ℂ) * (chi5 n : ℂ)) n‖ ≤ |b| := by
    intro n _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(chi5 n : ℂ)‖ ≤ 1 := by
      unfold chi5; split_ifs <;> simp
    calc |b| * ‖(chi5 n : ℂ)‖ ≤ |b| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg b)
      _ = |b| := mul_one _
  have hsum2 : LSeriesSummable (fun n => (b : ℂ) * (chi5 n : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re hchi_bdd hs
  have hsplit : LSeries (fun n => (coefDH a b n : ℂ)) s =
      LSeries (((1 : ℕ → ℂ) ⍟ dfac a) + (fun n => (b : ℂ) * (chi5 n : ℂ))) s := by
    apply LSeries_congr
    intro n hn
    simp only [Pi.add_apply, one_conv_dfac a hn, coefDH]
    push_cast
    ring
  rw [hsplit, LSeries_add hsum1 hsum2, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
    (summable_of_ne_finset_zero (term_dfac_eq_zero a s)), LSeries_one_eq_riemannZeta hs,
    LSeries_dfac, DirichletCharacter.LFunction_eq_LSeries chi5D hs]
  have hL : LSeries (fun n => (b : ℂ) * (chi5 n : ℂ)) s = b * LSeries (fun n => chi5D n) s := by
    rw [← LSeries_smul]
    apply LSeries_congr
    intro n _
    simp [chi5D_apply]
  rw [hL]
  ring

/-- Normalized mixture (`a + b = 1`), divisors of `36 = 2²·3²` (2 and 3 have `χ₅ = -1`):
any `Lv` solving the defining identity of `Λ` there has `Lv(4) = (2 - (a-b)²) log 2`,
`Lv(6) = 4ab log 6`, `Lv(12) = -4ab(a-b) log 12` and `Lv(36) = -4ab(1 - 3(a-b)²) log 6`.
These are the EARLIEST sign failures found by the scan in `research/axiso_literature/`
(`n = 12` when `0 < b < a`, `n = 36` when `a = b`), earlier than the squarefree cumulant
witnesses `42` and `546` below. -/
theorem vonMangoldtDH_36 (a b : ℝ) (hab : a + b = 1) (Lv : ℕ → ℝ)
    (hL : ∀ m ∈ Nat.divisors 36,
      ∑ p ∈ m.divisorsAntidiagonal, Lv p.1 * coefDH a b p.2 = coefDH a b m * Real.log m) :
    Lv 4 = (2 - (a - b) ^ 2) * Real.log 2 ∧ Lv 6 = 4 * a * b * Real.log 6 ∧
      Lv 12 = -4 * a * b * (a - b) * Real.log 12 ∧
      Lv 36 = -4 * a * b * (1 - 3 * (a - b) ^ 2) * Real.log 6 := by
  have c1 : coefDH a b 1 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c4 : coefDH a b 4 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c6 : coefDH a b 6 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c9 : coefDH a b 9 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c36 : coefDH a b 36 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c2 : coefDH a b 2 = a - b := coefDH_of_chi_neg (by norm_num)
  have c3 : coefDH a b 3 = a - b := coefDH_of_chi_neg (by norm_num)
  have c12 : coefDH a b 12 = a - b := coefDH_of_chi_neg (by norm_num)
  have c18 : coefDH a b 18 = a - b := coefDH_of_chi_neg (by norm_num)
  have e1 := hL 1 (by decide)
  have e2 := hL 2 (by decide)
  have e3 := hL 3 (by decide)
  have e4 := hL 4 (by decide)
  have e6 := hL 6 (by decide)
  have e9 := hL 9 (by decide)
  have e12 := hL 12 (by decide)
  have e18 := hL 18 (by decide)
  have e36 := hL 36 (by decide)
  rw [show Nat.divisorsAntidiagonal 1 = {(1,1)} from by decide] at e1
  rw [show Nat.divisorsAntidiagonal 2 = {(1,2),(2,1)} from by decide] at e2
  rw [show Nat.divisorsAntidiagonal 3 = {(1,3),(3,1)} from by decide] at e3
  rw [show Nat.divisorsAntidiagonal 4 = {(1,4),(2,2),(4,1)} from by decide] at e4
  rw [show Nat.divisorsAntidiagonal 6 = {(1,6),(2,3),(3,2),(6,1)} from by decide] at e6
  rw [show Nat.divisorsAntidiagonal 9 = {(1,9),(3,3),(9,1)} from by decide] at e9
  rw [show Nat.divisorsAntidiagonal 12 = {(1,12),(2,6),(3,4),(4,3),(6,2),(12,1)}
    from by decide] at e12
  rw [show Nat.divisorsAntidiagonal 18 = {(1,18),(2,9),(3,6),(6,3),(9,2),(18,1)}
    from by decide] at e18
  rw [show Nat.divisorsAntidiagonal 36 = {(1,36),(2,18),(3,12),(4,9),(6,6),(9,4),(12,3),
    (18,2),(36,1)} from by decide] at e36
  norm_num [c1, c2, c3, c4, c6, c9, c12, c18, c36] at e1 e2 e3 e4 e6 e9 e12 e18 e36
  have lg : ∀ x y : ℝ, 0 < x → 0 < y → Real.log (x * y) = Real.log x + Real.log y :=
    fun x y hx hy => Real.log_mul hx.ne' hy.ne'
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, lg _ _ (by norm_num) (by norm_num)]; ring
  have l9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, lg _ _ (by norm_num) (by norm_num)]; ring
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, lg _ _ (by norm_num) (by norm_num)]
  have l12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 4 * 3 by norm_num, lg _ _ (by norm_num) (by norm_num), l4]
  have l18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    rw [show (18 : ℝ) = 2 * 9 by norm_num, lg _ _ (by norm_num) (by norm_num), l9]
  have l36 : Real.log 36 = 2 * Real.log 2 + 2 * Real.log 3 := by
    rw [show (36 : ℝ) = 4 * 9 by norm_num, lg _ _ (by norm_num) (by norm_num), l4, l9]
  have hb : b = 1 - a := by linarith
  subst hb
  have h1 : Lv 1 = 0 := by linarith
  have h2 : Lv 2 = (2 * a - 1) * Real.log 2 := by linear_combination e2 - (a - (1 - a)) * h1
  have h3 : Lv 3 = (2 * a - 1) * Real.log 3 := by linear_combination e3 - (a - (1 - a)) * h1
  have h4 : Lv 4 = (2 - (2 * a - 1) ^ 2) * Real.log 2 := by
    linear_combination e4 - h1 - (2 * a - 1) * h2 + l4
  have h9 : Lv 9 = (2 - (2 * a - 1) ^ 2) * Real.log 3 := by
    linear_combination e9 - h1 - (2 * a - 1) * h3 + l9
  have h6 : Lv 6 = (1 - (2 * a - 1) ^ 2) * (Real.log 2 + Real.log 3) := by
    linear_combination e6 - h1 - (2 * a - 1) * h2 - (2 * a - 1) * h3 + l6
  have h12 : Lv 12 = -(2 * a - 1) * (1 - (2 * a - 1) ^ 2) * (2 * Real.log 2 + Real.log 3) := by
    linear_combination e12 - (2 * a - 1) * h1 - h2 - h3 - (2 * a - 1) * h4 - (2 * a - 1) * h6
      + (2 * a - 1) * l12
  have h18 : Lv 18 = -(2 * a - 1) * (1 - (2 * a - 1) ^ 2) * (Real.log 2 + 2 * Real.log 3) := by
    linear_combination e18 - (2 * a - 1) * h1 - h2 - h3 - (2 * a - 1) * h6 - (2 * a - 1) * h9
      + (2 * a - 1) * l18
  have h36 : Lv 36 = -(1 - (2 * a - 1) ^ 2) * (1 - 3 * (2 * a - 1) ^ 2) *
      (Real.log 2 + Real.log 3) := by
    linear_combination e36 - h1 - (2 * a - 1) * h2 - (2 * a - 1) * h3 - h4 - h6 - h9
      - (2 * a - 1) * h12 - (2 * a - 1) * h18 + l36
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h4
  · linear_combination h6 - 4 * a * (1 - a) * l6
  · linear_combination h12 + 4 * a * (1 - a) * (2 * a - 1) * l12
  · linear_combination h36 + 4 * a * (1 - a) * (1 - 3 * (2 * a - 1) ^ 2) * l6

/-- Normalized mixture (`a + b = 1`): any `Lv` solving the defining identity of `Λ` on the
divisors of `42 = 2·3·7` (three primes with `χ₅ = -1`) has
`Lv(6) = 4ab·log 6` (second cumulant) and `Lv(42) = -8ab(a-b)·log 42` (third cumulant). -/
theorem vonMangoldtDH_42 (a b : ℝ) (hab : a + b = 1) (Lv : ℕ → ℝ)
    (hL : ∀ m ∈ Nat.divisors 42,
      ∑ p ∈ m.divisorsAntidiagonal, Lv p.1 * coefDH a b p.2 = coefDH a b m * Real.log m) :
    Lv 6 = 4 * a * b * Real.log 6 ∧ Lv 42 = -8 * a * b * (a - b) * Real.log 42 := by
  have c1 : coefDH a b 1 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c6 : coefDH a b 6 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c14 : coefDH a b 14 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c21 : coefDH a b 21 = 1 := by rw [coefDH_of_chi_one (by norm_num)]; exact hab
  have c2 : coefDH a b 2 = a - b := coefDH_of_chi_neg (by norm_num)
  have c3 : coefDH a b 3 = a - b := coefDH_of_chi_neg (by norm_num)
  have c7 : coefDH a b 7 = a - b := coefDH_of_chi_neg (by norm_num)
  have c42 : coefDH a b 42 = a - b := coefDH_of_chi_neg (by norm_num)
  have e1 := hL 1 (by decide)
  have e2 := hL 2 (by decide)
  have e3 := hL 3 (by decide)
  have e7 := hL 7 (by decide)
  have e6 := hL 6 (by decide)
  have e14 := hL 14 (by decide)
  have e21 := hL 21 (by decide)
  have e42 := hL 42 (by decide)
  rw [show Nat.divisorsAntidiagonal 1 = {(1,1)} from by decide] at e1
  rw [show Nat.divisorsAntidiagonal 2 = {(1,2),(2,1)} from by decide] at e2
  rw [show Nat.divisorsAntidiagonal 3 = {(1,3),(3,1)} from by decide] at e3
  rw [show Nat.divisorsAntidiagonal 7 = {(1,7),(7,1)} from by decide] at e7
  rw [show Nat.divisorsAntidiagonal 6 = {(1,6),(2,3),(3,2),(6,1)} from by decide] at e6
  rw [show Nat.divisorsAntidiagonal 14 = {(1,14),(2,7),(7,2),(14,1)} from by decide] at e14
  rw [show Nat.divisorsAntidiagonal 21 = {(1,21),(3,7),(7,3),(21,1)} from by decide] at e21
  rw [show Nat.divisorsAntidiagonal 42 = {(1,42),(2,21),(3,14),(6,7),(7,6),(14,3),(21,2),(42,1)}
    from by decide] at e42
  norm_num [c1, c2, c3, c6, c7, c14, c21, c42] at e1 e2 e3 e7 e6 e14 e21 e42
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l14 : Real.log 14 = Real.log 2 + Real.log 7 := by
    rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l21 : Real.log 21 = Real.log 3 + Real.log 7 := by
    rw [show (21 : ℝ) = 3 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l42 : Real.log 42 = Real.log 2 + Real.log 3 + Real.log 7 := by
    rw [show (42 : ℝ) = 2 * 3 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have hb : b = 1 - a := by linarith
  subst hb
  have h1 : Lv 1 = 0 := by linarith
  have h2 : Lv 2 = (2 * a - 1) * Real.log 2 := by linear_combination e2 - (a - (1 - a)) * h1
  have h3 : Lv 3 = (2 * a - 1) * Real.log 3 := by linear_combination e3 - (a - (1 - a)) * h1
  have h7 : Lv 7 = (2 * a - 1) * Real.log 7 := by linear_combination e7 - (a - (1 - a)) * h1
  have h6 : Lv 6 = (1 - (2 * a - 1) ^ 2) * Real.log 6 := by
    linear_combination e6 - h1 - (2 * a - 1) * h2 - (2 * a - 1) * h3 + (2 * a - 1) ^ 2 * l6
  have h14 : Lv 14 = (1 - (2 * a - 1) ^ 2) * Real.log 14 := by
    linear_combination e14 - h1 - (2 * a - 1) * h2 - (2 * a - 1) * h7 + (2 * a - 1) ^ 2 * l14
  have h21 : Lv 21 = (1 - (2 * a - 1) ^ 2) * Real.log 21 := by
    linear_combination e21 - h1 - (2 * a - 1) * h3 - (2 * a - 1) * h7 + (2 * a - 1) ^ 2 * l21
  have h42 : Lv 42 = -2 * (2 * a - 1) * (1 - (2 * a - 1) ^ 2) * Real.log 42 := by
    linear_combination e42 - (2 * a - 1) * h1 - h2 - h3 - h7 - (2 * a - 1) * h6
      - (2 * a - 1) * h14 - (2 * a - 1) * h21
      + ((2 * a - 1) + 2 * (2 * a - 1) * (1 - (2 * a - 1) ^ 2)) * l42
      - (2 * a - 1) * (1 - (2 * a - 1) ^ 2) * l6 - (2 * a - 1) * (1 - (2 * a - 1) ^ 2) * l14
      - (2 * a - 1) * (1 - (2 * a - 1) ^ 2) * l21
  constructor
  · linear_combination h6
  · linear_combination h42

/-- The boundary case `a = b = 1/2`: the third cumulant vanishes and the fourth does not.
Any `Lv` solving the defining identity on the divisors of `546 = 2·3·7·13` has
`Lv(546) = -2·log 546 < 0`. -/
theorem vonMangoldtDH_546 (Lv : ℕ → ℝ)
    (hL : ∀ m ∈ Nat.divisors 546,
      ∑ p ∈ m.divisorsAntidiagonal, Lv p.1 * coefDH (1 / 2) (1 / 2) p.2 =
        coefDH (1 / 2) (1 / 2) m * Real.log m) :
    Lv 546 = -2 * Real.log 546 := by
  have cplus : ∀ n : ℕ, (n % 5 = 1 ∨ n % 5 = 4) → coefDH (1 / 2) (1 / 2) n = 1 := by
    intro n hn; rw [coefDH_of_chi_one hn]; norm_num
  have cminus : ∀ n : ℕ, (n % 5 = 2 ∨ n % 5 = 3) → coefDH (1 / 2) (1 / 2) n = 0 := by
    intro n hn; rw [coefDH_of_chi_neg hn]; norm_num
  have c1 := cplus 1 (by norm_num)
  have c6 := cplus 6 (by norm_num)
  have c14 := cplus 14 (by norm_num)
  have c21 := cplus 21 (by norm_num)
  have c26 := cplus 26 (by norm_num)
  have c39 := cplus 39 (by norm_num)
  have c91 := cplus 91 (by norm_num)
  have c546 := cplus 546 (by norm_num)
  have c2 := cminus 2 (by norm_num)
  have c3 := cminus 3 (by norm_num)
  have c7 := cminus 7 (by norm_num)
  have c13 := cminus 13 (by norm_num)
  have c42 := cminus 42 (by norm_num)
  have c78 := cminus 78 (by norm_num)
  have c182 := cminus 182 (by norm_num)
  have c273 := cminus 273 (by norm_num)
  have e1 := hL 1 (by decide)
  have e6 := hL 6 (by decide)
  have e14 := hL 14 (by decide)
  have e26 := hL 26 (by decide)
  have e21 := hL 21 (by decide)
  have e39 := hL 39 (by decide)
  have e91 := hL 91 (by decide)
  have e546 := hL 546 (by decide)
  rw [show Nat.divisorsAntidiagonal 1 = {(1,1)} from by decide] at e1
  rw [show Nat.divisorsAntidiagonal 6 = {(1,6),(2,3),(3,2),(6,1)} from by decide] at e6
  rw [show Nat.divisorsAntidiagonal 14 = {(1,14),(2,7),(7,2),(14,1)} from by decide] at e14
  rw [show Nat.divisorsAntidiagonal 26 = {(1,26),(2,13),(13,2),(26,1)} from by decide] at e26
  rw [show Nat.divisorsAntidiagonal 21 = {(1,21),(3,7),(7,3),(21,1)} from by decide] at e21
  rw [show Nat.divisorsAntidiagonal 39 = {(1,39),(3,13),(13,3),(39,1)} from by decide] at e39
  rw [show Nat.divisorsAntidiagonal 91 = {(1,91),(7,13),(13,7),(91,1)} from by decide] at e91
  rw [show Nat.divisorsAntidiagonal 546 = {(1,546),(2,273),(3,182),(6,91),(7,78),(13,42),
    (14,39),(21,26),(26,21),(39,14),(42,13),(78,7),(91,6),(182,3),(273,2),(546,1)}
    from by decide] at e546
  norm_num [c1, c2, c3, c6, c7, c13, c14, c21, c26, c39, c42, c78, c91, c182, c273, c546]
    at e1 e6 e14 e26 e21 e39 e91 e546
  have lg : ∀ x y : ℝ, 0 < x → 0 < y → Real.log (x * y) = Real.log x + Real.log y :=
    fun x y hx hy => Real.log_mul hx.ne' hy.ne'
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, lg _ _ (by norm_num) (by norm_num)]
  have l14 : Real.log 14 = Real.log 2 + Real.log 7 := by
    rw [show (14 : ℝ) = 2 * 7 by norm_num, lg _ _ (by norm_num) (by norm_num)]
  have l26 : Real.log 26 = Real.log 2 + Real.log 13 := by
    rw [show (26 : ℝ) = 2 * 13 by norm_num, lg _ _ (by norm_num) (by norm_num)]
  have l21 : Real.log 21 = Real.log 3 + Real.log 7 := by
    rw [show (21 : ℝ) = 3 * 7 by norm_num, lg _ _ (by norm_num) (by norm_num)]
  have l39 : Real.log 39 = Real.log 3 + Real.log 13 := by
    rw [show (39 : ℝ) = 3 * 13 by norm_num, lg _ _ (by norm_num) (by norm_num)]
  have l91 : Real.log 91 = Real.log 7 + Real.log 13 := by
    rw [show (91 : ℝ) = 7 * 13 by norm_num, lg _ _ (by norm_num) (by norm_num)]
  have l546 : Real.log 546 = Real.log 2 + Real.log 3 + Real.log 7 + Real.log 13 := by
    rw [show (546 : ℝ) = 2 * 3 * 7 * 13 by norm_num, lg _ _ (by norm_num) (by norm_num),
      lg _ _ (by norm_num) (by norm_num), lg _ _ (by norm_num) (by norm_num)]
  linear_combination e546 - e6 - e14 - e26 - e21 - e39 - e91 + 5 * e1 + 3 * l546
    - l6 - l14 - l26 - l21 - l39 - l91

/-- The scout's squarefree cumulant witnesses: for every normalized DH-type mixture with
`a ≥ |b| > 0` the von Mangoldt coefficient is negative at `6` (if `b < 0`), at `42` (third
cumulant, if `0 < b < a`) or at `546` (fourth cumulant, if `a = b`). -/
theorem dhMixture_P2_fails_squarefree (a b : ℝ) (hab : a + b = 1) (hdom : |b| ≤ a) (hb : b ≠ 0)
    (Lv : ℕ → ℝ)
    (hL : ∀ m ∈ Nat.divisors 546,
      ∑ p ∈ m.divisorsAntidiagonal, Lv p.1 * coefDH a b p.2 = coefDH a b m * Real.log m) :
    Lv 6 < 0 ∨ Lv 42 < 0 ∨ Lv 546 < 0 := by
  have hL42 : ∀ m ∈ Nat.divisors 42,
      ∑ p ∈ m.divisorsAntidiagonal, Lv p.1 * coefDH a b p.2 = coefDH a b m * Real.log m :=
    fun m hm => hL m (Nat.divisors_subset_of_dvd (by norm_num) (by norm_num) hm)
  obtain ⟨h6, h42⟩ := vonMangoldtDH_42 a b hab Lv hL42
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hl42 : 0 < Real.log 42 := Real.log_pos (by norm_num)
  have ha : 0 < a := lt_of_lt_of_le (abs_pos.mpr hb) hdom
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · left
    rw [h6]
    have : 4 * a * b < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos this hl6
  · have hba : b ≤ a := le_trans (le_abs_self b) hdom
    rcases eq_or_lt_of_le hba with heq | hlt
    · right; right
      have ha2 : a = 1 / 2 := by linarith
      have hb2 : b = 1 / 2 := by linarith
      subst ha2 hb2
      rw [vonMangoldtDH_546 Lv hL]
      have : 0 < Real.log 546 := Real.log_pos (by norm_num)
      linarith
    · right; left
      rw [h42]
      have : 0 < a * b * (a - b) := mul_pos (mul_pos ha hpos) (by linarith)
      nlinarith

/-- **P2 fails for every normalized DH-type mixture** `a·ζ(s)(1+√5·5^{-s}) + b·L(s,χ₅)` with
`a ≥ |b| > 0` (exactly the regime of nonnegative coefficients, `coefDH_nonneg`), already on
the divisors of 36: `Λ(6) < 0` if `b < 0`, `Λ(12) < 0` if `0 < b < a`, `Λ(36) < 0` if `a = b`. -/
theorem dhMixture_P2_fails (a b : ℝ) (hab : a + b = 1) (hdom : |b| ≤ a) (hb : b ≠ 0)
    (Lv : ℕ → ℝ)
    (hL : ∀ m ∈ Nat.divisors 36,
      ∑ p ∈ m.divisorsAntidiagonal, Lv p.1 * coefDH a b p.2 = coefDH a b m * Real.log m) :
    Lv 6 < 0 ∨ Lv 12 < 0 ∨ Lv 36 < 0 := by
  obtain ⟨-, h6, h12, h36⟩ := vonMangoldtDH_36 a b hab Lv hL
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hl12 : 0 < Real.log 12 := Real.log_pos (by norm_num)
  have ha : 0 < a := lt_of_lt_of_le (abs_pos.mpr hb) hdom
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · left
    rw [h6]
    have : 4 * a * b < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos this hl6
  · have hba : b ≤ a := le_trans (le_abs_self b) hdom
    rcases eq_or_lt_of_le hba with heq | hlt
    · right; right
      have ha2 : a = 1 / 2 := by linarith
      have hb2 : b = 1 / 2 := by linarith
      rw [h36, ha2, hb2]
      norm_num
      exact hl6
    · right; left
      rw [h12]
      have : 0 < a * b * (a - b) := mul_pos (mul_pos ha hpos) (by linarith)
      nlinarith

/-- Moment–cumulant identities for a `±1`-valued variable with mean `μ = a - b`, `a + b = 1`
(the weights of `ζ` and `L(·, χ₅)` at primes with `χ₅ = -1`): `κ₂ = 4ab`, `κ₃ = -8ab(a-b)`,
and `κ₄ = -2 + 8μ² - 6μ⁴` (so `κ₄ = -2` at `a = b`). -/
theorem cumulant_pm_one (μ a b : ℝ) (hμ : μ = a - b) (hab : a + b = 1) :
    (1 - μ ^ 2 = 4 * a * b) ∧
    (μ - 3 * 1 * μ + 2 * μ ^ 3 = -8 * a * b * (a - b)) ∧
    (1 - 4 * μ * μ - 3 * 1 ^ 2 + 12 * 1 * μ ^ 2 - 6 * μ ^ 4 = -2 + 8 * μ ^ 2 - 6 * μ ^ 4) := by
  subst hμ
  have hb : b = 1 - a := by linarith
  subst hb
  exact ⟨by ring, by ring, by ring⟩

/-! ## (C) The E8 normalization witness `G(s) = ζ(s/2 + 7/4)·ζ(s/2 - 5/4)` -/

/-- `G(s) = ζ(s/2 + 7/4) ζ(s/2 - 5/4)`: the E8 Epstein zeta `240·2^{-w} ζ(w) ζ(w-3)`,
`w = s/2 + 7/4`, renormalized to the Beurling frequencies `√n`. -/
noncomputable def GE8 (s : ℂ) : ℂ := riemannZeta (s / 2 + 7 / 4) * riemannZeta (s / 2 - 5 / 4)

/-- Its completion `Γ_ℂ(s/2 + 7/4)·G(s)`. -/
noncomputable def LambdaG (s : ℂ) : ℂ := Gammaℂ (s / 2 + 7 / 4) * GE8 s

/-- The completing factor is the scout's `(2π)^{-s/2} Γ(s/2 + 7/4)` up to the constant
`2(2π)^{-7/4}`. -/
theorem Gammaℂ_shift (s : ℂ) :
    Gammaℂ (s / 2 + 7 / 4) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(7 / 4 : ℂ)) *
        ((2 * (Real.pi : ℂ)) ^ (-(s / 2)) * Gamma (s / 2 + 7 / 4)) := by
  have h2pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [Gammaℂ_def, neg_add, cpow_add _ _ h2pi]
  ring

lemma Gammaℝ_ne_zero_of_notInt {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) : Gammaℝ z ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  exact hz (-(2 * n : ℤ)) (by rw [hn]; push_cast; ring)

lemma notInt_sub {w : ℂ} (hw : ∀ n : ℤ, w ≠ n) (m : ℤ) : ∀ n : ℤ, w - m ≠ n := by
  intro n h
  exact hw (n + m) (by push_cast; linear_combination h)

/-- Key identity: `Γ_ℂ(w) ζ(w) ζ(w-3) = (w-3)(w-1)/(4π²)·Λ(w) Λ(w-3)` for `w ∉ ℤ`. -/
theorem key_identity {w : ℂ} (hw : ∀ n : ℤ, w ≠ n) :
    Gammaℂ w * (riemannZeta w * riemannZeta (w - 3)) =
      (w - 3) * (w - 1) / (4 * (Real.pi : ℂ) ^ 2) *
        (completedRiemannZeta w * completedRiemannZeta (w - 3)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw0 : w ≠ 0 := by simpa using hw 0
  have hw3 : w - 3 ≠ 0 := by simpa using notInt_sub hw 3 0
  have hw1 : w - 1 ≠ 0 := by simpa using notInt_sub hw 1 0
  have hG : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_notInt hw
  have hG3 : Gammaℝ (w - 3) ≠ 0 := Gammaℝ_ne_zero_of_notInt (by simpa using notInt_sub hw 3)
  have hstep1 : Gammaℝ (w + 1) = Gammaℝ (w - 1) * (w - 1) / 2 / Real.pi := by
    rw [show w + 1 = (w - 1) + 2 by ring, Gammaℝ_add_two hw1]
  have hstep2 : Gammaℝ (w - 1) = Gammaℝ (w - 3) * (w - 3) / 2 / Real.pi := by
    rw [show w - 1 = (w - 3) + 2 by ring, Gammaℝ_add_two hw3]
  rw [← Gammaℝ_mul_Gammaℝ_add_one, hstep1, hstep2,
    riemannZeta_def_of_ne_zero hw0, riemannZeta_def_of_ne_zero hw3]
  field_simp
  ring

/-- **Functional equation of the E8 witness**: `Λ_G(1 - s) = Λ_G(s)` (root number `+1`,
degree 1 in the variable `s`), for every `s` with `s/2 + 7/4 ∉ ℤ`. -/
theorem LambdaG_one_sub (s : ℂ) (hw : ∀ n : ℤ, s / 2 + 7 / 4 ≠ n) :
    LambdaG (1 - s) = LambdaG s := by
  unfold LambdaG GE8
  have hw' : ∀ n : ℤ, (1 - s) / 2 + 7 / 4 ≠ n := by
    intro n h
    exact hw (4 - n) (by push_cast; linear_combination -h)
  rw [show (1 - s) / 2 - 5 / 4 = ((1 - s) / 2 + 7 / 4) - 3 by ring,
    show s / 2 - 5 / 4 = (s / 2 + 7 / 4) - 3 by ring,
    key_identity hw, key_identity hw']
  rw [show (1 - s) / 2 + 7 / 4 = 1 - ((s / 2 + 7 / 4) - 3) by ring,
    show 1 - ((s / 2 + 7 / 4) - 3) - 3 = 1 - (s / 2 + 7 / 4) by ring,
    completedRiemannZeta_one_sub, completedRiemannZeta_one_sub]
  ring

/-- `ζ` has no zero on the line `Re w = -1` (functional equation + `ζ ≠ 0` on `Re = 2`). -/
theorem riemannZeta_ne_zero_of_re_eq_neg_one {w : ℂ} (hw : w.re = -1) : riemannZeta w ≠ 0 := by
  have hs're : (1 - w).re = 2 := by simp [hw]; norm_num
  have hn : ∀ n : ℕ, (1 - w) ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    rw [hs're] at this
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h1 : (1 - w) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hs're] at this
    simp at this
  have h := riemannZeta_one_sub hn h1
  rw [show 1 - (1 - w) = w by ring] at h
  rw [h]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
  · rw [Ne, cpow_eq_zero_iff]
    intro hc
    have : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    exact this hc.1
  · exact Complex.Gamma_ne_zero_of_re_pos (by rw [hs're]; norm_num)
  · rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hk' : (1 - w) = 2 * k + 1 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk
      linear_combination hk
    have := congrArg Complex.re hk'
    rw [hs're] at this
    simp at this
    have hk2 : (2 : ℝ) = 2 * (k : ℝ) + 1 := this
    have : (2 : ℤ) = 2 * k + 1 := by exact_mod_cast hk2
    omega
  · exact riemannZeta_ne_zero_of_one_lt_re (by rw [hs're]; norm_num)

/-- **`G` has no zero on the critical line**: `G(1/2 + it) ≠ 0` for every real `t`. -/
theorem GE8_ne_zero_on_critical_line (t : ℝ) : GE8 (1 / 2 + t * I) ≠ 0 := by
  unfold GE8
  refine mul_ne_zero ?_ ?_
  · apply riemannZeta_ne_zero_of_one_lt_re
    simp
    norm_num
  · apply riemannZeta_ne_zero_of_re_eq_neg_one
    simp
    norm_num

/-- **Off-line zeros of `G`**: each zero `ρ` of `ζ` with `0 < Re ρ < 1` gives the zero
`2ρ + 5/2` of `G` with `5/2 < Re < 9/2`, and the mirror zero `1 - (2ρ + 5/2)` with
`Re < -3/2`.  (The existence of such a `ρ` is not proved here; the first one is
Arb-certified in `research/axiso_literature/`.) -/
theorem GE8_zero_of_zeta_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    GE8 (2 * ρ + 5 / 2) = 0 ∧ GE8 (1 - (2 * ρ + 5 / 2)) = 0 ∧
      5 / 2 < (2 * ρ + 5 / 2).re ∧ (2 * ρ + 5 / 2).re < 9 / 2 ∧
      (1 - (2 * ρ + 5 / 2)).re < -3 / 2 := by
  have hre : (2 * ρ + 5 / 2).re = 2 * ρ.re + 5 / 2 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold GE8
    rw [show (2 * ρ + 5 / 2) / 2 - 5 / 4 = ρ by ring, hρ, mul_zero]
  · unfold GE8
    have hn : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hne1 : ρ ≠ 1 := by
      intro h
      rw [h] at h1
      simp at h1
    have hz := riemannZeta_one_sub hn hne1
    rw [hρ, mul_zero] at hz
    rw [show (1 - (2 * ρ + 5 / 2)) / 2 + 7 / 4 = 1 - ρ by ring, hz, zero_mul]
  · rw [hre]; linarith
  · rw [hre]; linarith
  · have : (1 - (2 * ρ + 5 / 2)).re = -3 / 2 - 2 * ρ.re := by simp; ring
    rw [this]; linarith

/-- `G` is a product of two Euler products for `Re s > 9/2` (its pole is at `s = 9/2`, not `1`). -/
theorem GE8_eulerProduct {s : ℂ} (hs : 9 / 2 < s.re) :
    GE8 s = (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(s / 2 + 7 / 4)))⁻¹) *
      (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(s / 2 - 5 / 4)))⁻¹) := by
  unfold GE8
  have h1 : 1 < (s / 2 + 7 / 4).re := by
    have : (s / 2 + 7 / 4).re = s.re / 2 + 7 / 4 := by simp
    rw [this]; linarith
  have h2 : 1 < (s / 2 - 5 / 4).re := by
    have : (s / 2 - 5 / 4).re = s.re / 2 - 5 / 4 := by simp
    rw [this]; linarith
  rw [riemannZeta_eulerProduct_tprod h1, riemannZeta_eulerProduct_tprod h2]

/-! ## (D) Elementary fragments of the paper sketches -/

/-- If `n^{-iθ}` is a nonnegative real for an integer `n ≥ 1`, then `θ·log n ∈ 2πℤ`. -/
lemma twist_trivial {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (h : ∃ r : ℝ, 0 ≤ r ∧ (n : ℂ) ^ (-(θ : ℂ) * I) = r) :
    ∃ k : ℤ, θ * Real.log n = 2 * Real.pi * k := by
  obtain ⟨r, hr0, hr⟩ := h
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hexp : (n : ℂ) ^ (-(θ : ℂ) * I) = exp (((-(θ * Real.log n) : ℝ) : ℂ) * I) := by
    rw [cpow_def_of_ne_zero hn0, ← ofReal_natCast, ← ofReal_log (by positivity)]
    congr 1
    push_cast
    ring
  have hnorm : ‖(n : ℂ) ^ (-(θ : ℂ) * I)‖ = 1 := by rw [hexp, norm_exp_ofReal_mul_I]
  have hr1 : r = 1 := by
    rw [hr, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hnorm
    exact hnorm
  rw [hr1, hexp, ofReal_one] at hr
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hr
  have hc : ((-(θ * Real.log n) : ℝ) : ℂ) = ((k * (2 * Real.pi) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ I_ne_zero
    rw [hk]; push_cast; ring
  have hreal := ofReal_injective hc
  refine ⟨-k, ?_⟩
  push_cast
  linarith

lemma coprime_succ_two_mul_succ (q : ℕ) : Nat.Coprime (q + 1) (2 * q + 1) := by
  have h1 := Nat.gcd_dvd_left (q + 1) (2 * q + 1)
  have h2 := Nat.gcd_dvd_right (q + 1) (2 * q + 1)
  have h3 : Nat.gcd (q + 1) (2 * q + 1) ∣ 2 * (q + 1) := Dvd.dvd.mul_left h1 2
  have h4 := Nat.dvd_sub h3 h2
  rw [show 2 * (q + 1) - (2 * q + 1) = 1 by omega] at h4
  exact Nat.eq_one_of_dvd_one h4

/-- Step (1) of the collapse sketch, elementary half.  Kaczorowski–Perelli give
`a(n) n^{iθ} = f(n)` with `f` periodic mod `q`; with `a(1) = 1` and `a(n) ≥ 0` this makes
`n^{-iθ}` a nonnegative real for every `n ≡ 1 (mod q)`.  That already forces `θ = 0`
(only `n = q + 1` and `n = 2q + 1`, which are coprime, are used). -/
theorem theta_eq_zero_of_nonneg_twist (q : ℕ) (hq : 1 ≤ q) (θ : ℝ)
    (h : ∀ n : ℕ, n % q = 1 % q → 1 ≤ n → ∃ r : ℝ, 0 ≤ r ∧ (n : ℂ) ^ (-(θ : ℂ) * I) = r) :
    θ = 0 := by
  have hn1 : (q + 1) % q = 1 % q := by simp
  have hn2 : (2 * q + 1) % q = 1 % q := by
    rw [show 2 * q + 1 = 1 + q * 2 by ring, Nat.add_mul_mod_self_left]
  obtain ⟨k1, hk1⟩ := twist_trivial (by omega) (h (q + 1) hn1 (by omega))
  obtain ⟨k2, hk2⟩ := twist_trivial (by omega) (h (2 * q + 1) hn2 (by omega))
  by_contra hθ
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 0 < Real.log ((q + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
  have hl2 : 0 < Real.log ((2 * q + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
  have hk1ne : k1 ≠ 0 := by
    rintro rfl
    have h0 : θ * Real.log ((q + 1 : ℕ) : ℝ) = 0 := by rw [hk1]; simp
    rcases mul_eq_zero.mp h0 with h | h
    · exact hθ h
    · linarith
  have hcross : (k2 : ℝ) * Real.log ((q + 1 : ℕ) : ℝ) =
      (k1 : ℝ) * Real.log ((2 * q + 1 : ℕ) : ℝ) := by
    have e : θ * ((k2 : ℝ) * Real.log ((q + 1 : ℕ) : ℝ) -
        (k1 : ℝ) * Real.log ((2 * q + 1 : ℕ) : ℝ)) = 0 := by
      have : θ * ((k2 : ℝ) * Real.log ((q + 1 : ℕ) : ℝ)) =
          θ * ((k1 : ℝ) * Real.log ((2 * q + 1 : ℕ) : ℝ)) := by
        calc θ * ((k2 : ℝ) * Real.log ((q + 1 : ℕ) : ℝ))
            = (k2 : ℝ) * (θ * Real.log ((q + 1 : ℕ) : ℝ)) := by ring
          _ = (k2 : ℝ) * (2 * Real.pi * k1) := by rw [hk1]
          _ = (k1 : ℝ) * (2 * Real.pi * k2) := by ring
          _ = (k1 : ℝ) * (θ * Real.log ((2 * q + 1 : ℕ) : ℝ)) := by rw [hk2]
          _ = θ * ((k1 : ℝ) * Real.log ((2 * q + 1 : ℕ) : ℝ)) := by ring
      linarith
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h hθ
    · linarith
  have habs : (k2.natAbs : ℝ) * Real.log ((q + 1 : ℕ) : ℝ) =
      (k1.natAbs : ℝ) * Real.log ((2 * q + 1 : ℕ) : ℝ) := by
    have := congrArg abs hcross
    rw [abs_mul, abs_mul, abs_of_pos hl1, abs_of_pos hl2] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact this
  have hpow : ((q + 1) ^ k2.natAbs : ℕ) = (2 * q + 1) ^ k1.natAbs := by
    have hlog : Real.log ((((q + 1) ^ k2.natAbs : ℕ)) : ℝ) =
        Real.log ((((2 * q + 1) ^ k1.natAbs : ℕ)) : ℝ) := by
      push_cast
      rw [Real.log_pow, Real.log_pow]
      push_cast at habs
      exact habs
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) hlog
    exact_mod_cast this
  have hcop : Nat.Coprime ((q + 1) ^ k2.natAbs) ((2 * q + 1) ^ k1.natAbs) :=
    Nat.Coprime.pow _ _ (coprime_succ_two_mul_succ q)
  rw [hpow, Nat.coprime_self] at hcop
  have hge : 1 < (2 * q + 1) ^ k1.natAbs :=
    Nat.one_lt_pow (Int.natAbs_ne_zero.mpr hk1ne) (by omega)
  omega

/-- Last step of the uniformly-discrete argument: if every power of a rational `g` has
denominator dividing a fixed `D` (all `g^k` lie in `D⁻¹ℤ`), then `g` is an integer. -/
theorem den_eq_one_of_bounded_denominators (g : ℚ) (D : ℕ) (hD : 0 < D)
    (h : ∀ k : ℕ, ∃ z : ℤ, (D : ℚ) * g ^ k = z) : g.den = 1 := by
  have hdvd : ∀ k : ℕ, g.den ^ k ∣ D := by
    intro k
    obtain ⟨z, hz⟩ := h k
    have hgk : g ^ k = (z : ℚ) / (D : ℚ) := by
      have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      field_simp
      linarith [hz]
    have h1 := Rat.den_dvd z D
    rw [Rat.divInt_eq_div] at h1
    push_cast at h1
    rw [← hgk, Rat.den_pow] at h1
    exact_mod_cast h1
  by_contra hne
  have h2 : 2 ≤ g.den := by have := g.den_pos; omega
  have hle : g.den ^ D ≤ D := Nat.le_of_dvd hD (hdvd D)
  have hlt : D < 2 ^ D := Nat.lt_two_pow_self
  have hmono : 2 ^ D ≤ g.den ^ D := Nat.pow_le_pow_left h2 D
  omega

/-- The `K = ℚ` branch of the Kahane–Mandelbrojt order argument: a rational algebraic integer
is an integer. -/
theorem rat_integral_is_int (x : ℚ) (hx : IsIntegral ℤ x) : ∃ z : ℤ, (z : ℚ) = x := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact ⟨z, by simpa using hz⟩

end CruxAxisoLiterature

/-! ## Axiom audit -/

#print axioms CruxAxisoLiterature.Pfac_fe
#print axioms CruxAxisoLiterature.LambdaF_one_sub
#print axioms CruxAxisoLiterature.LambdaF_eq
#print axioms CruxAxisoLiterature.completedF_fe
#print axioms CruxAxisoLiterature.coefF_eq
#print axioms CruxAxisoLiterature.one_le_coefF
#print axioms CruxAxisoLiterature.coefF_le_seven
#print axioms CruxAxisoLiterature.LSeries_coefF
#print axioms CruxAxisoLiterature.coefFA_isMultiplicative
#print axioms CruxAxisoLiterature.sZero_re
#print axioms CruxAxisoLiterature.sZero_im
#print axioms CruxAxisoLiterature.one_lt_sZero_re
#print axioms CruxAxisoLiterature.sZero_im_ne_zero
#print axioms CruxAxisoLiterature.two_cpow_neg_sZero
#print axioms CruxAxisoLiterature.Pfac_sZero
#print axioms CruxAxisoLiterature.Pfac_one_sub_sZero
#print axioms CruxAxisoLiterature.negControl_zeros
#print axioms CruxAxisoLiterature.vonMangoldtF_two_pow
#print axioms CruxAxisoLiterature.vonMangoldtF_two_pow_consistent
#print axioms CruxAxisoLiterature.vonMangoldtF_of_logDeriv
#print axioms CruxAxisoLiterature.chi5_eq_jacobiSym
#print axioms CruxAxisoLiterature.coefDH_nonneg
#print axioms CruxAxisoLiterature.chi5D_apply
#print axioms CruxAxisoLiterature.LSeries_coefDH
#print axioms CruxAxisoLiterature.vonMangoldtDH_36
#print axioms CruxAxisoLiterature.vonMangoldtDH_42
#print axioms CruxAxisoLiterature.vonMangoldtDH_546
#print axioms CruxAxisoLiterature.dhMixture_P2_fails
#print axioms CruxAxisoLiterature.dhMixture_P2_fails_squarefree
#print axioms CruxAxisoLiterature.cumulant_pm_one
#print axioms CruxAxisoLiterature.Gammaℂ_shift
#print axioms CruxAxisoLiterature.key_identity
#print axioms CruxAxisoLiterature.LambdaG_one_sub
#print axioms CruxAxisoLiterature.riemannZeta_ne_zero_of_re_eq_neg_one
#print axioms CruxAxisoLiterature.GE8_ne_zero_on_critical_line
#print axioms CruxAxisoLiterature.GE8_zero_of_zeta_zero
#print axioms CruxAxisoLiterature.GE8_eulerProduct
#print axioms CruxAxisoLiterature.theta_eq_zero_of_nonneg_twist
#print axioms CruxAxisoLiterature.den_eq_one_of_bounded_denominators
#print axioms CruxAxisoLiterature.rat_integral_is_int

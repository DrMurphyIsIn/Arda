/-
  Crux2_rigidity_rate (li_positivity island) -- RIGIDITY CARRIES NO RATE.
  Lens "rigidity-rate", crux round 2, BUILDER file.

  conjecture1_proved = False.  RH is open.  Nothing in this file bears on the location of the zeros
  of the Riemann zeta function.  It is a no-go about a class of arguments: the quantitative content
  of the Beurling-Hamburger rigidity (Theorem A of round 1) is finite coefficient data, and finite
  coefficient data together with an Euler product and nonnegative von Mangoldt weights (P2) is
  compatible with a zero at 1 - delta + i t for EVERY delta > 0 and EVERY t, including points
  inside the proven Mossinghoff-Trudgian-Yang zero-free region of zeta.

  Every theorem and lemma below prints exactly [propext, Classical.choice, Quot.sound] under
  #print axioms (the list is at the end of the file).  There is no `sorry`, no `admit`, no
  `native_decide`, no new `axiom` declaration and no `opaque` constant.  Imports: Mathlib, and the
  island module LowHeightBox (for the strip
  representation of zeta and its real-axis nonvanishing on (0,1)).

  WHAT IT ESTABLISHES (THEOREM-kernel-checked).
  A-C  The window identities (finite atomic measures nu = r delta_0 + sum_i w_i (delta_{x_i} +
       delta_{-x_i})): the triangle-tested FE defect equals the sinc^2-weighted non-integrality
       (`window_defect_identity`), with stability constant 8/pi^2 (`window_defect_stability`),
       rigidity (`window_defect_rigidity`), counting form (`window_defect_counting`), the finite
       extremal point-mass inequality (`atom_le_triPairHat`), and the multiplicity identity
       (`triPairHat_mod_eq`, `triPairHat_mod_int`): the modulated triangle reads off a_m exactly.
  D    Local positivity of the pole-shadow fakes: coefficients a_n >= 0 (`fakeCoeff_nonneg`),
       a_n = 1 for n < X (`fakeCoeff_eq_one_of_lt`), local von Mangoldt brackets
       1 - 2 p^{-k delta} cos(k t log p) >= 0 (`fake_vonMangoldt_bracket_nonneg`).
  E    The fake as an ANALYTIC object built from Mathlib's riemannZeta:
       * a_n = sum_{d | n} g(d) with g multiplicative (`fakeCoeff_eq_zeta_mul_gFun`);
       * Euler product of 1/zeta_{>=X} (`hasProd_inv_zetaTail`);
       * sum a_n n^{-s} = F(s) := zeta(s)/(zeta_{>=X}(s+delta-it) zeta_{>=X}(s+delta+it)) for
         Re s > 1 (`LSeries_fakeCoeff_eq_poleShadow`);
       * F holomorphic on {Re s > 1 - delta} \ {1} (`poleShadow_differentiableAt_of_re`), with the
         same zeros as zeta there (`poleShadow_eq_zero_iff`), a simple pole at 1 with nonzero
         residue (`poleShadow_residue`), holomorphic on a punctured neighbourhood of
         s0 = 1 - delta + it (`poleShadow_eventually_differentiableAt`), and F(s) -> 0 as s -> s0
         (`poleShadow_tendsto_zero`); F(s)/(s - s0) has an explicit limit, nonzero iff
         zeta(s0) != 0 (`poleShadow_div_tendsto`, `poleShadow_simple_zero`);
       * t = 0: an exact DOUBLE real zero at 1 - delta (`poleShadow_real_double_zero`);
       * HEADLINE `finite_data_no_zero_free_region`: for all X > 1, delta > 0, t != 0 there is such
         an Euler product agreeing with zeta's coefficients below X and vanishing at 1 - delta + it;
       * `mty_fake`: agreement with zeta's coefficients for all n < T^A (A >= 3.86) is compatible
         with a zero at height T inside sigma >= 1 - 1/(5.558691 log T);
       * EXPULSION estimate: left of its zero the real fake is exponentially large,
         |F(sigma)| >= (sigma/(1-sigma) - 1/2) exp(2 sum_{p<X} p^{-(sigma+eta)}) /
         ((sigma+eta)/(1-sigma-eta) + 1/2)^2 (`poleShadow_real_exp_large`), hence any uniform
         counting constant K it could carry is exponentially large (`expulsion_of_transfer_bound`,
         conditional on the transfer inequality, which is paper-level).
  F    The two window tests are blind to the fake below X (`fake_window_tests_blind`).

  WHAT IT DOES NOT ESTABLISH.
  * Anything about the zeros of zeta, or any zero-free region for zeta.
  * The passage FE <=> distributional Poisson identity nu^ = nu (paper-level, classical).
  * Riemann's theta relation for the fake to precision e^{-pi X^2/Y} on [1/Y, Y] (paper proof plus
    numerics in telperion/research/crux2_rigidity-rate), and the C^{-k} window-defect bound.
  * The identification of the local brackets with the log-derivative coefficients of F (P2 at the
    analytic level): the brackets are kernel-checked, -F'/F = sum Lambda_F n^{-s} is paper-level.
  * The transfer lemma, the rescaling/grafting lemmas and the Broucke-based rate cap (paper-level;
    the cap rests on Broucke, arXiv:2507.13780, Thm 1.6, checked by reading, not formalized).
  * The intermediate-regime question (precision t^A, A < 1/(1-theta), uniform K): OPEN.
-/
import Mathlib
import LowHeightBox

open Real

namespace Crux2RigidityRate


/-! ## A. The Fourier pair triangle <-> sinc^2 -/

/-- Antiderivative of `(1 - ξ) cos(2π x ξ)` (valid for `x ≠ 0`). -/
noncomputable def triAnti (x ξ : ℝ) : ℝ :=
  (1 - ξ) * Real.sin (2 * π * x * ξ) / (2 * π * x) - Real.cos (2 * π * x * ξ) / (4 * π ^ 2 * x ^ 2)

lemma triAnti_hasDerivAt (x : ℝ) (hx : x ≠ 0) (ξ : ℝ) :
    HasDerivAt (triAnti x) ((1 - ξ) * Real.cos (2 * π * x * ξ)) ξ := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hlin : HasDerivAt (fun ξ : ℝ => 2 * π * x * ξ) (2 * π * x) ξ := by
    simpa using (hasDerivAt_id ξ).const_mul (2 * π * x)
  have hsin : HasDerivAt (fun ξ : ℝ => Real.sin (2 * π * x * ξ))
      (Real.cos (2 * π * x * ξ) * (2 * π * x)) ξ :=
    (Real.hasDerivAt_sin _).comp ξ hlin
  have hcos : HasDerivAt (fun ξ : ℝ => Real.cos (2 * π * x * ξ))
      (-Real.sin (2 * π * x * ξ) * (2 * π * x)) ξ :=
    (Real.hasDerivAt_cos _).comp ξ hlin
  have h1 : HasDerivAt (fun ξ : ℝ => 1 - ξ) (-1) ξ := (hasDerivAt_id' ξ).const_sub 1
  have hprod := (h1.fun_mul hsin).div_const (2 * π * x)
  have hq := hcos.div_const (4 * π ^ 2 * x ^ 2)
  have hall := hprod.fun_sub hq
  have hfun : triAnti x = fun ξ : ℝ => (1 - ξ) * Real.sin (2 * π * x * ξ) / (2 * π * x)
      - Real.cos (2 * π * x * ξ) / (4 * π ^ 2 * x ^ 2) := by
    funext ξ; rfl
  rw [hfun]
  refine hall.congr_deriv ?_
  field_simp
  ring

/-- One-sided cosine form of the triangle/sinc^2 pair. -/
theorem tri_cos_integral (x : ℝ) (hx : x ≠ 0) :
    ∫ ξ in (0 : ℝ)..1, (1 - ξ) * Real.cos (2 * π * x * ξ)
      = Real.sin (π * x) ^ 2 / (2 * π ^ 2 * x ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ξ _ => triAnti_hasDerivAt x hx ξ)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hcos : Real.cos (2 * π * x) = 1 - 2 * Real.sin (π * x) ^ 2 := by
    rw [show 2 * π * x = 2 * (π * x) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  simp only [triAnti, mul_one, mul_zero, Real.sin_zero, Real.cos_zero, sub_self, zero_mul,
    zero_div, sub_zero]
  rw [hcos]
  field_simp
  ring

/-- Two-sided form: `∫_{-1}^{1} (1-|ξ|) cos(2π x ξ) dξ = sin(πx)^2/(π^2 x^2)`. -/
theorem tri_cos_integral_symm (x : ℝ) (hx : x ≠ 0) :
    ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) * Real.cos (2 * π * x * ξ)
      = Real.sin (π * x) ^ 2 / (π ^ 2 * x ^ 2) := by
  have hcont : Continuous (fun ξ : ℝ => (1 - |ξ|) * Real.cos (2 * π * x * ξ)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h_right : ∫ ξ in (0 : ℝ)..1, (1 - |ξ|) * Real.cos (2 * π * x * ξ)
      = ∫ ξ in (0 : ℝ)..1, (1 - ξ) * Real.cos (2 * π * x * ξ) := by
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le zero_le_one] at hξ
    simp only [abs_of_nonneg hξ.1]
  have h_left : ∫ ξ in (-1 : ℝ)..0, (1 - |ξ|) * Real.cos (2 * π * x * ξ)
      = ∫ ξ in (0 : ℝ)..1, (1 - ξ) * Real.cos (2 * π * x * ξ) := by
    have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (fun ξ : ℝ => (1 - |ξ|) * Real.cos (2 * π * x * ξ))
    simp only [neg_zero] at hneg
    rw [← hneg]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le zero_le_one] at hξ
    simp only [abs_neg, abs_of_nonneg hξ.1, mul_neg, Real.cos_neg]
  rw [h_left, h_right, tri_cos_integral x hx]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `∫_{-1}^{1} (1-|ξ|) dξ = 1`. -/
theorem tri_integral_one : ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) = 1 := by
  have hcont : Continuous (fun ξ : ℝ => 1 - |ξ|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hR : ∫ ξ in (0 : ℝ)..1, (1 - |ξ|) = ∫ ξ in (0 : ℝ)..1, (1 - ξ) := by
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le zero_le_one] at hξ
    simp only [abs_of_nonneg hξ.1]
  have hL : ∫ ξ in (-1 : ℝ)..0, (1 - |ξ|) = ∫ ξ in (0 : ℝ)..1, (1 - ξ) := by
    have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (fun ξ : ℝ => 1 - |ξ|)
    simp only [neg_zero] at hneg
    rw [← hneg]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le zero_le_one] at hξ
    simp only [abs_neg, abs_of_nonneg hξ.1]
  have h01 : ∫ ξ in (0 : ℝ)..1, (1 - ξ) = 1 / 2 := by
    have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun ξ : ℝ => ξ - ξ ^ 2 / 2) (1 - ξ) ξ := by
      intro ξ _
      have := ((hasDerivAt_id' ξ).fun_sub ((hasDerivAt_pow 2 ξ).div_const 2))
      refine this.congr_deriv ?_
      norm_num
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_num
  rw [hL, hR, h01]
  norm_num

/-! ## B. Jordan-type bound -/

/-- `4 ‖x‖^2 ≤ sin(πx)^2`, with `‖x‖ = |x - round x|` the distance to `ℤ`. Sharp at half-integers. -/
theorem four_dist_sq_le_sin_sq (x : ℝ) : 4 * (x - round x) ^ 2 ≤ Real.sin (π * x) ^ 2 := by
  have hy2 : |x - round x| ≤ 1 / 2 := abs_sub_round x
  have hper : Real.sin (π * x) ^ 2 = Real.sin (π * (x - round x)) ^ 2 := by
    have hx : π * x = π * (x - round x) + ((round x : ℤ) : ℝ) * π := by ring
    rw [hx, Real.sin_add_int_mul_pi, mul_pow]
    have h1 : ((-1 : ℝ) ^ (round x)) ^ 2 = 1 := by
      rw [sq, ← mul_zpow]; norm_num
    rw [h1, one_mul]
  have habs : Real.sin (π * (x - round x)) ^ 2 = Real.sin (π * |x - round x|) ^ 2 := by
    rcases abs_cases (x - round x) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, neg_sq]
  have hj : 2 / π * (π * |x - round x|) ≤ Real.sin (π * |x - round x|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos, abs_nonneg (x - round x)])
  have hj' : 2 * |x - round x| ≤ Real.sin (π * |x - round x|) := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    have : 2 / π * (π * |x - round x|) = 2 * |x - round x| := by field_simp
    linarith
  have h0 : 0 ≤ 2 * |x - round x| := by positivity
  calc 4 * (x - round x) ^ 2 = (2 * |x - round x|) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    _ ≤ Real.sin (π * |x - round x|) ^ 2 := by nlinarith
    _ = Real.sin (π * x) ^ 2 := by rw [hper, habs]

/-! ## C. The rigidity identity for finite even measures -/

variable {ι : Type*}

/-- The triangle pairing `⟨ν̂, Λ⟩ = ∫_{-1}^{1} (1-|ξ|) ν̂(ξ) dξ` of the Fourier transform
`ν̂(ξ) = r + Σ_{i∈s} 2 w_i cos(2π x_i ξ)` of `ν = r δ₀ + Σ_{i∈s} w_i (δ_{x_i} + δ_{-x_i})`. -/
noncomputable def triPairHat (s : Finset ι) (r : ℝ) (w x : ι → ℝ) : ℝ :=
  ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) * (r + ∑ i ∈ s, 2 * w i * Real.cos (2 * π * x i * ξ))

/-- The triangle pairing `⟨ν, Λ⟩` of the measure itself, `Λ(y) = max (1-|y|) 0`. -/
noncomputable def triPair (s : Finset ι) (r : ℝ) (w x : ι → ℝ) : ℝ :=
  r * max (1 - |(0 : ℝ)|) 0 + ∑ i ∈ s, w i * (max (1 - |x i|) 0 + max (1 - |-x i|) 0)

/-- The atom-by-atom evaluation of `⟨ν̂, Λ⟩`. -/
theorem triPairHat_eq (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) :
    triPairHat s r w x
      = r + ∑ i ∈ s, 2 * w i * (Real.sin (π * x i) ^ 2 / (π ^ 2 * x i ^ 2)) := by
  unfold triPairHat
  have hsplit : (fun ξ : ℝ => (1 - |ξ|) * (r + ∑ i ∈ s, 2 * w i * Real.cos (2 * π * x i * ξ)))
      = fun ξ : ℝ => r * (1 - |ξ|)
          + ∑ i ∈ s, 2 * w i * ((1 - |ξ|) * Real.cos (2 * π * x i * ξ)) := by
    funext ξ
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro i _; ring
  rw [hsplit, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, tri_integral_one, mul_one,
      intervalIntegral.integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_const_mul, tri_cos_integral_symm (x i) (hx i hi)]
    · intro i _
      apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable
    apply continuous_finsetSum; intro i _; fun_prop

/-- With the Beurling gap `|x_i| ≥ 1`, `⟨ν, Λ⟩ = r`. -/
theorem triPair_eq_of_gap (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (hx : ∀ i ∈ s, 1 ≤ |x i|) :
    triPair s r w x = r := by
  unfold triPair
  have hsum : ∑ i ∈ s, w i * (max (1 - |x i|) 0 + max (1 - |-x i|) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h1 : max (1 - |x i|) 0 = 0 := max_eq_right (by linarith [hx i hi])
    have h2 : max (1 - |-x i|) 0 = 0 := by rw [abs_neg]; exact h1
    rw [h1, h2]; ring
  rw [hsum]; simp

/-- **The rigidity identity.** Under the Beurling gap, the triangle-tested functional-equation
defect `⟨ν̂ - ν, Λ⟩` equals the `sinc^2`-weighted mass of `ν` off the origin. -/
theorem window_defect_identity (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (hx : ∀ i ∈ s, 1 ≤ |x i|) :
    triPairHat s r w x - triPair s r w x
      = ∑ i ∈ s, 2 * w i * (Real.sin (π * x i) ^ 2 / (π ^ 2 * x i ^ 2)) := by
  have hne : ∀ i ∈ s, x i ≠ 0 := fun i hi h => by
    have := hx i hi; rw [h, abs_zero] at this; linarith
  rw [triPairHat_eq s r w x hne, triPair_eq_of_gap s r w x hx]
  ring

/-- **Extremal point-mass inequality (finite form).** For nonnegative weights at nonzero points,
the atom `r` at the origin is at most the triangle average `⟨ν̂, Λ⟩` of the Fourier transform. -/
theorem atom_le_triPairHat (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0)
    (hw : ∀ i ∈ s, 0 ≤ w i) : r ≤ triPairHat s r w x := by
  rw [triPairHat_eq s r w x hx]
  have : 0 ≤ ∑ i ∈ s, 2 * w i * (Real.sin (π * x i) ^ 2 / (π ^ 2 * x i ^ 2)) := by
    apply Finset.sum_nonneg
    intro i hi
    have := hw i hi
    positivity
  linarith

/-- Pointwise stability: `sin(πx)^2/(π^2 x^2) ≥ (4/π^2) ‖x‖^2 / x^2`. -/
lemma sinc_sq_ge (y : ℝ) (hy : y ≠ 0) :
    (4 / π ^ 2) * ((y - round y) ^ 2 / y ^ 2) ≤ Real.sin (π * y) ^ 2 / (π ^ 2 * y ^ 2) := by
  have hj := four_dist_sq_le_sin_sq y
  have hπ : 0 < π ^ 2 := by positivity
  have hy2 : 0 < y ^ 2 := by positivity
  rw [show (4 / π ^ 2) * ((y - round y) ^ 2 / y ^ 2) = (4 * (y - round y) ^ 2) / (π ^ 2 * y ^ 2) by
    field_simp]
  exact div_le_div_of_nonneg_right hj (by positivity)

/-- **Quantitative rigidity with the explicit constant `8/π^2`.** -/
theorem window_defect_stability (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (hx : ∀ i ∈ s, 1 ≤ |x i|)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (8 / π ^ 2) * ∑ i ∈ s, w i * ((x i - round (x i)) ^ 2 / x i ^ 2)
      ≤ triPairHat s r w x - triPair s r w x := by
  rw [window_defect_identity s r w x hx, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hne : x i ≠ 0 := fun h => by have := hx i hi; rw [h, abs_zero] at this; linarith
  have h1 := sinc_sq_ge (x i) hne
  have hwi := hw i hi
  have : (8 / π ^ 2) * (w i * ((x i - round (x i)) ^ 2 / x i ^ 2))
      = 2 * w i * ((4 / π ^ 2) * ((x i - round (x i)) ^ 2 / x i ^ 2)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Rigidity.** If the triangle-tested FE defect vanishes and all weights are positive, every
atom sits at an integer. -/
theorem window_defect_rigidity (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (hx : ∀ i ∈ s, 1 ≤ |x i|)
    (hw : ∀ i ∈ s, 0 < w i) (h0 : triPairHat s r w x = triPair s r w x) :
    ∀ i ∈ s, x i = round (x i) := by
  have hstab := window_defect_stability s r w x hx (fun i hi => (hw i hi).le)
  rw [h0, sub_self] at hstab
  have hπ : 0 < 8 / π ^ 2 := by positivity
  have hnn : ∀ i ∈ s, 0 ≤ w i * ((x i - round (x i)) ^ 2 / x i ^ 2) := fun i hi => by
    have := (hw i hi).le; positivity
  have hsum0 : ∑ i ∈ s, w i * ((x i - round (x i)) ^ 2 / x i ^ 2) = 0 := by
    have hle : ∑ i ∈ s, w i * ((x i - round (x i)) ^ 2 / x i ^ 2) ≤ 0 := by
      by_contra hc
      have hc' := lt_of_not_ge hc
      have := mul_pos hπ hc'
      linarith
    exact le_antisymm hle (Finset.sum_nonneg hnn)
  intro i hi
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 i hi
  have hne : x i ≠ 0 := fun h => by have := hx i hi; rw [h, abs_zero] at this; linarith
  have hx2 : 0 < x i ^ 2 := by positivity
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h (hw i hi).ne'
  · rw [div_eq_zero_iff] at h
    rcases h with h | h
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linarith
    · exact absurd h hx2.ne'

/-- **Counting form.** Weight at distance `≥ η` from `ℤ` inside `|x| ≤ X` is at most
`(π^2/8)(X^2/η^2)` times the triangle-tested FE defect. -/
theorem window_defect_counting (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (hx : ∀ i ∈ s, 1 ≤ |x i|)
    (hw : ∀ i ∈ s, 0 ≤ w i) (X η : ℝ) (hη : 0 < η) :
    ∑ i ∈ s.filter (fun i => |x i| ≤ X ∧ η ≤ |x i - round (x i)|), w i
      ≤ (π ^ 2 / 8) * (X ^ 2 / η ^ 2) * (triPairHat s r w x - triPair s r w x) := by
  have hstab := window_defect_stability s r w x hx hw
  have hπ : 0 < π ^ 2 := by positivity
  have hη2 : 0 < η ^ 2 := by positivity
  -- each filtered term: w_i ≤ (X^2/η^2) w_i ‖x_i‖^2/x_i^2
  have hterm : ∀ i ∈ s.filter (fun i => |x i| ≤ X ∧ η ≤ |x i - round (x i)|),
      w i ≤ (X ^ 2 / η ^ 2) * (w i * ((x i - round (x i)) ^ 2 / x i ^ 2)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨his, hX, hηi⟩ := hi
    have hwi := hw i his
    have hne : x i ≠ 0 := fun h => by have := hx i his; rw [h, abs_zero] at this; linarith
    have hx2 : 0 < x i ^ 2 := by positivity
    have hxX : x i ^ 2 ≤ X ^ 2 := by
      have h1 : |x i| ^ 2 ≤ X ^ 2 := by
        have : 0 ≤ |x i| := abs_nonneg _
        nlinarith
      rwa [sq_abs] at h1
    have hd : η ^ 2 ≤ (x i - round (x i)) ^ 2 := by
      have h1 : η ^ 2 ≤ |x i - round (x i)| ^ 2 := by nlinarith
      rwa [sq_abs] at h1
    -- (X^2/η^2) * ((x-r)^2/x^2) ≥ 1
    have hratio : 1 ≤ (X ^ 2 / η ^ 2) * ((x i - round (x i)) ^ 2 / x i ^ 2) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      nlinarith
    calc w i = w i * 1 := by ring
      _ ≤ w i * ((X ^ 2 / η ^ 2) * ((x i - round (x i)) ^ 2 / x i ^ 2)) :=
          mul_le_mul_of_nonneg_left hratio hwi
      _ = (X ^ 2 / η ^ 2) * (w i * ((x i - round (x i)) ^ 2 / x i ^ 2)) := by ring
  have hsub : ∑ i ∈ s.filter (fun i => |x i| ≤ X ∧ η ≤ |x i - round (x i)|),
      (w i * ((x i - round (x i)) ^ 2 / x i ^ 2))
      ≤ ∑ i ∈ s, (w i * ((x i - round (x i)) ^ 2 / x i ^ 2)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i hi _
    have := hw i hi
    positivity
  calc ∑ i ∈ s.filter (fun i => |x i| ≤ X ∧ η ≤ |x i - round (x i)|), w i
      ≤ ∑ i ∈ s.filter (fun i => |x i| ≤ X ∧ η ≤ |x i - round (x i)|),
          (X ^ 2 / η ^ 2) * (w i * ((x i - round (x i)) ^ 2 / x i ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = (X ^ 2 / η ^ 2) * ∑ i ∈ s.filter (fun i => |x i| ≤ X ∧ η ≤ |x i - round (x i)|),
          (w i * ((x i - round (x i)) ^ 2 / x i ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ (X ^ 2 / η ^ 2) * ∑ i ∈ s, (w i * ((x i - round (x i)) ^ 2 / x i ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hsub; positivity
    _ = (π ^ 2 / 8) * (X ^ 2 / η ^ 2) *
          ((8 / π ^ 2) * ∑ i ∈ s, (w i * ((x i - round (x i)) ^ 2 / x i ^ 2))) := by
        field_simp
    _ ≤ (π ^ 2 / 8) * (X ^ 2 / η ^ 2) * (triPairHat s r w x - triPair s r w x) := by
        apply mul_le_mul_of_nonneg_left hstab; positivity

/-! ## D. Local positivity of the pole-shadow fakes -/

/-- The von Mangoldt weight of the fake at `p^k`, `p ≥ X`, is `log p · (1 - 2 p^{-kδ} cos θ)`;
its bracket is `≥ 0` as soon as `p^δ ≥ 2`. -/
theorem fake_vonMangoldt_bracket_nonneg (p δ θ : ℝ) (k : ℕ) (hp : 1 < p) (hδ : 0 < δ)
    (h2 : 2 ≤ p ^ δ) (hk : 1 ≤ k) : 0 ≤ 1 - 2 * p ^ (-((k : ℝ) * δ)) * Real.cos θ := by
  have hp0 : 0 < p := by linarith
  have hkδ : δ ≤ (k : ℝ) * δ := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hmono : p ^ δ ≤ p ^ ((k : ℝ) * δ) := Real.rpow_le_rpow_of_exponent_le hp.le hkδ
  have hpos : 0 < p ^ ((k : ℝ) * δ) := Real.rpow_pos_of_pos hp0 _
  have hinv : p ^ (-((k : ℝ) * δ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hp0.le, inv_eq_one_div]
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  have hnn : 0 ≤ p ^ (-((k : ℝ) * δ)) := (Real.rpow_pos_of_pos hp0 _).le
  have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
  nlinarith

/-- The local factor `(1 - αT)(1 - ᾱT)/(1 - T)` with `α = a + ib`: exact truncation identity
exhibiting its power-series coefficients `1, 1 - 2a, c, c, ..., c` with `c = (1-a)^2 + b^2`. -/
theorem fake_local_factor_identity (a b T : ℝ) (J : ℕ) (hJ : 1 ≤ J) :
    1 - 2 * a * T + (a ^ 2 + b ^ 2) * T ^ 2
      = (1 - T) * (1 + (1 - 2 * a) * T
          + ((1 - a) ^ 2 + b ^ 2) * ∑ j ∈ Finset.Ico 2 (J + 1), T ^ j)
        + ((1 - a) ^ 2 + b ^ 2) * T ^ (J + 1) := by
  induction J, hJ using Nat.le_induction with
  | base => simp; ring
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n + 1)]
    rw [ih]
    ring

/-- The local coefficients of the fake are nonnegative when `|α|^2 = a^2 + b^2 ≤ 1/4`. -/
theorem fake_local_coeffs_nonneg (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1 / 4) :
    0 ≤ 1 - 2 * a ∧ 0 ≤ (1 - a) ^ 2 + b ^ 2 := by
  constructor
  · nlinarith [sq_nonneg b, sq_nonneg (a - 1 / 2)]
  · positivity

/-- Local coefficient of the pole-shadow fake at `p^j`, `j ≥ 1`: `1` below `X`; above `X`,
`c_p(1) = 1 - 2 p^{-δ} cos(t log p)` and `c_p(j ≥ 2) = |1 - p^{-δ+it}|^2`. -/
noncomputable def fakeLocal (X δ t : ℝ) (p j : ℕ) : ℝ :=
  if (p : ℝ) < X then 1
  else if j = 1 then 1 - 2 * (p : ℝ) ^ (-δ) * Real.cos (t * Real.log p)
  else (1 - (p : ℝ) ^ (-δ) * Real.cos (t * Real.log p)) ^ 2
        + ((p : ℝ) ^ (-δ) * Real.sin (t * Real.log p)) ^ 2

/-- Dirichlet coefficients of the fake (multiplicative): `a n = ∏_{p^j ∥ n} c_p(j)`. -/
noncomputable def fakeCoeff (X δ t : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, fakeLocal X δ t p (n.factorization p)

theorem fakeLocal_nonneg (X δ t : ℝ) (hX : 1 < X) (hδ : 0 < δ) (h2 : 2 ≤ X ^ δ) (p j : ℕ) :
    0 ≤ fakeLocal X δ t p j := by
  unfold fakeLocal
  split_ifs with h1 hj
  · norm_num
  · have hXp : X ≤ (p : ℝ) := not_lt.mp h1
    have hp : 1 < (p : ℝ) := lt_of_lt_of_le hX hXp
    have hpδ : 2 ≤ (p : ℝ) ^ δ := le_trans h2 (Real.rpow_le_rpow (by linarith) hXp hδ.le)
    have := fake_vonMangoldt_bracket_nonneg (p : ℝ) δ (t * Real.log p) 1 hp hδ hpδ le_rfl
    simpa using this
  · positivity

/-- The fake's coefficients are nonnegative. -/
theorem fakeCoeff_nonneg (X δ t : ℝ) (hX : 1 < X) (hδ : 0 < δ) (h2 : 2 ≤ X ^ δ) (n : ℕ) :
    0 ≤ fakeCoeff X δ t n :=
  Finset.prod_nonneg (fun p _ => fakeLocal_nonneg X δ t hX hδ h2 p _)

/-- The fake's coefficients equal those of `ζ` (namely `1`) for every `n < X`. -/
theorem fakeCoeff_eq_one_of_lt (X δ t : ℝ) (n : ℕ) (hn : (n : ℝ) < X) :
    fakeCoeff X δ t n = 1 := by
  unfold fakeCoeff
  apply Finset.prod_eq_one
  intro p hp
  have hn0 : n ≠ 0 := by rintro rfl; simp at hp
  have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)
  have hpX : (p : ℝ) < X := lt_of_le_of_lt (by exact_mod_cast hpn) hn
  simp [fakeLocal, hpX]

/-! ## C'. The multiplicity half: modulated triangles -/

/-- `sinc(π y)^2` with the value `1` at `y = 0`. -/
noncomputable def sincSq (y : ℝ) : ℝ := if y = 0 then 1 else Real.sin (π * y) ^ 2 / (π ^ 2 * y ^ 2)

lemma sincSq_int_ne_zero (m : ℤ) (hm : m ≠ 0) : sincSq (m : ℝ) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  simp only [sincSq, hm', ↓reduceIte]
  have : Real.sin (π * (m : ℝ)) = 0 := by
    rw [mul_comm]; exact Real.sin_int_mul_pi m
  rw [this]; simp

/-- The triangle/sinc^2 pair for every real frequency (value `1` at `0`). -/
theorem tri_cos_integral_all (y : ℝ) :
    ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) * Real.cos (2 * π * y * ξ) = sincSq y := by
  by_cases hy : y = 0
  · subst hy
    simp only [sincSq, ↓reduceIte, mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact tri_integral_one
  · rw [tri_cos_integral_symm y hy]; simp [sincSq, hy]

lemma cos_mul_cos_eq (a b : ℝ) :
    Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Modulated triangle: `∫_{-1}^{1} Λ(ξ) cos(2πxξ) cos(2πmξ) dξ = (sinc²(x-m) + sinc²(x+m))/2`. -/
theorem tri_cos_cos_integral (x m : ℝ) :
    ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) * (Real.cos (2 * π * x * ξ) * Real.cos (2 * π * m * ξ))
      = (sincSq (x - m) + sincSq (x + m)) / 2 := by
  have hfun : (fun ξ : ℝ => (1 - |ξ|) * (Real.cos (2 * π * x * ξ) * Real.cos (2 * π * m * ξ)))
      = fun ξ : ℝ => ((1 - |ξ|) * Real.cos (2 * π * (x - m) * ξ)
          + (1 - |ξ|) * Real.cos (2 * π * (x + m) * ξ)) / 2 := by
    funext ξ
    rw [cos_mul_cos_eq, show 2 * π * x * ξ - 2 * π * m * ξ = 2 * π * (x - m) * ξ by ring,
      show 2 * π * x * ξ + 2 * π * m * ξ = 2 * π * (x + m) * ξ by ring]
    ring
  rw [hfun, intervalIntegral.integral_div, intervalIntegral.integral_add,
    tri_cos_integral_all, tri_cos_integral_all]
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

/-- **Multiplicity identity (finite form).** The modulated triangle pairing of `ν̂` at frequency `m`
equals the `sinc^2`-weighted mass of `ν` around `± m`:
`⟨ν̂, Λ cos(2πm·)⟩ = r sinc²(m) + Σ_i w_i (sinc²(x_i - m) + sinc²(x_i + m))`.
For an integer `m ≠ 0` and integer atoms this reads off the multiplicity at `m`; an exact FE window
(`ν̂ = r δ₀` on `(-1,1)`) forces it to equal `r`. -/
theorem triPairHat_mod_eq (s : Finset ι) (r : ℝ) (w x : ι → ℝ) (m : ℝ) :
    ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) * ((r + ∑ i ∈ s, 2 * w i * Real.cos (2 * π * x i * ξ))
        * Real.cos (2 * π * m * ξ))
      = r * sincSq m + ∑ i ∈ s, w i * (sincSq (x i - m) + sincSq (x i + m)) := by
  have hsplit : (fun ξ : ℝ => (1 - |ξ|) * ((r + ∑ i ∈ s, 2 * w i * Real.cos (2 * π * x i * ξ))
        * Real.cos (2 * π * m * ξ)))
      = fun ξ : ℝ => r * ((1 - |ξ|) * Real.cos (2 * π * m * ξ))
          + ∑ i ∈ s, 2 * w i * ((1 - |ξ|) * (Real.cos (2 * π * x i * ξ) * Real.cos (2 * π * m * ξ))) := by
    funext ξ
    rw [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro i _; ring
  rw [hsplit, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, tri_cos_integral_all,
      intervalIntegral.integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_const_mul, tri_cos_cos_integral]
      ring
    · intro i _
      apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable
    apply continuous_finsetSum; intro i _; fun_prop

/-- For integer atoms `n_i ≥ 1` and an integer `m ≥ 1`, the modulated pairing is exactly the
multiplicity `Σ_{n_i = m} w_i`. -/
theorem triPairHat_mod_int (s : Finset ι) (r : ℝ) (w : ι → ℝ) (n : ι → ℤ) (m : ℤ)
    (hn : ∀ i ∈ s, 1 ≤ n i) (hm : 1 ≤ m) :
    ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) * ((r + ∑ i ∈ s, 2 * w i * Real.cos (2 * π * (n i : ℝ) * ξ))
        * Real.cos (2 * π * (m : ℝ) * ξ))
      = ∑ i ∈ s.filter (fun i => n i = m), w i := by
  rw [triPairHat_mod_eq s r w (fun i => (n i : ℝ)) (m : ℝ)]
  rw [sincSq_int_ne_zero m (by omega), mul_zero, zero_add, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have h2 : sincSq ((n i : ℝ) + m) = 0 := by
    have := sincSq_int_ne_zero (n i + m) (by have := hn i hi; omega)
    simpa using this
  by_cases h : n i = m
  · have h0 : sincSq ((n i : ℝ) - m) = 1 := by
      have hz : (n i : ℝ) - m = 0 := by rw [h]; ring
      simp only [sincSq, hz, ↓reduceIte]
    rw [h0, h2]; simp [h]
  · have h1 : sincSq ((n i : ℝ) - m) = 0 := by
      have := sincSq_int_ne_zero (n i - m) (sub_ne_zero.mpr h)
      simpa using this
    simp [h, h1, h2]

section PoleShadow

open Complex Filter Topology

/-! ## E. The pole-shadow fake as an analytic function (Mathlib's `riemannZeta`)

All objects below are built from Mathlib's `riemannZeta` (meromorphic continuation, residue `1` at
`s = 1`, Euler product on `Re s > 1`, nonvanishing on `Re s ≥ 1`).  Section E0 builds multiplicative
functions from local data; E1 writes the fake's coefficients as `1 ⋆ g`; E2 builds
`ζ_{≥X}(w) = ζ(w) ∏_{p<X}(1 - p^{-w})` and the Euler product of `1/ζ_{≥X}`; E3 identifies the
fake's Dirichlet series with `F = ζ(s)/(ζ_{≥X}(s+δ-it) ζ_{≥X}(s+δ+it))` on `Re s > 1`; E4 proves
the zero at `s₀ = 1 - δ + it`, its order, holomorphy, the zero set in `Re s > 1 - δ`, and the pole
at `1`; E5 the real double zero, multiplicativity, and the packaged headline statements; E6 the
exponential size of the real fake left of its zero (the expulsion estimate). -/

/-! ### E0. Multiplicative functions from local data -/

/-- The arithmetic function `n ↦ ∏_{p^j ∥ n} loc p j` (value `0` at `0`). -/
noncomputable def ofLocal {R : Type*} [CommMonoidWithZero R] (loc : ℕ → ℕ → R) :
    ArithmeticFunction R where
  toFun n := if n = 0 then 0 else n.factorization.prod loc
  map_zero' := by simp

lemma ofLocal_apply {R : Type*} [CommMonoidWithZero R] (loc : ℕ → ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    ofLocal loc n = n.factorization.prod loc := by
  simp [ofLocal, hn]

theorem ofLocal_isMultiplicative {R : Type*} [CommMonoidWithZero R] (loc : ℕ → ℕ → R) :
    (ofLocal loc).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [ofLocal], fun {m n} hm hn hmn => ?_⟩
  rw [ofLocal_apply loc (mul_ne_zero hm hn), ofLocal_apply loc hm, ofLocal_apply loc hn,
    Nat.factorization_mul hm hn]
  apply Finsupp.prod_add_index_of_disjoint
  rw [Nat.support_factorization, Nat.support_factorization]
  exact hmn.disjoint_primeFactors

theorem ofLocal_prime_pow {R : Type*} [CommMonoidWithZero R] (loc : ℕ → ℕ → R)
    (h0 : ∀ p, loc p 0 = 1) {p : ℕ} (hp : p.Prime) (j : ℕ) : ofLocal loc (p ^ j) = loc p j := by
  rw [ofLocal_apply loc (pow_ne_zero j hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (h0 p)]

/-! ### E1. The fake's coefficients as a Dirichlet convolution `1 ⋆ g` -/

/-- `α_p = p^{-δ + i t}`. -/
noncomputable def alphaP (δ t : ℝ) (p : ℕ) : ℂ := (p : ℂ) ^ (-((δ : ℂ) - t * I))

/-- `ᾱ_p = p^{-δ - i t}`. -/
noncomputable def alphaBarP (δ t : ℝ) (p : ℕ) : ℂ := (p : ℂ) ^ (-((δ : ℂ) + t * I))

lemma alphaP_eq (δ t : ℝ) {p : ℕ} (hp : 0 < p) :
    alphaP δ t p = (((p : ℝ) ^ (-δ) : ℝ) : ℂ)
      * ((Real.cos (t * Real.log p) : ℂ) + (Real.sin (t * Real.log p) : ℂ) * I) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  unfold alphaP
  rw [cpow_def_of_ne_zero hp', ← natCast_log, Real.rpow_def_of_pos hpr]
  have : ((Real.log (p : ℝ) : ℝ) : ℂ) * -((δ : ℂ) - t * I)
      = ((Real.log p * -δ : ℝ) : ℂ) + ((t * Real.log p : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp]
  push_cast
  ring

lemma alphaBarP_eq (δ t : ℝ) {p : ℕ} (hp : 0 < p) :
    alphaBarP δ t p = (((p : ℝ) ^ (-δ) : ℝ) : ℂ)
      * ((Real.cos (t * Real.log p) : ℂ) - (Real.sin (t * Real.log p) : ℂ) * I) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  unfold alphaBarP
  rw [cpow_def_of_ne_zero hp', ← natCast_log, Real.rpow_def_of_pos hpr]
  have : ((Real.log (p : ℝ) : ℝ) : ℂ) * -((δ : ℂ) + t * I)
      = ((Real.log p * -δ : ℝ) : ℂ) + ((-(t * Real.log p) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

lemma alpha_add (δ t : ℝ) {p : ℕ} (hp : 0 < p) :
    alphaP δ t p + alphaBarP δ t p
      = ((2 * (p : ℝ) ^ (-δ) * Real.cos (t * Real.log p) : ℝ) : ℂ) := by
  rw [alphaP_eq δ t hp, alphaBarP_eq δ t hp]
  push_cast
  ring

lemma alpha_mul (δ t : ℝ) {p : ℕ} (hp : 0 < p) :
    alphaP δ t p * alphaBarP δ t p = ((((p : ℝ) ^ (-δ)) ^ 2 : ℝ) : ℂ) := by
  rw [alphaP_eq δ t hp, alphaBarP_eq δ t hp, Complex.ofReal_pow]
  have h' : ((Real.cos (t * Real.log p) : ℂ)) ^ 2 + ((Real.sin (t * Real.log p) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (t * Real.log p)
  linear_combination ((((p : ℝ) ^ (-δ) : ℝ) : ℂ)) ^ 2 * h'
    + (-((((p : ℝ) ^ (-δ) : ℝ) : ℂ)) ^ 2 * ((Real.sin (t * Real.log p) : ℂ)) ^ 2) * Complex.I_sq

/-- Local data of `g`, whose local factor is `(1 - α_p T)(1 - ᾱ_p T)` for `p ≥ X` and `1` below. -/
noncomputable def gLoc (X δ t : ℝ) (p j : ℕ) : ℂ :=
  if j = 0 then 1
  else if (p : ℝ) < X then 0
  else if j = 1 then -(alphaP δ t p + alphaBarP δ t p)
  else if j = 2 then alphaP δ t p * alphaBarP δ t p
  else 0

/-- The multiplicative function `g` with `L(g, s) = ∏_{p ≥ X} (1 - α_p p^{-s})(1 - ᾱ_p p^{-s})`. -/
noncomputable def gFun (X δ t : ℝ) : ArithmeticFunction ℂ := ofLocal (gLoc X δ t)

/-- Complex local data of the fake (value `1` at exponent `0`). -/
noncomputable def fakeLocC (X δ t : ℝ) (p j : ℕ) : ℂ :=
  if j = 0 then 1 else ((fakeLocal X δ t p j : ℝ) : ℂ)

theorem fakeCoeff_eq_ofLocal (X δ t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((fakeCoeff X δ t n : ℝ) : ℂ) = ofLocal (fakeLocC X δ t) n := by
  rw [ofLocal_apply _ hn, Finsupp.prod, Nat.support_factorization, fakeCoeff]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hpos : n.factorization p ≠ 0 := by
    have := Nat.pos_of_mem_primeFactors hp
    exact (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
      (Nat.dvd_of_mem_primeFactors hp)).ne'
  simp [fakeLocC, hpos]

theorem zeta_mul_gFun_prime_pow (X δ t : ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * gFun X δ t) (p ^ j) = fakeLocC X δ t p j := by
  have hg0 : ∀ q, gLoc X δ t q 0 = 1 := fun q => by simp [gLoc]
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp only [gFun, ofLocal_prime_pow _ hg0 hp]
  have hp0 : 0 < p := hp.pos
  rcases Nat.lt_or_ge j 1 with hj | hj
  · -- j = 0
    have : j = 0 := by omega
    subst this
    simp [gLoc, fakeLocC]
  by_cases hX : (p : ℝ) < X
  · -- small prime: g vanishes at p^k, k ≥ 1
    have hsum : ∑ k ∈ Finset.range (j + 1), gLoc X δ t p k = 1 := by
      rw [Finset.sum_range_succ']
      simp [gLoc, hX]
    rw [hsum]
    simp [fakeLocC, fakeLocal, hX, show j ≠ 0 by omega]
  · rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by omega
      subst this
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, gLoc, fakeLocC, fakeLocal]
      simp only [hX, ite_false, one_ne_zero, ite_true, zero_add]
      rw [alpha_add δ t hp0]
      push_cast
      ring
    · have hsub : ∑ k ∈ Finset.range (j + 1), gLoc X δ t p k
          = ∑ k ∈ Finset.range 3, gLoc X δ t p k := by
        symm
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
        · intro k _ hk
          simp only [Finset.mem_range, not_lt] at hk
          simp [gLoc, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
      rw [hsub]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, gLoc, fakeLocC, fakeLocal]
      simp only [hX, ite_false, one_ne_zero, ite_true, zero_add, show j ≠ 0 by omega,
        show j ≠ 1 by omega, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num]
      rw [alpha_add δ t hp0, alpha_mul δ t hp0]
      have hreal : 1 + -(2 * (p : ℝ) ^ (-δ) * Real.cos (t * Real.log p)) + ((p : ℝ) ^ (-δ)) ^ 2
          = (1 - (p : ℝ) ^ (-δ) * Real.cos (t * Real.log p)) ^ 2
            + ((p : ℝ) ^ (-δ) * Real.sin (t * Real.log p)) ^ 2 := by
        linear_combination (-((p : ℝ) ^ (-δ)) ^ 2) * Real.cos_sq_add_sin_sq (t * Real.log p)
      exact_mod_cast hreal

/-- **The fake's coefficients are `1 ⋆ g`**: `a_n = Σ_{d ∣ n} g(d)` for `n ≥ 1`. -/
theorem fakeCoeff_eq_zeta_mul_gFun (X δ t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((fakeCoeff X δ t n : ℝ) : ℂ)
      = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * gFun X δ t) n := by
  rw [fakeCoeff_eq_ofLocal X δ t hn]
  have h1 := ofLocal_isMultiplicative (fakeLocC X δ t)
  have h2 : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * gFun X δ t).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul (ofLocal_isMultiplicative _)
  have hc0 : ∀ q, fakeLocC X δ t q 0 = 1 := fun q => by simp [fakeLocC]
  have heq := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ h1 _ h2).mpr
    (fun p i hp => by rw [ofLocal_prime_pow _ hc0 hp, zeta_mul_gFun_prime_pow X δ t hp])
  rw [heq]

/-! ### E2. `ζ` with the Euler factors below `X` removed, and its Euler product -/

/-- `ζ_{≥X}(w) = ζ(w) ∏_{p < X} (1 - p^{-w})`: the Riemann zeta function with its Euler factors at
the primes below `X` removed. -/
noncomputable def zetaTail (X : ℝ) (w : ℂ) : ℂ :=
  riemannZeta w * ∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-w))

/-- **The pole-shadow fake** `F(s) = ζ(s) / (ζ_{≥X}(s + δ - it) · ζ_{≥X}(s + δ + it))`. -/
noncomputable def poleShadow (X δ t : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s / (zetaTail X (s + ((δ : ℂ) - t * I)) * zetaTail X (s + ((δ : ℂ) + t * I)))

lemma norm_natCast_cpow_neg_lt_one {p : ℕ} (hp : 2 ≤ p) {w : ℂ} (hw : 0 < w.re) :
    ‖(p : ℂ) ^ (-w)‖ < 1 := by
  rw [norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

lemma one_sub_natCast_cpow_ne_zero {p : ℕ} (hp : 2 ≤ p) {w : ℂ} (hw : 0 < w.re) :
    1 - (p : ℂ) ^ (-w) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-w) = 1 := (sub_eq_zero.mp h).symm
  have := norm_natCast_cpow_neg_lt_one hp hw
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

lemma prod_primesBelow_ne_zero (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-w)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp =>
    one_sub_natCast_cpow_ne_zero (Nat.mem_primesBelow.mp hp).2.two_le hw

theorem zetaTail_ne_zero (X : ℝ) {w : ℂ} (hw : 1 ≤ w.re) : zetaTail X w ≠ 0 :=
  mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hw) (prod_primesBelow_ne_zero _ (by linarith))

/-- For `Re w > 1`, the Euler product of `1/ζ_{≥X}(w)`: a `HasProd` over `ℕ` of the function that is
`1` off the primes and at the primes `< X`, and `1 - p^{-w}` at the primes `≥ X`. -/
theorem hasProd_inv_zetaTail (X : ℝ) {w : ℂ} (hw : 1 < w.re) :
    HasProd ({p : ℕ | p.Prime}.mulIndicator
        fun p : ℕ => if (p : ℝ) < X then (1 : ℂ) else 1 - (p : ℂ) ^ (-w))
      (zetaTail X w)⁻¹ := by
  have h1 : HasProd ({p : ℕ | p.Prime}.mulIndicator fun p : ℕ => 1 - (p : ℂ) ^ (-w))
      (riemannZeta w)⁻¹ := by
    have h := (riemannZeta_eulerProduct_hasProd hw).inv₀ (riemannZeta_ne_zero_of_one_le_re hw.le)
    simp only [inv_inv] at h
    rw [← hasProd_subtype_iff_mulIndicator]
    exact h
  set S := Nat.primesBelow ⌈X⌉₊ with hS
  have h2 : HasProd (fun p : ℕ => if p ∈ S then (1 - (p : ℂ) ^ (-w))⁻¹ else 1)
      (∏ p ∈ S, (1 - (p : ℂ) ^ (-w))⁻¹) := by
    have := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional ℕ) (s := S)
      (f := fun p : ℕ => if p ∈ S then (1 - (p : ℂ) ^ (-w))⁻¹ else 1)
      (fun b hb => by simp [hb])
    convert this using 1
    exact Finset.prod_congr rfl fun p hp => by simp [hp]
  have h3 := h1.mul h2
  convert h3 using 1
  · funext p
    simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq]
    by_cases hp : p.Prime
    · have hmem : p ∈ S ↔ (p : ℝ) < X := by
        rw [hS, Nat.mem_primesBelow, Nat.lt_ceil]; simp [hp]
      by_cases hX : (p : ℝ) < X
      · have hne := one_sub_natCast_cpow_ne_zero hp.two_le (w := w) (by linarith)
        simp [hp, hX, hmem.mpr hX, hne]
      · simp [hp, hX, (not_congr hmem).mpr hX]
    · have : p ∉ S := fun h => hp (Nat.mem_primesBelow.mp h).2
      simp [hp, this]
  · unfold zetaTail
    rw [mul_inv, Finset.prod_inv_distrib]

/-! ### E3. The Dirichlet series of the fake equals the pole shadow on `Re s > 1` -/

lemma gLoc_zero (X δ t : ℝ) (p : ℕ) : gLoc X δ t p 0 = 1 := by simp [gLoc]

lemma norm_gLoc_le_one {X δ t : ℝ} (hX : 1 < X) (hδ : 0 < δ) (h2 : 2 ≤ X ^ δ) (p j : ℕ) :
    ‖gLoc X δ t p j‖ ≤ 1 := by
  unfold gLoc
  split_ifs with h0 hX' h1 h2'
  · simp
  · simp
  · have hXp : X ≤ (p : ℝ) := not_lt.mp hX'
    have hp0 : 0 < p := by exact_mod_cast (lt_of_lt_of_le (by linarith : (0 : ℝ) < X) hXp)
    have hpδ : 2 ≤ (p : ℝ) ^ δ := le_trans h2 (Real.rpow_le_rpow (by linarith) hXp hδ.le)
    have hpp : (0 : ℝ) < (p : ℝ) ^ δ := by positivity
    have hinv : (p : ℝ) ^ (-δ) ≤ 1 / 2 := by
      rw [Real.rpow_neg (by positivity), inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpδ
    have hnn : 0 ≤ (p : ℝ) ^ (-δ) := Real.rpow_nonneg (by positivity) _
    rw [norm_neg, alpha_add δ t hp0, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [Real.cos_le_one (t * Real.log p), Real.neg_one_le_cos (t * Real.log p)]
  · have hXp : X ≤ (p : ℝ) := not_lt.mp hX'
    have hp0 : 0 < p := by exact_mod_cast (lt_of_lt_of_le (by linarith : (0 : ℝ) < X) hXp)
    have hpδ : 2 ≤ (p : ℝ) ^ δ := le_trans h2 (Real.rpow_le_rpow (by linarith) hXp hδ.le)
    have hinv : (p : ℝ) ^ (-δ) ≤ 1 / 2 := by
      rw [Real.rpow_neg (by positivity), inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpδ
    have hnn : 0 ≤ (p : ℝ) ^ (-δ) := Real.rpow_nonneg (by positivity) _
    rw [alpha_mul δ t hp0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  · simp

theorem norm_gFun_le_one {X δ t : ℝ} (hX : 1 < X) (hδ : 0 < δ) (h2 : 2 ≤ X ^ δ) (n : ℕ) :
    ‖gFun X δ t n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [gFun, ofLocal_apply _ hn, Finsupp.prod, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun p _ => norm_gLoc_le_one hX hδ h2 p _)

theorem LSeriesSummable_gFun {X δ t : ℝ} (hX : 1 < X) (hδ : 0 < δ) (h2 : 2 ≤ X ^ δ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n => gFun X δ t n) s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hs
    ⟨1, fun n _ => by simpa using norm_gFun_le_one (t := t) hX hδ h2 n⟩

/-- The local Euler factor of `g` at a prime `p`. -/
theorem tsum_term_gFun_prime_pow (X δ t : ℝ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ∑' e, LSeries.term (fun n => gFun X δ t n) s (p ^ e)
      = (if (p : ℝ) < X then (1 : ℂ) else 1 - (p : ℂ) ^ (-(s + ((δ : ℂ) - t * I))))
        * (if (p : ℝ) < X then (1 : ℂ) else 1 - (p : ℂ) ^ (-(s + ((δ : ℂ) + t * I)))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hps : (p : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hp0)
  have hterm : ∀ e : ℕ, LSeries.term (fun n => gFun X δ t n) s (p ^ e)
      = gLoc X δ t p e / ((p : ℂ) ^ s) ^ e := by
    intro e
    rw [LSeries.term_of_ne_zero (pow_ne_zero e hp.ne_zero), gFun,
      ofLocal_prime_pow _ (gLoc_zero X δ t) hp, Nat.cast_pow, ← natCast_cpow_natCast_mul,
      cpow_nat_mul]
  rw [tsum_eq_sum (s := Finset.range 3)]
  swap
  · intro e he
    simp only [Finset.mem_range, not_lt] at he
    rw [hterm e]
    simp [gLoc, show e ≠ 0 by omega, show e ≠ 1 by omega, show e ≠ 2 by omega]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hterm, zero_add]
  by_cases hX : (p : ℝ) < X
  · simp [gLoc, hX]
  · simp only [gLoc, hX, ite_false, ite_true, one_ne_zero, show (2 : ℕ) ≠ 0 by norm_num,
      show (2 : ℕ) ≠ 1 by norm_num, pow_zero, pow_one, div_one]
    have e1 : (p : ℂ) ^ (-(s + ((δ : ℂ) - t * I))) = alphaP δ t p * ((p : ℂ) ^ s)⁻¹ := by
      rw [alphaP, ← cpow_neg, ← cpow_add _ _ hp0]; ring_nf
    have e2 : (p : ℂ) ^ (-(s + ((δ : ℂ) + t * I))) = alphaBarP δ t p * ((p : ℂ) ^ s)⁻¹ := by
      rw [alphaBarP, ← cpow_neg, ← cpow_add _ _ hp0]; ring_nf
    rw [e1, e2]
    field_simp
    ring

/-- `L(g, s) = 1/(ζ_{≥X}(s + δ - it) ζ_{≥X}(s + δ + it))` for `Re s > 1`. -/
theorem LSeries_gFun_eq {X δ t : ℝ} (hX : 1 < X) (hδ : 0 < δ) (h2 : 2 ≤ X ^ δ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => gFun X δ t n) s
      = (zetaTail X (s + ((δ : ℂ) - t * I)))⁻¹ * (zetaTail X (s + ((δ : ℂ) + t * I)))⁻¹ := by
  set f : ℕ → ℂ := LSeries.term (fun n => gFun X δ t n) s with hf
  have hmult := ofLocal_isMultiplicative (gLoc X δ t)
  have hf1 : f 1 = 1 := by
    rw [hf, LSeries.term_of_ne_zero one_ne_zero]
    simp [gFun, hmult.map_one]
  have hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [hf]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hf]
    rw [hf, LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
      LSeries.term_of_ne_zero hn, Nat.cast_mul, natCast_mul_natCast_cpow]
    simp only [gFun] at hmult ⊢
    rw [hmult.map_mul_of_coprime hmn]
    ring
  have hsum : Summable (fun n => ‖f n‖) := (LSeriesSummable_gFun hX hδ h2 hs).norm
  have hf0 : f 0 = 0 := by simp [hf]
  have hE := EulerProduct.eulerProduct_hasProd_mulIndicator hf1 hfmul hsum hf0
  have hA := hasProd_inv_zetaTail X (w := s + ((δ : ℂ) - t * I)) (by simp; linarith)
  have hB := hasProd_inv_zetaTail X (w := s + ((δ : ℂ) + t * I)) (by simp; linarith)
  have hAB := hA.mul hB
  have hloc : ({p : ℕ | p.Prime}.mulIndicator fun p => ∑' e, f (p ^ e))
      = ({p : ℕ | p.Prime}.mulIndicator
          fun p : ℕ => if (p : ℝ) < X then (1 : ℂ) else 1 - (p : ℂ) ^ (-(s + ((δ : ℂ) - t * I))))
        * ({p : ℕ | p.Prime}.mulIndicator
          fun p : ℕ => if (p : ℝ) < X then (1 : ℂ) else 1 - (p : ℂ) ^ (-(s + ((δ : ℂ) + t * I)))) := by
    funext p
    simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq, Pi.mul_apply]
    by_cases hp : p.Prime
    · simp only [hp, ite_true]
      exact tsum_term_gFun_prime_pow X δ t hp s
    · simp [hp]
  rw [hloc] at hE
  exact hE.unique hAB

/-- **Identification.** For `Re s > 1` the Dirichlet series of the fake's coefficients equals the
pole shadow `ζ(s) / (ζ_{≥X}(s + δ - it) ζ_{≥X}(s + δ + it))`. -/
theorem LSeries_fakeCoeff_eq_poleShadow {X δ t : ℝ} (hX : 1 < X) (hδ : 0 < δ) (h2 : 2 ≤ X ^ δ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((fakeCoeff X δ t n : ℝ) : ℂ)) s = poleShadow X δ t s := by
  have hcongr : LSeries (fun n => ((fakeCoeff X δ t n : ℝ) : ℂ)) s
      = LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * gFun X δ t) n) s :=
    LSeries_congr (fun {n} hn => fakeCoeff_eq_zeta_mul_gFun X δ t hn) s
  have hzfun : (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)
      = fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ) := by
    funext n; simp [ArithmeticFunction.natCoe_apply]
  have hz : LSeriesSummable (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s := by
    rw [hzfun]; exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  rw [hcongr, ArithmeticFunction.LSeries_mul' hz (LSeriesSummable_gFun hX hδ h2 hs),
    LSeries_gFun_eq hX hδ h2 hs, hzfun, ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    poleShadow, div_eq_mul_inv, mul_inv]


/-! ### E4. The analytic zero, the pole, and holomorphy of the pole shadow -/

lemma differentiableAt_prod_primesBelow (N : ℕ) (w : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-w))) w := by
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.ne_zero
  exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl hp0))

theorem differentiableAt_zetaTail (X : ℝ) {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ (zetaTail X) w :=
  (differentiableAt_riemannZeta hw).mul (differentiableAt_prod_primesBelow _ w)

/-- The residue of `ζ_{≥X}` at `w = 1` is `∏_{p < X} (1 - 1/p)`. -/
theorem zetaTail_residue (X : ℝ) :
    Tendsto (fun w => (w - 1) * zetaTail X w) (𝓝[≠] 1)
      (𝓝 (∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))) := by
  have hc : Tendsto (fun w : ℂ => ∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-w))) (𝓝[≠] 1)
      (𝓝 (∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))) :=
    (differentiableAt_prod_primesBelow _ 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := riemannZeta_residue_one.mul hc
  rw [one_mul] at h
  refine h.congr (fun w => ?_)
  unfold zetaTail; ring

lemma residue_ne_zero (X : ℝ) : ∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))) ≠ 0 :=
  prod_primesBelow_ne_zero _ (by simp)

/-- The shift `s ↦ s + c` maps the punctured neighbourhood of `1 - c` to that of `1`. -/
lemma tendsto_shift (c : ℂ) : Tendsto (fun s => s + c) (𝓝[≠] (1 - c)) (𝓝[≠] 1) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h : Tendsto (fun s => s + c) (𝓝 (1 - c)) (𝓝 ((1 - c) + c)) :=
      (continuous_id.add continuous_const).tendsto _
    rw [sub_add_cancel] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    intro h
    apply hs
    have h' : s + c = 1 := h
    show s = 1 - c
    linear_combination h'

/-- Near the zero: `(s - s₀)⁻¹ · (ζ_{≥X}(s + c))⁻¹ → (∏_{p<X}(1 - 1/p))⁻¹` where `s₀ = 1 - c`. -/
lemma tendsto_div_zetaTail_shift (X : ℝ) (c : ℂ) :
    Tendsto (fun s => ((s - (1 - c)) * zetaTail X (s + c))⁻¹) (𝓝[≠] (1 - c))
      (𝓝 (∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹) := by
  have h := ((zetaTail_residue X).comp (tendsto_shift c)).inv₀ (residue_ne_zero X)
  refine h.congr (fun s => ?_)
  simp only [Function.comp]
  congr 1
  ring

/-- `1/ζ_{≥X}(s + c) → 0` as `s → 1 - c`. -/
lemma tendsto_inv_zetaTail_shift (X : ℝ) (c : ℂ) :
    Tendsto (fun s => (zetaTail X (s + c))⁻¹) (𝓝[≠] (1 - c)) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℂ => s - (1 - c)) (𝓝[≠] (1 - c)) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - (1 - c)) (𝓝 (1 - c)) (𝓝 ((1 - c) - (1 - c))) :=
      (continuous_id.sub continuous_const).tendsto _
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := h1.mul (tendsto_div_zetaTail_shift X c)
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - (1 - c) ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs', one_mul]

/-- `ζ_{≥X}(s + c) ≠ 0` for `s` in a punctured neighbourhood of `1 - c`. -/
lemma eventually_zetaTail_shift_ne_zero (X : ℝ) (c : ℂ) :
    ∀ᶠ s in 𝓝[≠] (1 - c), zetaTail X (s + c) ≠ 0 := by
  have h := ((zetaTail_residue X).comp (tendsto_shift c)).eventually_ne (residue_ne_zero X)
  filter_upwards [h] with s hs
  intro h0
  apply hs
  simp only [Function.comp, h0, mul_zero]

section Zero

variable (X δ t : ℝ)

/-- The location of the fake zero, `s₀ = 1 - δ + i t`. -/
noncomputable abbrev s₀ : ℂ := 1 - ((δ : ℂ) - t * I)

lemma s₀_re : (s₀ δ t).re = 1 - δ := by simp [s₀]
lemma s₀_im : (s₀ δ t).im = t := by simp [s₀]

lemma s₀_ne_one {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : s₀ δ t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [s₀_re] at this
  simp at this
  linarith

lemma s₀_add_c₂ : s₀ δ t + ((δ : ℂ) + t * I) = 1 + 2 * t * I := by simp [s₀]; ring

lemma one_add_two_t_ne_one {t : ℝ} (ht : t ≠ 0) : (1 : ℂ) + 2 * t * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact ht this

lemma one_add_two_t_re (t : ℝ) : ((1 : ℂ) + 2 * t * I).re = 1 := by simp

/-- **The fake zero.** For `δ > 0` and `t ≠ 0` the pole shadow tends to `0` at `s₀ = 1 - δ + i t`. -/
theorem poleShadow_tendsto_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≠ 0) :
    Tendsto (poleShadow X δ t) (𝓝[≠] (s₀ δ t)) (𝓝 0) := by
  have hζ : Tendsto riemannZeta (𝓝[≠] (s₀ δ t)) (𝓝 (riemannZeta (s₀ δ t))) :=
    (differentiableAt_riemannZeta (s₀_ne_one hδ t)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hA := tendsto_inv_zetaTail_shift X ((δ : ℂ) - t * I)
  have hB : Tendsto (fun s => (zetaTail X (s + ((δ : ℂ) + t * I)))⁻¹) (𝓝[≠] (s₀ δ t))
      (𝓝 (zetaTail X (1 + 2 * t * I))⁻¹) := by
    have hc : ContinuousAt (fun s => zetaTail X (s + ((δ : ℂ) + t * I))) (s₀ δ t) := by
      have hd := (differentiableAt_zetaTail X (w := s₀ δ t + ((δ : ℂ) + t * I))
        (by rw [s₀_add_c₂]; exact one_add_two_t_ne_one ht)).continuousAt
      exact ContinuousAt.comp (x := s₀ δ t) (f := fun s : ℂ => s + ((δ : ℂ) + t * I)) hd
        (continuous_id.add continuous_const).continuousAt
    have hv : zetaTail X (s₀ δ t + ((δ : ℂ) + t * I)) = zetaTail X (1 + 2 * t * I) := by
      rw [s₀_add_c₂]
    have hne : zetaTail X (1 + 2 * t * I) ≠ 0 :=
      zetaTail_ne_zero X (by rw [one_add_two_t_re])
    have hB0 : Tendsto (fun s => (zetaTail X (s + ((δ : ℂ) + t * I)))⁻¹) (𝓝[≠] (s₀ δ t))
        (𝓝 (zetaTail X (s₀ δ t + ((δ : ℂ) + t * I)))⁻¹) :=
      (hc.tendsto.inv₀ (by rw [hv]; exact hne)).mono_left nhdsWithin_le_nhds
    rwa [hv] at hB0
  have h := (hζ.mul hA).mul hB
  rw [mul_zero, zero_mul] at h
  refine h.congr (fun s => ?_)
  simp only [poleShadow, div_eq_mul_inv, mul_inv]
  ring

/-- **Order of the fake zero.** `F(s)/(s - s₀) → ζ(s₀) · (∏_{p<X}(1 - 1/p))⁻¹ · ζ_{≥X}(1 + 2it)⁻¹`;
the limit is nonzero iff `ζ(s₀) ≠ 0`, i.e. the zero is simple unless `ζ` itself vanishes there. -/
theorem poleShadow_div_tendsto {δ t : ℝ} (hδ : 0 < δ) (ht : t ≠ 0) :
    Tendsto (fun s => poleShadow X δ t s / (s - s₀ δ t)) (𝓝[≠] (s₀ δ t))
      (𝓝 (riemannZeta (s₀ δ t) * (∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹
        * (zetaTail X (1 + 2 * t * I))⁻¹)) := by
  have hζ : Tendsto riemannZeta (𝓝[≠] (s₀ δ t)) (𝓝 (riemannZeta (s₀ δ t))) :=
    (differentiableAt_riemannZeta (s₀_ne_one hδ t)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hA := tendsto_div_zetaTail_shift X ((δ : ℂ) - t * I)
  have hB : Tendsto (fun s => (zetaTail X (s + ((δ : ℂ) + t * I)))⁻¹) (𝓝[≠] (s₀ δ t))
      (𝓝 (zetaTail X (1 + 2 * t * I))⁻¹) := by
    have hc : ContinuousAt (fun s => zetaTail X (s + ((δ : ℂ) + t * I))) (s₀ δ t) := by
      have hd := (differentiableAt_zetaTail X (w := s₀ δ t + ((δ : ℂ) + t * I))
        (by rw [s₀_add_c₂]; exact one_add_two_t_ne_one ht)).continuousAt
      exact ContinuousAt.comp (x := s₀ δ t) (f := fun s : ℂ => s + ((δ : ℂ) + t * I)) hd
        (continuous_id.add continuous_const).continuousAt
    have hv : zetaTail X (s₀ δ t + ((δ : ℂ) + t * I)) = zetaTail X (1 + 2 * t * I) := by
      rw [s₀_add_c₂]
    have hne : zetaTail X (1 + 2 * t * I) ≠ 0 :=
      zetaTail_ne_zero X (by rw [one_add_two_t_re])
    have hB0 : Tendsto (fun s => (zetaTail X (s + ((δ : ℂ) + t * I)))⁻¹) (𝓝[≠] (s₀ δ t))
        (𝓝 (zetaTail X (s₀ δ t + ((δ : ℂ) + t * I)))⁻¹) :=
      (hc.tendsto.inv₀ (by rw [hv]; exact hne)).mono_left nhdsWithin_le_nhds
    rwa [hv] at hB0
  have h := (hζ.mul hA).mul hB
  refine h.congr (fun s => ?_)
  simp only [poleShadow, div_eq_mul_inv, mul_inv]
  ring

/-- The pole shadow is holomorphic in a punctured neighbourhood of `s₀`. -/
theorem poleShadow_eventually_differentiableAt {δ t : ℝ} (hδ : 0 < δ) (ht : t ≠ 0) :
    ∀ᶠ s in 𝓝[≠] (s₀ δ t), DifferentiableAt ℂ (poleShadow X δ t) s := by
  have h1 : ∀ᶠ s in 𝓝[≠] (s₀ δ t), s ≠ 1 :=
    (eventually_ne_nhds (s₀_ne_one hδ t)).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ s in 𝓝[≠] (s₀ δ t), s + ((δ : ℂ) - t * I) ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    intro h
    apply hs
    show s = 1 - ((δ : ℂ) - t * I)
    linear_combination h
  have h3 := eventually_zetaTail_shift_ne_zero X ((δ : ℂ) - t * I)
  have hw₂ : s₀ δ t + ((δ : ℂ) + t * I) ≠ 1 := by rw [s₀_add_c₂]; exact one_add_two_t_ne_one ht
  have h4 : ∀ᶠ s in 𝓝[≠] (s₀ δ t), s + ((δ : ℂ) + t * I) ≠ 1 := by
    have hc : ContinuousAt (fun s : ℂ => s + ((δ : ℂ) + t * I)) (s₀ δ t) :=
      (continuous_id.add continuous_const).continuousAt
    exact (hc.eventually_ne hw₂).filter_mono nhdsWithin_le_nhds
  have h5 : ∀ᶠ s in 𝓝[≠] (s₀ δ t), zetaTail X (s + ((δ : ℂ) + t * I)) ≠ 0 := by
    have hc : ContinuousAt (fun s => zetaTail X (s + ((δ : ℂ) + t * I))) (s₀ δ t) := by
      have hd := (differentiableAt_zetaTail X hw₂).continuousAt
      exact ContinuousAt.comp (x := s₀ δ t) (f := fun s : ℂ => s + ((δ : ℂ) + t * I)) hd
        (continuous_id.add continuous_const).continuousAt
    have hne : zetaTail X (s₀ δ t + ((δ : ℂ) + t * I)) ≠ 0 := by
      rw [s₀_add_c₂]; exact zetaTail_ne_zero X (by rw [one_add_two_t_re])
    exact (hc.eventually_ne hne).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2, h3, h4, h5] with s hs1 hs2 hs3 hs4 hs5
  have dA : DifferentiableAt ℂ (fun s => zetaTail X (s + ((δ : ℂ) - t * I))) s :=
    (differentiableAt_zetaTail X hs2).comp s (differentiableAt_id.add_const _)
  have dB : DifferentiableAt ℂ (fun s => zetaTail X (s + ((δ : ℂ) + t * I))) s :=
    (differentiableAt_zetaTail X hs4).comp s (differentiableAt_id.add_const _)
  exact (differentiableAt_riemannZeta hs1).div (dA.mul dB) (mul_ne_zero hs3 hs5)

/-- The pole shadow is holomorphic on `{Re s > 1 - δ} \ {1}`. -/
theorem poleShadow_differentiableAt_of_re {δ : ℝ} {s : ℂ} (hs : 1 - δ < s.re)
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (poleShadow X δ t) s := by
  have hre1 : 1 < (s + ((δ : ℂ) - t * I)).re := by simp; linarith
  have hre2 : 1 < (s + ((δ : ℂ) + t * I)).re := by simp; linarith
  have hne1 : s + ((δ : ℂ) - t * I) ≠ 1 := fun h => by rw [h] at hre1; simp at hre1
  have hne2 : s + ((δ : ℂ) + t * I) ≠ 1 := fun h => by rw [h] at hre2; simp at hre2
  have dA : DifferentiableAt ℂ (fun s => zetaTail X (s + ((δ : ℂ) - t * I))) s :=
    (differentiableAt_zetaTail X hne1).comp s (differentiableAt_id.add_const _)
  have dB : DifferentiableAt ℂ (fun s => zetaTail X (s + ((δ : ℂ) + t * I))) s :=
    (differentiableAt_zetaTail X hne2).comp s (differentiableAt_id.add_const _)
  exact (differentiableAt_riemannZeta hs1).div (dA.mul dB)
    (mul_ne_zero (zetaTail_ne_zero X hre1.le) (zetaTail_ne_zero X hre2.le))

/-- In `Re s > 1 - δ` the zeros of the pole shadow are exactly those of `ζ`. -/
theorem poleShadow_eq_zero_iff {δ : ℝ} {s : ℂ} (hs : 1 - δ < s.re) :
    poleShadow X δ t s = 0 ↔ riemannZeta s = 0 := by
  have hre1 : 1 ≤ (s + ((δ : ℂ) - t * I)).re := by simp; linarith
  have hre2 : 1 ≤ (s + ((δ : ℂ) + t * I)).re := by simp; linarith
  rw [poleShadow, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (mul_ne_zero (zetaTail_ne_zero X hre1) (zetaTail_ne_zero X hre2))
  · exact Or.inl

/-- **The pole at `s = 1`** has residue `(ζ_{≥X}(1 + δ - it) ζ_{≥X}(1 + δ + it))⁻¹ ≠ 0`. -/
theorem poleShadow_residue {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun s => (s - 1) * poleShadow X δ t s) (𝓝[≠] 1)
      (𝓝 ((zetaTail X (1 + ((δ : ℂ) - t * I)) * zetaTail X (1 + ((δ : ℂ) + t * I)))⁻¹)) := by
  have hre1 : 1 < (1 + ((δ : ℂ) - t * I)).re := by simp; linarith
  have hre2 : 1 < (1 + ((δ : ℂ) + t * I)).re := by simp; linarith
  have hne1 : (1 : ℂ) + ((δ : ℂ) - t * I) ≠ 1 := fun h => by rw [h] at hre1; simp at hre1
  have hne2 : (1 : ℂ) + ((δ : ℂ) + t * I) ≠ 1 := fun h => by rw [h] at hre2; simp at hre2
  have hc : ContinuousAt (fun s => zetaTail X (s + ((δ : ℂ) - t * I))
      * zetaTail X (s + ((δ : ℂ) + t * I))) 1 := by
    have dA := ((differentiableAt_zetaTail X hne1).continuousAt).comp
      (f := fun s : ℂ => s + ((δ : ℂ) - t * I)) (continuous_id.add continuous_const).continuousAt
    have dB := ((differentiableAt_zetaTail X hne2).continuousAt).comp
      (f := fun s : ℂ => s + ((δ : ℂ) + t * I)) (continuous_id.add continuous_const).continuousAt
    exact dA.mul dB
  have hden : Tendsto (fun s => (zetaTail X (s + ((δ : ℂ) - t * I))
      * zetaTail X (s + ((δ : ℂ) + t * I)))⁻¹) (𝓝[≠] (1 : ℂ))
      (𝓝 ((zetaTail X (1 + ((δ : ℂ) - t * I)) * zetaTail X (1 + ((δ : ℂ) + t * I)))⁻¹)) :=
    (hc.tendsto.inv₀ (mul_ne_zero (zetaTail_ne_zero X hre1.le)
      (zetaTail_ne_zero X hre2.le))).mono_left nhdsWithin_le_nhds
  have h := riemannZeta_residue_one.mul hden
  rw [one_mul] at h
  refine h.congr (fun s => ?_)
  simp only [poleShadow, div_eq_mul_inv]
  ring

lemma poleShadow_residue_ne_zero {δ : ℝ} (hδ : 0 < δ) :
    (zetaTail X (1 + ((δ : ℂ) - t * I)) * zetaTail X (1 + ((δ : ℂ) + t * I)))⁻¹ ≠ 0 := by
  have hre1 : 1 ≤ (1 + ((δ : ℂ) - t * I)).re := by simp; linarith
  have hre2 : 1 ≤ (1 + ((δ : ℂ) + t * I)).re := by simp; linarith
  exact inv_ne_zero (mul_ne_zero (zetaTail_ne_zero X hre1) (zetaTail_ne_zero X hre2))


/-! ### E5. Exact order of the zero, the real double zero, and the packaged statements -/

/-- For `ζ(s₀) ≠ 0` the zero of the pole shadow at `s₀` is simple (nonzero limit of `F/(s - s₀)`). -/
theorem poleShadow_simple_zero {δ t : ℝ} (hζ : riemannZeta (s₀ δ t) ≠ 0) :
    riemannZeta (s₀ δ t) * (∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹
      * (zetaTail X (1 + 2 * t * I))⁻¹ ≠ 0 :=
  mul_ne_zero (mul_ne_zero hζ (inv_ne_zero (residue_ne_zero X)))
    (inv_ne_zero (zetaTail_ne_zero X (by rw [one_add_two_t_re])))

/-- **`t = 0`: a double real zero at `1 - δ`** (for `0 < δ < 1`), with the exact nonzero limit of
`F(s)/(s - (1 - δ))^2`; the nonvanishing of `ζ(1 - δ)` is `LowHeightBox`'s real-axis corollary. -/
theorem poleShadow_real_double_zero {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun s => poleShadow X δ 0 s / (s - s₀ δ 0) ^ 2) (𝓝[≠] (s₀ δ 0))
      (𝓝 (riemannZeta (s₀ δ 0)
        * ((∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹) ^ 2))
    ∧ riemannZeta (s₀ δ 0) * ((∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹) ^ 2
      ≠ 0 := by
  have hc : ((δ : ℂ) + ((0 : ℝ) : ℂ) * I) = ((δ : ℂ) - ((0 : ℝ) : ℂ) * I) := by simp
  have hs₀ : s₀ δ 0 = ((1 - δ : ℝ) : ℂ) := by simp [s₀]
  constructor
  · have hζ : Tendsto riemannZeta (𝓝[≠] (s₀ δ 0)) (𝓝 (riemannZeta (s₀ δ 0))) :=
      (differentiableAt_riemannZeta (s₀_ne_one hδ 0)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hA := tendsto_div_zetaTail_shift X ((δ : ℂ) - ((0 : ℝ) : ℂ) * I)
    have h := hζ.mul (hA.mul hA)
    have hval : riemannZeta (s₀ δ 0)
        * ((∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹
          * (∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹)
        = riemannZeta (s₀ δ 0) * ((∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-(1 : ℂ))))⁻¹) ^ 2 := by
      ring
    rw [hval] at h
    refine h.congr (fun s => ?_)
    simp only [poleShadow, hc, s₀, div_eq_mul_inv, mul_inv, ← inv_pow]
    ring
  · refine mul_ne_zero ?_ (pow_ne_zero 2 (inv_ne_zero (residue_ne_zero X)))
    rw [hs₀]
    exact LowHeightBox.riemannZeta_ne_zero_of_unit_interval (1 - δ) (by linarith) (by linarith)

end Zero

/-- The fake's coefficients are multiplicative (they come from an Euler product). -/
theorem fakeCoeff_mul_of_coprime (X δ t : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    fakeCoeff X δ t (m * n) = fakeCoeff X δ t m * fakeCoeff X δ t n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have : n = 1 := (Nat.coprime_zero_left n).mp hmn
    subst this; simp [fakeCoeff]
  rcases eq_or_ne n 0 with rfl | hn
  · have : m = 1 := (Nat.coprime_zero_right m).mp hmn
    subst this; simp [fakeCoeff]
  have h := (ofLocal_isMultiplicative (fakeLocC X δ t)).map_mul_of_coprime hmn
  rw [← fakeCoeff_eq_ofLocal X δ t (mul_ne_zero hm hn), ← fakeCoeff_eq_ofLocal X δ t hm,
    ← fakeCoeff_eq_ofLocal X δ t hn] at h
  exact_mod_cast h

/-- **Placement inside the Mossinghoff–Trudgian–Yang region.** With `X = T^A` and
`δ = log 2 / log X` one has `X^δ = 2`, and for `A ≥ 3.86` the abscissa `1 - δ` exceeds
`1 - 1/(5.558691 log T)`. -/
theorem mty_placement {T A : ℝ} (hT : 2 ≤ T) (hA : 386 / 100 ≤ A) :
    1 < T ^ A ∧ 0 < Real.log 2 / Real.log (T ^ A)
      ∧ (T ^ A) ^ (Real.log 2 / Real.log (T ^ A)) = 2
      ∧ 1 - 1 / (5558691 / 1000000 * Real.log T) < 1 - Real.log 2 / Real.log (T ^ A) := by
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hA0 : 0 < A := by linarith
  have hlogX : Real.log (T ^ A) = A * Real.log T := Real.log_rpow hT0 A
  have hX1 : 1 < T ^ A := Real.one_lt_rpow (by linarith) hA0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨hX1, ?_, ?_, ?_⟩
  · rw [hlogX]; positivity
  · rw [Real.rpow_def_of_pos (by linarith), hlogX]
    have : A * Real.log T * (Real.log 2 / (A * Real.log T)) = Real.log 2 := by
      field_simp
    rw [this, Real.exp_log (by norm_num)]
  · rw [hlogX, sub_lt_sub_iff_left, div_lt_div_iff₀ (by positivity) (by positivity)]
    have h2 := Real.log_two_lt_d9
    have hkey : 5558691 / 1000000 * Real.log 2 < A := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr hkey) hlogT]

/-- Choosing the cut `X' = max X 2^{1/δ}` makes the local weights nonnegative. -/
lemma two_le_max_rpow {X δ : ℝ} (hδ : 0 < δ) : 2 ≤ (max X ((2 : ℝ) ^ (1 / δ))) ^ δ := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / δ) := by positivity
  calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
        rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
    _ ≤ (max X ((2 : ℝ) ^ (1 / δ))) ^ δ :=
        Real.rpow_le_rpow h0 (le_max_right _ _) hδ.le

/-- **Headline (statements 3-4): finite coefficient data + P2 + an Euler product give no zero-free
region at all.** For every `X > 1`, `δ > 0`, `t ≠ 0` there is `X' ≥ X` such that the pole-shadow fake
`F = poleShadow X' δ t` has: nonnegative multiplicative (Euler-product) coefficients equal to `1`
for every `n < X`; nonnegative local von Mangoldt brackets `1 - 2 p^{-kδ} cos(k t log p)` (P2);
Dirichlet series equal to `F` on `Re s > 1`; `F` holomorphic on `{Re s > 1 - δ} \ {1}` with the
same zeros as `ζ` there, and on a punctured neighbourhood of `s₀ = 1 - δ + i t`; and `F(s) → 0`
as `s → s₀`. -/
theorem finite_data_no_zero_free_region (X δ t : ℝ) (hX : 1 < X) (hδ : 0 < δ) (ht : t ≠ 0) :
    ∃ X' : ℝ, X ≤ X' ∧ 1 < X' ∧ 2 ≤ X' ^ δ ∧
      (∀ n, 0 ≤ fakeCoeff X' δ t n) ∧
      (∀ n : ℕ, (n : ℝ) < X → fakeCoeff X' δ t n = 1) ∧
      (∀ {m n : ℕ}, m.Coprime n →
        fakeCoeff X' δ t (m * n) = fakeCoeff X' δ t m * fakeCoeff X' δ t n) ∧
      (∀ p k : ℕ, X' ≤ (p : ℝ) → 1 ≤ k →
        0 ≤ 1 - 2 * (p : ℝ) ^ (-((k : ℝ) * δ)) * Real.cos (k * t * Real.log p)) ∧
      (∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((fakeCoeff X' δ t n : ℝ) : ℂ)) s = poleShadow X' δ t s) ∧
      (∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → DifferentiableAt ℂ (poleShadow X' δ t) s) ∧
      (∀ s : ℂ, 1 - δ < s.re → (poleShadow X' δ t s = 0 ↔ riemannZeta s = 0)) ∧
      (∀ᶠ s in 𝓝[≠] (s₀ δ t), DifferentiableAt ℂ (poleShadow X' δ t) s) ∧
      Tendsto (poleShadow X' δ t) (𝓝[≠] (s₀ δ t)) (𝓝 0) := by
  set X' := max X ((2 : ℝ) ^ (1 / δ)) with hX'
  have hXX' : X ≤ X' := le_max_left _ _
  have hX'1 : 1 < X' := lt_of_lt_of_le hX hXX'
  have h2 : 2 ≤ X' ^ δ := two_le_max_rpow hδ
  refine ⟨X', hXX', hX'1, h2, fakeCoeff_nonneg X' δ t hX'1 hδ h2, ?_,
    fun hmn => fakeCoeff_mul_of_coprime X' δ t hmn, ?_,
    fun s hs => LSeries_fakeCoeff_eq_poleShadow hX'1 hδ h2 hs,
    fun s hs hs1 => poleShadow_differentiableAt_of_re X' t hs hs1,
    fun s hs => poleShadow_eq_zero_iff X' t hs,
    poleShadow_eventually_differentiableAt X' hδ ht,
    poleShadow_tendsto_zero X' hδ ht⟩
  · intro n hn
    exact fakeCoeff_eq_one_of_lt X' δ t n (lt_of_lt_of_le hn hXX')
  · intro p k hp hk
    have hp1 : 1 < (p : ℝ) := lt_of_lt_of_le hX'1 hp
    have hpδ : 2 ≤ (p : ℝ) ^ δ := le_trans h2 (Real.rpow_le_rpow (by linarith) hp hδ.le)
    exact fake_vonMangoldt_bracket_nonneg (p : ℝ) δ (k * t * Real.log p) k hp1 hδ hpδ hk

/-- **The MTY instance.** For `T ≥ 2` and `A ≥ 3.86`, agreement with ζ's coefficients for all
`n < T^A` (plus `a_n ≥ 0`, Euler product, P2) is compatible with a zero at height `T` whose abscissa
lies inside the Mossinghoff–Trudgian–Yang zero-free region `σ ≥ 1 - 1/(5.558691 log T)` of ζ. -/
theorem mty_fake {T A : ℝ} (hT : 2 ≤ T) (hA : 386 / 100 ≤ A) :
    ∃ X δ : ℝ, X = T ^ A ∧ 0 < δ ∧ 1 < X ∧ 2 ≤ X ^ δ ∧
      (∀ n, 0 ≤ fakeCoeff X δ T n) ∧
      (∀ n : ℕ, (n : ℝ) < T ^ A → fakeCoeff X δ T n = 1) ∧
      (∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((fakeCoeff X δ T n : ℝ) : ℂ)) s = poleShadow X δ T s) ∧
      Tendsto (poleShadow X δ T) (𝓝[≠] (s₀ δ T)) (𝓝 0) ∧
      (s₀ δ T).im = T ∧ 1 - 1 / (5558691 / 1000000 * Real.log T) < (s₀ δ T).re := by
  obtain ⟨hX1, hδ, hXδ, hreg⟩ := mty_placement hT hA
  have hT0 : T ≠ 0 := by intro h; rw [h] at hT; norm_num at hT
  refine ⟨T ^ A, Real.log 2 / Real.log (T ^ A), rfl, hδ, hX1, hXδ.ge,
    fakeCoeff_nonneg _ _ T hX1 hδ hXδ.ge, fun n hn => fakeCoeff_eq_one_of_lt _ _ T n hn,
    fun s hs => LSeries_fakeCoeff_eq_poleShadow hX1 hδ hXδ.ge hs,
    poleShadow_tendsto_zero _ hδ hT0, s₀_im _ _, ?_⟩
  rw [s₀_re]
  exact hreg



/-! ### E6. Expulsion: left of its zero the real fake is exponentially large -/

/-- Two-sided bounds for `ζ` on the real segment `(0,1)` from the strip representation
`ζ(σ) = σ/(σ-1) - σ J(σ)` and the sharp bound `|J(σ)| ≤ 1/(2σ)`. -/
theorem norm_riemannZeta_real_bounds {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    σ / (1 - σ) - 1 / 2 ≤ ‖riemannZeta (σ : ℂ)‖ ∧ ‖riemannZeta (σ : ℂ)‖ ≤ σ / (1 - σ) + 1 / 2 := by
  have hdom : (σ : ℂ) ∈ ZeroFreeBridge.stripDomain := by
    refine ⟨by simpa using h0, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [ZeroFreeBridge.zeta_fract_repr hdom, ZeroFreeBridge.stripRHS]
  have hJ := LowHeightBox.norm_fractIntegral_le_half (s := (σ : ℂ)) (by simpa using h0)
  simp only [Complex.ofReal_re] at hJ
  have hA : ‖(σ : ℂ) / ((σ : ℂ) - 1)‖ = σ / (1 - σ) := by
    rw [show (σ : ℂ) / ((σ : ℂ) - 1) = ((σ / (σ - 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (div_neg_of_pos_of_neg h0 (by linarith))]
    rw [show (1 - σ) = -(σ - 1) by ring, div_neg]
  have hB : ‖(σ : ℂ) * ZeroFreeBridge.fractIntegral σ‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    calc σ * ‖ZeroFreeBridge.fractIntegral (σ : ℂ)‖ ≤ σ * (1 / (2 * σ)) :=
          mul_le_mul_of_nonneg_left hJ h0.le
      _ = 1 / 2 := by field_simp
  constructor
  · have := norm_sub_norm_le ((σ : ℂ) / ((σ : ℂ) - 1)) ((σ : ℂ) * ZeroFreeBridge.fractIntegral σ)
    linarith
  · have := norm_sub_le ((σ : ℂ) / ((σ : ℂ) - 1)) ((σ : ℂ) * ZeroFreeBridge.fractIntegral σ)
    linarith

/-- On the real axis, the removed Euler factors are exponentially small:
`∏_{p<X} (1 - p^{-σ}) ≤ exp(-Σ_{p<X} p^{-σ})`. -/
theorem norm_prod_primesBelow_real_le (N : ℕ) {σ : ℝ} (h0 : 0 < σ) :
    ‖∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-(σ : ℂ)))‖
      ≤ Real.exp (-∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (-σ)) := by
  rw [norm_prod, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro p hp
  have hp2 := (Nat.mem_primesBelow.mp hp).2.two_le
  have hpos : (0 : ℝ) < p := by positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hc : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpos.le]
    push_cast
    rfl
  have hx : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hx0 : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hpos.le _
  rw [hc, show (1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ) = ((1 - (p : ℝ) ^ (-σ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith [Real.add_one_le_exp (-(p : ℝ) ^ (-σ))]

/-- **The real fake is exponentially large left of its double zero.** For `1/2 ≤ σ` and
`σ + η < 1`, with `σ' = σ + η`,
`|F_{X,0,η}(σ)| ≥ (σ/(1-σ) - 1/2) · exp(2 Σ_{p<X} p^{-σ'}) / (σ'/(1-σ') + 1/2)^2`. -/
theorem poleShadow_real_exp_large (X : ℝ) {η σ : ℝ} (hη : 0 < η) (hσ : 1 / 2 ≤ σ)
    (hσ1 : σ + η < 1) :
    (σ / (1 - σ) - 1 / 2) * Real.exp (2 * ∑ p ∈ Nat.primesBelow ⌈X⌉₊, (p : ℝ) ^ (-(σ + η)))
        / ((σ + η) / (1 - (σ + η)) + 1 / 2) ^ 2
      ≤ ‖poleShadow X η 0 (σ : ℂ)‖ := by
  set σ' := σ + η with hσ'
  set S := ∑ p ∈ Nat.primesBelow ⌈X⌉₊, (p : ℝ) ^ (-σ') with hS
  have hσ0 : 0 < σ := by linarith
  have hσ1' : σ < 1 := by linarith
  have hσ'0 : 0 < σ' := by linarith
  have hshift : (σ : ℂ) + ((η : ℂ) - ((0 : ℝ) : ℂ) * I) = ((σ' : ℝ) : ℂ) := by
    rw [hσ']; push_cast; ring
  have hshift' : (σ : ℂ) + ((η : ℂ) + ((0 : ℝ) : ℂ) * I) = ((σ' : ℝ) : ℂ) := by
    rw [hσ']; push_cast; ring
  have hF : poleShadow X η 0 (σ : ℂ) = riemannZeta σ / (zetaTail X σ' * zetaTail X σ') := by
    rw [poleShadow, hshift, hshift']
  have hζσ := (norm_riemannZeta_real_bounds hσ0 hσ1').1
  have hζσ' := (norm_riemannZeta_real_bounds hσ'0 hσ1).2
  have hprod := norm_prod_primesBelow_real_le ⌈X⌉₊ hσ'0
  have hζne : riemannZeta ((σ' : ℝ) : ℂ) ≠ 0 :=
    LowHeightBox.riemannZeta_ne_zero_of_unit_interval σ' hσ'0 hσ1
  have hPne : ∏ p ∈ Nat.primesBelow ⌈X⌉₊, (1 - (p : ℂ) ^ (-((σ' : ℝ) : ℂ))) ≠ 0 :=
    prod_primesBelow_ne_zero _ (by simpa using hσ'0)
  have hTne : zetaTail X σ' ≠ 0 := mul_ne_zero hζne hPne
  have hTpos : 0 < ‖zetaTail X σ'‖ := norm_pos_iff.mpr hTne
  have hT : ‖zetaTail X σ'‖ ≤ (σ' / (1 - σ') + 1 / 2) * Real.exp (-S) := by
    rw [zetaTail, norm_mul]
    exact mul_le_mul hζσ' hprod (norm_nonneg _) (by positivity)
  have hnum : 1 / 2 ≤ σ / (1 - σ) - 1 / 2 := by
    rw [le_sub_iff_add_le, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, le_div_iff₀ (by linarith)]
    linarith
  rw [hF, norm_div, norm_mul, ← sq]
  have hB0 : 0 < (σ' / (1 - σ') + 1 / 2) := by
    have : 0 < σ' / (1 - σ') := div_pos hσ'0 (by linarith)
    linarith
  have hT2 : ‖zetaTail X σ'‖ ^ 2 ≤ ((σ' / (1 - σ') + 1 / 2) * Real.exp (-S)) ^ 2 :=
    pow_le_pow_left₀ hTpos.le hT 2
  have hexp : Real.exp (2 * S) = (Real.exp (-S) ^ 2)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  calc (σ / (1 - σ) - 1 / 2) * Real.exp (2 * S) / (σ' / (1 - σ') + 1 / 2) ^ 2
      = (σ / (1 - σ) - 1 / 2) / ((σ' / (1 - σ') + 1 / 2) * Real.exp (-S)) ^ 2 := by
        rw [hexp, mul_pow]; field_simp
    _ ≤ ‖riemannZeta (σ : ℂ)‖ / ((σ' / (1 - σ') + 1 / 2) * Real.exp (-S)) ^ 2 := by
        gcongr
    _ ≤ ‖riemannZeta (σ : ℂ)‖ / ‖zetaTail X σ'‖ ^ 2 := by
        apply div_le_div_of_nonneg_left (by linarith) (by positivity) hT2

/-- **Expulsion from uniform counting classes (conditional packaging).** If the real fake satisfied
the transfer inequality `|F(σ) - ζ(σ)| ≤ K σ X^{θ-σ}/(σ-θ)` of a counting class `𝒞(X, θ, K)` at a
real `σ ∈ (θ, 1-η)` with `σ ≥ 1/2` (membership implies it: THEOREM-paper-proof, Stieltjes), then
`K` is at least `(σ-θ) X^{σ-θ}/σ` times the exponential lower bound minus `σ/(1-σ) + 1/2`. -/
theorem expulsion_of_transfer_bound (X : ℝ) {η σ θ K : ℝ} (hη : 0 < η) (hσ : 1 / 2 ≤ σ)
    (hσ1 : σ + η < 1) (hθ : θ < σ) (hX : 0 < X)
    (hK : ‖poleShadow X η 0 (σ : ℂ) - riemannZeta σ‖ ≤ K * σ * X ^ (θ - σ) / (σ - θ)) :
    (σ - θ) * X ^ (σ - θ) / σ
        * ((σ / (1 - σ) - 1 / 2) * Real.exp (2 * ∑ p ∈ Nat.primesBelow ⌈X⌉₊, (p : ℝ) ^ (-(σ + η)))
            / ((σ + η) / (1 - (σ + η)) + 1 / 2) ^ 2 - (σ / (1 - σ) + 1 / 2))
      ≤ K := by
  have hσ0 : 0 < σ := by linarith
  have hlow := poleShadow_real_exp_large X hη hσ hσ1
  have hup := (norm_riemannZeta_real_bounds hσ0 (by linarith)).2
  have htri : ‖poleShadow X η 0 (σ : ℂ)‖ - ‖riemannZeta (σ : ℂ)‖
      ≤ ‖poleShadow X η 0 (σ : ℂ) - riemannZeta σ‖ := norm_sub_norm_le _ _
  have hpos : 0 < (σ - θ) * X ^ (σ - θ) / σ := by
    have : 0 < X ^ (σ - θ) := Real.rpow_pos_of_pos hX _
    have : 0 < σ - θ := by linarith
    positivity
  have hXX : X ^ (σ - θ) * X ^ (θ - σ) = 1 := by
    rw [← Real.rpow_add hX]; simp
  calc (σ - θ) * X ^ (σ - θ) / σ
        * ((σ / (1 - σ) - 1 / 2) * Real.exp (2 * ∑ p ∈ Nat.primesBelow ⌈X⌉₊, (p : ℝ) ^ (-(σ + η)))
            / ((σ + η) / (1 - (σ + η)) + 1 / 2) ^ 2 - (σ / (1 - σ) + 1 / 2))
      ≤ (σ - θ) * X ^ (σ - θ) / σ * (K * σ * X ^ (θ - σ) / (σ - θ)) := by
        apply mul_le_mul_of_nonneg_left _ hpos.le
        linarith
    _ = K * (X ^ (σ - θ) * X ^ (θ - σ)) := by
        have : σ - θ ≠ 0 := by linarith
        field_simp
    _ = K := by rw [hXX, mul_one]


end PoleShadow

/-! ## F. The rigidity window tests cannot tell the fake from `ζ` below `X` -/

/-- **Blindness of the two window tests.** Truncate the fake at `M` and form the finite even measure
`ν = δ₀ + Σ_{n=1}^{M} a_n (δ_n + δ_{-n})` (`r = 1`, as for `ζ`).  Its triangle-tested FE defect is
exactly `0`, and its modulated-triangle multiplicity test at every `1 ≤ m ≤ M` with `m < X` returns
`a_m = 1 = r`: the values `ζ`'s truncation gives. -/
theorem fake_window_tests_blind (X δ t : ℝ) (M : ℕ) :
    triPairHat (Finset.Icc 1 M) 1 (fun n : ℕ => fakeCoeff X δ t n) (fun n : ℕ => (n : ℝ))
        - triPair (Finset.Icc 1 M) 1 (fun n : ℕ => fakeCoeff X δ t n) (fun n : ℕ => (n : ℝ)) = 0
    ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M → (m : ℝ) < X →
      ∫ ξ in (-1 : ℝ)..1, (1 - |ξ|) * ((1 + ∑ n ∈ Finset.Icc 1 M,
          2 * fakeCoeff X δ t n * Real.cos (2 * π * ((n : ℤ) : ℝ) * ξ))
            * Real.cos (2 * π * ((m : ℤ) : ℝ) * ξ)) = 1 := by
  constructor
  · have hx : ∀ n ∈ Finset.Icc 1 M, (1 : ℝ) ≤ |((n : ℕ) : ℝ)| := by
      intro n hn
      have h1 := (Finset.mem_Icc.mp hn).1
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast h1
    rw [window_defect_identity _ _ _ _ hx]
    apply Finset.sum_eq_zero
    intro n _
    have hs : Real.sin (π * (n : ℝ)) = 0 := by
      rw [mul_comm]; exact Real.sin_nat_mul_pi n
    rw [hs]; ring
  · intro m hm1 hmM hmX
    have h := triPairHat_mod_int (Finset.Icc 1 M) 1 (fun n : ℕ => fakeCoeff X δ t n)
      (fun n : ℕ => (n : ℤ)) (m : ℤ) (fun n hn => by exact_mod_cast (Finset.mem_Icc.mp hn).1)
      (by exact_mod_cast hm1)
    rw [h]
    have hfilter : (Finset.Icc 1 M).filter (fun n : ℕ => (n : ℤ) = (m : ℤ)) = {m} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Nat.cast_inj]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro rfl; exact ⟨⟨hm1, hmM⟩, rfl⟩
    rw [hfilter, Finset.sum_singleton]
    exact fakeCoeff_eq_one_of_lt X δ t m hmX

end Crux2RigidityRate

#print axioms Crux2RigidityRate.triAnti_hasDerivAt
#print axioms Crux2RigidityRate.tri_cos_integral
#print axioms Crux2RigidityRate.tri_cos_integral_symm
#print axioms Crux2RigidityRate.tri_integral_one
#print axioms Crux2RigidityRate.four_dist_sq_le_sin_sq
#print axioms Crux2RigidityRate.triPairHat_eq
#print axioms Crux2RigidityRate.triPair_eq_of_gap
#print axioms Crux2RigidityRate.window_defect_identity
#print axioms Crux2RigidityRate.atom_le_triPairHat
#print axioms Crux2RigidityRate.sinc_sq_ge
#print axioms Crux2RigidityRate.window_defect_stability
#print axioms Crux2RigidityRate.window_defect_rigidity
#print axioms Crux2RigidityRate.window_defect_counting
#print axioms Crux2RigidityRate.fake_vonMangoldt_bracket_nonneg
#print axioms Crux2RigidityRate.fake_local_factor_identity
#print axioms Crux2RigidityRate.fake_local_coeffs_nonneg
#print axioms Crux2RigidityRate.fakeLocal_nonneg
#print axioms Crux2RigidityRate.fakeCoeff_nonneg
#print axioms Crux2RigidityRate.fakeCoeff_eq_one_of_lt
#print axioms Crux2RigidityRate.sincSq_int_ne_zero
#print axioms Crux2RigidityRate.tri_cos_integral_all
#print axioms Crux2RigidityRate.cos_mul_cos_eq
#print axioms Crux2RigidityRate.tri_cos_cos_integral
#print axioms Crux2RigidityRate.triPairHat_mod_eq
#print axioms Crux2RigidityRate.triPairHat_mod_int
#print axioms Crux2RigidityRate.ofLocal_apply
#print axioms Crux2RigidityRate.ofLocal_isMultiplicative
#print axioms Crux2RigidityRate.ofLocal_prime_pow
#print axioms Crux2RigidityRate.alphaP_eq
#print axioms Crux2RigidityRate.alphaBarP_eq
#print axioms Crux2RigidityRate.alpha_add
#print axioms Crux2RigidityRate.alpha_mul
#print axioms Crux2RigidityRate.fakeCoeff_eq_ofLocal
#print axioms Crux2RigidityRate.zeta_mul_gFun_prime_pow
#print axioms Crux2RigidityRate.fakeCoeff_eq_zeta_mul_gFun
#print axioms Crux2RigidityRate.norm_natCast_cpow_neg_lt_one
#print axioms Crux2RigidityRate.one_sub_natCast_cpow_ne_zero
#print axioms Crux2RigidityRate.prod_primesBelow_ne_zero
#print axioms Crux2RigidityRate.zetaTail_ne_zero
#print axioms Crux2RigidityRate.hasProd_inv_zetaTail
#print axioms Crux2RigidityRate.gLoc_zero
#print axioms Crux2RigidityRate.norm_gLoc_le_one
#print axioms Crux2RigidityRate.norm_gFun_le_one
#print axioms Crux2RigidityRate.LSeriesSummable_gFun
#print axioms Crux2RigidityRate.tsum_term_gFun_prime_pow
#print axioms Crux2RigidityRate.LSeries_gFun_eq
#print axioms Crux2RigidityRate.LSeries_fakeCoeff_eq_poleShadow
#print axioms Crux2RigidityRate.differentiableAt_prod_primesBelow
#print axioms Crux2RigidityRate.differentiableAt_zetaTail
#print axioms Crux2RigidityRate.zetaTail_residue
#print axioms Crux2RigidityRate.residue_ne_zero
#print axioms Crux2RigidityRate.tendsto_shift
#print axioms Crux2RigidityRate.tendsto_div_zetaTail_shift
#print axioms Crux2RigidityRate.tendsto_inv_zetaTail_shift
#print axioms Crux2RigidityRate.eventually_zetaTail_shift_ne_zero
#print axioms Crux2RigidityRate.s₀_re
#print axioms Crux2RigidityRate.s₀_im
#print axioms Crux2RigidityRate.s₀_ne_one
#print axioms Crux2RigidityRate.s₀_add_c₂
#print axioms Crux2RigidityRate.one_add_two_t_ne_one
#print axioms Crux2RigidityRate.one_add_two_t_re
#print axioms Crux2RigidityRate.poleShadow_tendsto_zero
#print axioms Crux2RigidityRate.poleShadow_div_tendsto
#print axioms Crux2RigidityRate.poleShadow_eventually_differentiableAt
#print axioms Crux2RigidityRate.poleShadow_differentiableAt_of_re
#print axioms Crux2RigidityRate.poleShadow_eq_zero_iff
#print axioms Crux2RigidityRate.poleShadow_residue
#print axioms Crux2RigidityRate.poleShadow_residue_ne_zero
#print axioms Crux2RigidityRate.poleShadow_simple_zero
#print axioms Crux2RigidityRate.poleShadow_real_double_zero
#print axioms Crux2RigidityRate.fakeCoeff_mul_of_coprime
#print axioms Crux2RigidityRate.mty_placement
#print axioms Crux2RigidityRate.two_le_max_rpow
#print axioms Crux2RigidityRate.finite_data_no_zero_free_region
#print axioms Crux2RigidityRate.mty_fake
#print axioms Crux2RigidityRate.norm_riemannZeta_real_bounds
#print axioms Crux2RigidityRate.norm_prod_primesBelow_real_le
#print axioms Crux2RigidityRate.poleShadow_real_exp_large
#print axioms Crux2RigidityRate.expulsion_of_transfer_bound
#print axioms Crux2RigidityRate.fake_window_tests_blind

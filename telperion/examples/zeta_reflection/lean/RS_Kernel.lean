/-  RS_Kernel.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 2:
    Riemann's kernels, their difference equations, Gaussian bounds, the Fresnel line integral,
    the pole-crossing lemmas and the Mordell closed form.

    Mathlib-only (imports `RS_Strip` only).

    ## The kernels

        rsD x = e^{i pi x} - e^{-i pi x}          (= 2 i sin(pi x); zeros exactly at the integers)
        rsG x = e^{ i pi x^2} / rsD x              (Riemann's kernel of the zeta integral)
        rsH x = e^{-i pi x^2} / rsD x              (the kernel of the chi-side integral)

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `rsD_eq_zero_iff`, `rsD_add_one`, `rsG_add_one`, `rsH_add_one` : zeros and the difference
        equations  rsG(x+1) = rsG x + e^{i pi (x^2+x)},  rsH(x+1) = rsH x - e^{-i pi (x^2+x)}.
      * `norm_rsG_le`, `norm_rsH_le` : on a slanted strip, away from the real axis (|Im x| >= 1), the
        kernels are bounded by exp(-2 pi (Im x)^2 + 2 pi D |Im x|)  (Gaussian decay).
      * `lineUp_fresnel`, `lineUp_gauss` : the Gaussian line integrals, e.g.
            lineUp c (x |-> e^{i pi (x^2+x) - x y}) = e^{y/2 + i y^2/(4 pi)}     (every c, every y).
      * `lineUp_same_gap`, `lineUp_cross` : moving the slope-(+1) line inside a gap (n, n+1) changes
        nothing; moving it across the pole at the integer n adds phi(n):
            lineUp c2 (rsG * phi) = lineUp c1 (rsG * phi) + phi n,   n-1 < c1 < n < c2 < n+1,
        for every phi holomorphic on the strip with at most exponential growth.  No residue theorem
        is used: the pole is removed by `dslope`, and the jump of the bare kernel is computed from
        the difference equation and the Fresnel integral.
      * `lineDn_same_gap`, `lineDn_cross` : the slope-(-1) analogues for rsH (by conjugation).
      * `lineUp_mordell` : the Mordell closed form, for 0 < c < 1 and every y:
            lineUp c (x |-> rsG x e^{-x y}) (e^{-y/2} - e^{y/2}) = e^{-y/2} - e^{i y^2/(4 pi)}.

    conjecture1_proved = False.  Contour identities for one explicit kernel; nothing here bears
    on RH.
-/
import RS_Strip

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. The kernels and their algebra -/

/-- The denominator `e^{i pi x} - e^{-i pi x} = 2 i sin (pi x)`. -/
def rsD (x : ℂ) : ℂ := cexp (↑π * I * x) - cexp (-(↑π * I * x))

/-- Riemann's kernel `e^{i pi x^2} / (e^{i pi x} - e^{-i pi x})`. -/
def rsG (x : ℂ) : ℂ := cexp (↑π * I * x ^ 2) / rsD x

/-- The conjugate-side kernel `e^{-i pi x^2} / (e^{i pi x} - e^{-i pi x})`. -/
def rsH (x : ℂ) : ℂ := cexp (-(↑π * I * x ^ 2)) / rsD x

theorem pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero

theorem rsD_eq_zero_iff (x : ℂ) : rsD x = 0 ↔ ∃ n : ℤ, x = n := by
  unfold rsD
  rw [sub_eq_zero, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * ↑π * I : ℂ) * x = (2 * ↑π * I) * n := by linear_combination hn
    exact mul_left_cancel₀ (by simp [I_ne_zero]) h2
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem rsD_int (n : ℤ) : rsD n = 0 := (rsD_eq_zero_iff _).mpr ⟨n, rfl⟩

theorem differentiable_rsD : Differentiable ℂ rsD := by
  unfold rsD; fun_prop

theorem hasDerivAt_rsD (x : ℂ) :
    HasDerivAt rsD (↑π * I * (cexp (↑π * I * x) + cexp (-(↑π * I * x)))) x := by
  have h1 : HasDerivAt (fun x : ℂ => ↑π * I * x) (↑π * I) x := by
    simpa using (hasDerivAt_id x).const_mul (↑π * I)
  have h2 : HasDerivAt (fun x : ℂ => -(↑π * I * x)) (-(↑π * I)) x := h1.neg
  have := h1.cexp.sub h2.cexp
  exact this.congr_deriv (by ring)

theorem deriv_rsD_int_ne_zero (n : ℤ) : deriv rsD n ≠ 0 := by
  rw [(hasDerivAt_rsD n).deriv]
  refine mul_ne_zero (mul_ne_zero pi_ne_zero' I_ne_zero) ?_
  intro h
  have h2 : cexp (↑π * I * n) * (cexp (↑π * I * n) + cexp (-(↑π * I * n))) = 0 := by
    rw [h, mul_zero]
  rw [mul_add, ← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero] at h2
  have h3 : cexp (↑π * I * n + ↑π * I * n) = 1 := by
    rw [show (↑π * I * n + ↑π * I * n : ℂ) = n * (2 * ↑π * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [h3] at h2
  norm_num at h2

theorem exp_neg_piI : cexp (-(↑π * I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

theorem rsD_add_one (x : ℂ) : rsD (x + 1) = -rsD x := by
  unfold rsD
  have e1 : cexp (↑π * I * (x + 1)) = -cexp (↑π * I * x) := by
    rw [show ↑π * I * (x + 1) = ↑π * I * x + ↑π * I by ring, Complex.exp_add,
      Complex.exp_pi_mul_I]; ring
  have e2 : cexp (-(↑π * I * (x + 1))) = -cexp (-(↑π * I * x)) := by
    rw [show -(↑π * I * (x + 1)) = -(↑π * I * x) + -(↑π * I) by ring, Complex.exp_add,
      exp_neg_piI]; ring
  rw [e1, e2]; ring

theorem rsG_add_one (x : ℂ) (hx : rsD x ≠ 0) :
    rsG (x + 1) = rsG x + cexp (↑π * I * (x ^ 2 + x)) := by
  unfold rsG
  rw [rsD_add_one]
  have e3 : cexp (↑π * I * (x + 1) ^ 2) =
      -(cexp (↑π * I * x ^ 2) * (cexp (↑π * I * x) * cexp (↑π * I * x))) := by
    rw [show ↑π * I * (x + 1) ^ 2 = ↑π * I * x ^ 2 + (↑π * I * x + ↑π * I * x) + ↑π * I by ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have e4 : cexp (↑π * I * (x ^ 2 + x)) = cexp (↑π * I * x ^ 2) * cexp (↑π * I * x) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e3, e4, neg_div_neg_eq]
  have huv : cexp (↑π * I * x) * cexp (-(↑π * I * x)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have key : cexp (↑π * I * x ^ 2) * (cexp (↑π * I * x) * cexp (↑π * I * x)) =
      cexp (↑π * I * x ^ 2) + cexp (↑π * I * x ^ 2) * cexp (↑π * I * x) * rsD x := by
    unfold rsD; linear_combination (cexp (↑π * I * x ^ 2)) * huv
  rw [key, add_div, mul_div_assoc, div_self hx, mul_one]

theorem rsH_add_one (x : ℂ) (hx : rsD x ≠ 0) :
    rsH (x + 1) = rsH x - cexp (-(↑π * I * (x ^ 2 + x))) := by
  unfold rsH
  rw [rsD_add_one]
  have e3 : cexp (-(↑π * I * (x + 1) ^ 2)) =
      -(cexp (-(↑π * I * x ^ 2)) * (cexp (-(↑π * I * x)) * cexp (-(↑π * I * x)))) := by
    rw [show -(↑π * I * (x + 1) ^ 2) =
        -(↑π * I * x ^ 2) + (-(↑π * I * x) + -(↑π * I * x)) + -(↑π * I) by ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_add, exp_neg_piI]; ring
  have e4 : cexp (-(↑π * I * (x ^ 2 + x))) =
      cexp (-(↑π * I * x ^ 2)) * cexp (-(↑π * I * x)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e3, e4, neg_div_neg_eq]
  have huv : cexp (↑π * I * x) * cexp (-(↑π * I * x)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have key : cexp (-(↑π * I * x ^ 2)) * (cexp (-(↑π * I * x)) * cexp (-(↑π * I * x))) =
      cexp (-(↑π * I * x ^ 2)) - cexp (-(↑π * I * x ^ 2)) * cexp (-(↑π * I * x)) * rsD x := by
    unfold rsD; linear_combination (cexp (-(↑π * I * x ^ 2))) * huv
  rw [key, sub_div, mul_div_assoc, div_self hx, mul_one]

/-! ## 2. Norm bounds -/

theorem norm_exp_piI_sq (x : ℂ) :
    ‖cexp (↑π * I * x ^ 2)‖ = Real.exp (-(2 * π * x.re * x.im)) := by
  rw [Complex.norm_exp]; congr 1; simp [pow_two, mul_re, mul_im]; ring

theorem norm_exp_neg_piI_sq (x : ℂ) :
    ‖cexp (-(↑π * I * x ^ 2))‖ = Real.exp (2 * π * x.re * x.im) := by
  rw [Complex.norm_exp]; congr 1; simp [pow_two, mul_re, mul_im]; ring

theorem norm_exp_piI (x : ℂ) : ‖cexp (↑π * I * x)‖ = Real.exp (-(π * x.im)) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]

theorem norm_exp_neg_piI (x : ℂ) : ‖cexp (-(↑π * I * x))‖ = Real.exp (π * x.im) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]

theorem norm_rsD_ge (x : ℂ) :
    Real.exp (π * |x.im|) - Real.exp (-(π * |x.im|)) ≤ ‖rsD x‖ := by
  unfold rsD
  rcases le_total 0 x.im with h | h
  · rw [abs_of_nonneg h]
    have := norm_sub_norm_le (cexp (-(↑π * I * x))) (cexp (↑π * I * x))
    rw [norm_exp_piI, norm_exp_neg_piI, norm_sub_rev] at this
    linarith
  · rw [abs_of_nonpos h, mul_neg, neg_neg]
    have := norm_sub_norm_le (cexp (↑π * I * x)) (cexp (-(↑π * I * x)))
    rw [norm_exp_piI, norm_exp_neg_piI] at this
    linarith

theorem one_le_norm_rsD {x : ℂ} (h : 1 ≤ |x.im|) : 1 ≤ ‖rsD x‖ := by
  have h1 := norm_rsD_ge x
  have hp : π ≤ π * |x.im| := by nlinarith [Real.pi_pos]
  have h2 : Real.exp π ≤ Real.exp (π * |x.im|) := Real.exp_le_exp.mpr hp
  have h3 : Real.exp (-(π * |x.im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, abs_nonneg x.im]
  have h4 : π + 1 ≤ Real.exp π := Real.add_one_le_exp π
  have h5 : 3 < π := Real.pi_gt_three
  linarith

theorem norm_rsG_le_of_im {x : ℂ} (h : 1 ≤ |x.im|) :
    ‖rsG x‖ ≤ Real.exp (-(2 * π * x.re * x.im)) := by
  unfold rsG
  rw [norm_div, norm_exp_piI_sq]
  have h1 := one_le_norm_rsD h
  exact div_le_self (Real.exp_pos _).le h1

theorem norm_rsH_le_of_im {x : ℂ} (h : 1 ≤ |x.im|) :
    ‖rsH x‖ ≤ Real.exp (2 * π * x.re * x.im) := by
  unfold rsH
  rw [norm_div, norm_exp_neg_piI_sq]
  have h1 := one_le_norm_rsD h
  exact div_le_self (Real.exp_pos _).le h1

/-- On the slanted strip `c1 <= Re x - Im x <= c2`, `‖x‖ <= 2 |Im x| + D`, `D = |c1| + |c2|`. -/
theorem norm_le_of_upStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) :
    ‖x‖ ≤ 2 * |x.im| + (|c₁| + |c₂|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im x
  have hd : |x.re - x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have h2 : |x.re| ≤ |x.im| + |x.re - x.im| := by
    calc |x.re| = |x.im + (x.re - x.im)| := by ring_nf
      _ ≤ |x.im| + |x.re - x.im| := abs_add_le _ _
  linarith

theorem norm_le_of_dnStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re + x.im ∈ Icc c₁ c₂) :
    ‖x‖ ≤ 2 * |x.im| + (|c₁| + |c₂|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im x
  have hd : |x.re + x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have h2 : |x.re| ≤ |x.im| + |x.re + x.im| := by
    calc |x.re| = |(-x.im) + (x.re + x.im)| := by ring_nf
      _ ≤ |-x.im| + |x.re + x.im| := abs_add_le _ _
      _ = |x.im| + |x.re + x.im| := by rw [abs_neg]
  linarith

/-- **Gaussian decay of `rsG` on a slope-(+1) strip.** -/
theorem norm_rsG_le {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) (h : 1 ≤ |x.im|) :
    ‖rsG x‖ ≤ Real.exp (-(2 * π) * x.im ^ 2 + 2 * π * (|c₁| + |c₂|) * |x.im|) := by
  refine (norm_rsG_le_of_im h).trans (Real.exp_le_exp.mpr ?_)
  have hd : |x.re - x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have key : x.re * x.im = x.im ^ 2 + (x.re - x.im) * x.im := by ring
  have h2 : -((x.re - x.im) * x.im) ≤ (|c₁| + |c₂|) * |x.im| := by
    calc -((x.re - x.im) * x.im) ≤ |(x.re - x.im) * x.im| := neg_le_abs _
      _ = |x.re - x.im| * |x.im| := abs_mul _ _
      _ ≤ (|c₁| + |c₂|) * |x.im| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  have hpi := Real.pi_pos
  nlinarith

/-- **Gaussian decay of `rsH` on a slope-(-1) strip.** -/
theorem norm_rsH_le {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re + x.im ∈ Icc c₁ c₂) (h : 1 ≤ |x.im|) :
    ‖rsH x‖ ≤ Real.exp (-(2 * π) * x.im ^ 2 + 2 * π * (|c₁| + |c₂|) * |x.im|) := by
  refine (norm_rsH_le_of_im h).trans (Real.exp_le_exp.mpr ?_)
  have hd : |x.re + x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have key : x.re * x.im = -x.im ^ 2 + (x.re + x.im) * x.im := by ring
  have h2 : (x.re + x.im) * x.im ≤ (|c₁| + |c₂|) * |x.im| := by
    calc (x.re + x.im) * x.im ≤ |(x.re + x.im) * x.im| := le_abs_self _
      _ = |x.re + x.im| * |x.im| := abs_mul _ _
      _ ≤ (|c₁| + |c₂|) * |x.im| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  have hpi := Real.pi_pos
  nlinarith

/-! ## 3. The Fresnel line integral -/

theorem one_add_I_sq : (1 + I : ℂ) ^ 2 = 2 * I := by
  ring_nf; rw [I_sq]; ring

theorem half_cpow_half_mul : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) * (1 + I) = cexp (↑π / 4 * I) := by
  have h1 : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have : ((1 / 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = (((1 / 2 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
      (ofReal_cpow (by norm_num) _).symm
    push_cast at this
    rw [this]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_one]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h1, Complex.exp_mul_I, ← ofReal_ofNat 4, ← ofReal_div, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

/-- **Fresnel line integral.**  For every complex shift `B` and every `c`,
    `lineUp c (x |-> e^{i pi (x+B)^2}) = (1/2)^{1/2} (1 + i) = e^{i pi / 4}`. -/
theorem lineUp_fresnel (c : ℝ) (B : ℂ) :
    lineUp c (fun x => cexp (↑π * I * (x + B) ^ 2)) = cexp (↑π / 4 * I) := by
  unfold lineUp
  set w : ℂ := c + B with hw
  have hpt : ∀ v : ℝ, cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2) =
      cexp ((-2 * ↑π) * (v : ℂ) ^ 2 + (2 * ↑π * I * w * (1 + I)) * v + ↑π * I * w ^ 2) := by
    intro v
    congr 1
    rw [hw]
    linear_combination (↑π * I * (v : ℂ) ^ 2) * one_add_I_sq + (2 * ↑π * (v : ℂ) ^ 2) * I_sq
  simp_rw [hpt]
  rw [integral_mul_const, integral_cexp_quadratic (by simp [Real.pi_pos])]
  have hexp : ↑π * I * w ^ 2 - (2 * ↑π * I * w * (1 + I)) ^ 2 / (4 * (-2 * ↑π)) = 0 := by
    have hpi := pi_ne_zero'
    field_simp
    linear_combination (4 * ↑π * I * w ^ 2 + 2 * ↑π * I ^ 2 * w ^ 2) * I_sq
  rw [hexp, Complex.exp_zero, mul_one]
  have hb : (↑π / -(-2 * ↑π) : ℂ) = 1 / 2 := by field_simp
  rw [hb, half_cpow_half_mul]

/-- **Gaussian line integral with a linear exponential.**  For every `c` and `y`,
    `lineUp c (x |-> e^{i pi (x^2+x) - x y}) = e^{y/2 + i y^2/(4 pi)}`. -/
theorem lineUp_gauss (c : ℝ) (y : ℂ) :
    lineUp c (fun x => cexp (↑π * I * (x ^ 2 + x) - x * y)) =
      cexp (y / 2 + I * y ^ 2 / (4 * ↑π)) := by
  set B : ℂ := 1 / 2 + I * y / (2 * ↑π) with hB
  have hpt : ∀ x : ℂ, cexp (↑π * I * (x ^ 2 + x) - x * y) =
      cexp (↑π * I * (x + B) ^ 2) * cexp (-(↑π * I * B ^ 2)) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    rw [hB]
    have hpi := pi_ne_zero'
    field_simp
    linear_combination (-(4 * ↑π * x * y)) * I_sq
  have : lineUp c (fun x => cexp (↑π * I * (x ^ 2 + x) - x * y)) =
      lineUp c (fun x => cexp (↑π * I * (x + B) ^ 2)) * cexp (-(↑π * I * B ^ 2)) := by
    unfold lineUp
    rw [← integral_mul_const]
    congr 1; ext v
    beta_reduce
    rw [hpt]; ring
  rw [this, lineUp_fresnel, ← Complex.exp_add]
  congr 1
  rw [hB]
  have hpi := pi_ne_zero'
  field_simp
  linear_combination (-(4 * I * y ^ 2 + 8 * ↑π * y)) * I_sq

theorem lineUp_gauss_zero (c : ℝ) :
    lineUp c (fun x => cexp (↑π * I * (x ^ 2 + x))) = 1 := by
  have := lineUp_gauss c 0
  simp only [mul_zero, sub_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Complex.exp_zero] at this
  exact this

/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/

theorem gauss_tail_small {C a b : ℝ} (ha : 0 < a) :
    ∀ ε > 0, ∃ Y : ℝ, 1 ≤ Y ∧ ∀ y : ℝ, Y ≤ |y| → C * Real.exp (-a * y ^ 2 + b * |y|) ≤ ε := by
  intro ε hε
  set K := Real.exp (b ^ 2 / (2 * a)) with hK
  set M := |C| * K + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨max 1 (2 / a * |Real.log (M / ε)|), le_max_left _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ |y| := le_trans (le_max_left _ _) hy
  have hy2 : 2 / a * |Real.log (M / ε)| ≤ |y| := le_trans (le_max_right _ _) hy
  have h1 : C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) := by
    calc C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * Real.exp (-a * y ^ 2 + b * |y|) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) :=
          mul_le_mul_of_nonneg_left (exp_quad_le a b y ha) (abs_nonneg C)
  have h2 : Real.exp (-(a / 2) * y ^ 2) ≤ Real.exp (-(a / 2) * |y|) := by
    apply Real.exp_le_exp.mpr
    have : |y| ≤ y ^ 2 := by
      rw [← sq_abs]; nlinarith
    nlinarith
  have h3 : Real.exp (-(a / 2) * |y|) ≤ ε / M := by
    have hl : |Real.log (M / ε)| ≤ a / 2 * |y| := by
      have := mul_le_mul_of_nonneg_left hy2 (le_of_lt (half_pos ha))
      rwa [← mul_assoc, show a / 2 * (2 / a) = 1 by field_simp, one_mul] at this
    calc Real.exp (-(a / 2) * |y|) ≤ Real.exp (-Real.log (M / ε)) := by
          apply Real.exp_le_exp.mpr
          have := le_abs_self (Real.log (M / ε))
          nlinarith
      _ = ε / M := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  calc C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) := h1
    _ ≤ M * Real.exp (-(a / 2) * |y|) := by
        have : |C| * (K * Real.exp (-(a / 2) * y ^ 2)) ≤ |C| * K * Real.exp (-(a / 2) * |y|) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : |C| * K * Real.exp (-(a / 2) * |y|) ≤ M * Real.exp (-(a / 2) * |y|) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        linarith
    _ ≤ M * (ε / M) := mul_le_mul_of_nonneg_left h3 hMpos.le
    _ = ε := by field_simp

theorem lineUp_pt_mem (c v : ℝ) :
    ((c : ℂ) + v * (1 + I)).re - ((c : ℂ) + v * (1 + I)).im ∈ Icc c c := by
  simp

theorem lineUp_pt_im (c v : ℝ) : ((c : ℂ) + v * (1 + I)).im = v := by simp

theorem lineDn_pt_mem (c v : ℝ) :
    ((c : ℂ) + v * (1 - I)).re + ((c : ℂ) + v * (1 - I)).im ∈ Icc c c := by
  simp

theorem lineDn_pt_im (c v : ℝ) : ((c : ℂ) + v * (1 - I)).im = -v := by simp

theorem integrable_lineUp {F : ℂ → ℂ} {c₁ c₂ c : ℝ} (hc : c ∈ Icc c₁ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    Integrable (fun v : ℝ => F (c + v * (1 + I))) := by
  have hmem : ∀ v : ℝ, ((c : ℂ) + v * (1 + I)) ∈ {x : ℂ | x.re - x.im ∈ Icc c₁ c₂} := by
    intro v
    simp only [mem_setOf_eq]
    have e : ((c : ℂ) + v * (1 + I)).re - ((c : ℂ) + v * (1 + I)).im = c := by simp
    rw [e]; exact hc
  refine integrable_of_continuous_of_tail (a := a) (b := b) (C := C) (R := 1)
    (hcont.comp_continuous (by fun_prop) hmem) ha (fun v hv => ?_)
  have := hbound _ (hmem v) (by rw [lineUp_pt_im]; exact hv)
  rwa [lineUp_pt_im] at this

theorem integrable_lineDn {F : ℂ → ℂ} {c₁ c₂ c : ℝ} (hc : c ∈ Icc c₁ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re + x.im ∈ Icc c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    Integrable (fun v : ℝ => F (c + v * (1 - I))) := by
  have hmem : ∀ v : ℝ, ((c : ℂ) + v * (1 - I)) ∈ {x : ℂ | x.re + x.im ∈ Icc c₁ c₂} := by
    intro v
    simp only [mem_setOf_eq]
    have e : ((c : ℂ) + v * (1 - I)).re + ((c : ℂ) + v * (1 - I)).im = c := by simp
    rw [e]; exact hc
  refine integrable_of_continuous_of_tail (a := a) (b := b) (C := C) (R := 1)
    (hcont.comp_continuous (by fun_prop) hmem) ha (fun v hv => ?_)
  have := hbound _ (hmem v) (by rw [lineDn_pt_im, abs_neg]; exact hv)
  rwa [lineDn_pt_im, abs_neg, neg_sq] at this

/-- `lineUp_eq_of_strip` with the integrability and decay hypotheses replaced by one Gaussian
    bound in `Im x` (valid for `|Im x| >= 1`). -/
theorem lineUp_eq_of_strip' {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    lineUp c₁ F = lineUp c₂ F := by
  refine lineUp_eq_of_strip hc hcont hdiff
    (integrable_lineUp ⟨le_rfl, hc⟩ hcont ha hbound)
    (integrable_lineUp ⟨hc, le_rfl⟩ hcont ha hbound) (fun ε hε => ?_)
  obtain ⟨Y, hY1, hY⟩ := gauss_tail_small (C := C) (b := b) ha ε hε
  refine ⟨2 * Y + (|c₁| + |c₂|), fun x hx hR => ?_⟩
  have hn := norm_le_of_upStrip hx
  have him : Y ≤ |x.im| := by linarith
  exact (hbound x hx (le_trans hY1 him)).trans (hY _ him)

theorem lineDn_eq_of_strip' {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re + x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re + x.im ∈ Ioo c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    lineDn c₁ F = lineDn c₂ F := by
  refine lineDn_eq_of_strip hc hcont hdiff
    (integrable_lineDn ⟨le_rfl, hc⟩ hcont ha hbound)
    (integrable_lineDn ⟨hc, le_rfl⟩ hcont ha hbound) (fun ε hε => ?_)
  obtain ⟨Y, hY1, hY⟩ := gauss_tail_small (C := C) (b := b) ha ε hε
  refine ⟨2 * Y + (|c₁| + |c₂|), fun x hx hR => ?_⟩
  have hn := norm_le_of_dnStrip hx
  have him : Y ≤ |x.im| := by linarith
  exact (hbound x hx (le_trans hY1 him)).trans (hY _ him)

/-- The Gaussian bound for `rsG * phi` on a slope-(+1) strip, for `phi` of exponential growth. -/
theorem norm_rsG_mul_le {φ : ℂ → ℂ} {c₁ c₂ A B : ℝ} {x : ℂ} (hx : x.re - x.im ∈ Icc c₁ c₂)
    (h1 : 1 ≤ |x.im|) (hφ : ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    ‖rsG x * φ x‖ ≤ (|A| * Real.exp (|B| * (|c₁| + |c₂|))) *
      Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |B|) * |x.im|) := by
  have hG := norm_rsG_le hx h1
  have hn := norm_le_of_upStrip hx
  have hφ' : ‖φ x‖ ≤ |A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|))) := by
    refine hφ.trans ?_
    calc A * Real.exp (B * ‖x‖) ≤ |A| * Real.exp (B * ‖x‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
      _ ≤ |A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
          apply Real.exp_le_exp.mpr
          calc B * ‖x‖ ≤ |B| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _)
            _ ≤ |B| * (2 * |x.im| + (|c₁| + |c₂|)) :=
                mul_le_mul_of_nonneg_left hn (abs_nonneg B)
  rw [norm_mul]
  calc ‖rsG x‖ * ‖φ x‖ ≤ Real.exp (-(2 * π) * x.im ^ 2 + 2 * π * (|c₁| + |c₂|) * |x.im|) *
        (|A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|)))) :=
        mul_le_mul hG hφ' (norm_nonneg _) (Real.exp_pos _).le
    _ = (|A| * Real.exp (|B| * (|c₁| + |c₂|))) *
        Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |B|) * |x.im|) := by
        have e : ∀ p q : ℝ, Real.exp p * (|A| * Real.exp q) = |A| * Real.exp (p + q) := by
          intro p q; rw [Real.exp_add]; ring
        have e' : ∀ p q : ℝ, |A| * Real.exp p * Real.exp q = |A| * Real.exp (p + q) := by
          intro p q; rw [Real.exp_add]; ring
        rw [e, e']; congr 2; ring

/-- The Gaussian bound for `rsH * psi` on a slope-(-1) strip. -/
theorem norm_rsH_mul_le {ψ : ℂ → ℂ} {c₁ c₂ A B : ℝ} {x : ℂ} (hx : x.re + x.im ∈ Icc c₁ c₂)
    (h1 : 1 ≤ |x.im|) (hψ : ‖ψ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    ‖rsH x * ψ x‖ ≤ (|A| * Real.exp (|B| * (|c₁| + |c₂|))) *
      Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |B|) * |x.im|) := by
  have hG := norm_rsH_le hx h1
  have hn := norm_le_of_dnStrip hx
  have hψ' : ‖ψ x‖ ≤ |A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|))) := by
    refine hψ.trans ?_
    calc A * Real.exp (B * ‖x‖) ≤ |A| * Real.exp (B * ‖x‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
      _ ≤ |A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
          apply Real.exp_le_exp.mpr
          calc B * ‖x‖ ≤ |B| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _)
            _ ≤ |B| * (2 * |x.im| + (|c₁| + |c₂|)) :=
                mul_le_mul_of_nonneg_left hn (abs_nonneg B)
  rw [norm_mul]
  calc ‖rsH x‖ * ‖ψ x‖ ≤ Real.exp (-(2 * π) * x.im ^ 2 + 2 * π * (|c₁| + |c₂|) * |x.im|) *
        (|A| * Real.exp (|B| * (2 * |x.im| + (|c₁| + |c₂|)))) :=
        mul_le_mul hG hψ' (norm_nonneg _) (Real.exp_pos _).le
    _ = (|A| * Real.exp (|B| * (|c₁| + |c₂|))) *
        Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |B|) * |x.im|) := by
        have e : ∀ p q : ℝ, Real.exp p * (|A| * Real.exp q) = |A| * Real.exp (p + q) := by
          intro p q; rw [Real.exp_add]; ring
        have e' : ∀ p q : ℝ, |A| * Real.exp p * Real.exp q = |A| * Real.exp (p + q) := by
          intro p q; rw [Real.exp_add]; ring
        rw [e, e']; congr 2; ring

/-! ## 5. Linearity and translation of line integrals -/

theorem lineUp_congr {F G : ℂ → ℂ} {c : ℝ}
    (h : ∀ v : ℝ, F (c + v * (1 + I)) = G (c + v * (1 + I))) : lineUp c F = lineUp c G := by
  unfold lineUp; congr 1; ext v; rw [h]

theorem lineDn_congr {F G : ℂ → ℂ} {c : ℝ}
    (h : ∀ v : ℝ, F (c + v * (1 - I)) = G (c + v * (1 - I))) : lineDn c F = lineDn c G := by
  unfold lineDn; congr 1; ext v; rw [h]

theorem lineUp_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineUp c (fun x => k * F x) = k * lineUp c F := by
  unfold lineUp; rw [← integral_const_mul]; congr 1; ext v; ring

theorem lineUp_add {F G : ℂ → ℂ} {c : ℝ}
    (hF : Integrable (fun v : ℝ => F (c + v * (1 + I))))
    (hG : Integrable (fun v : ℝ => G (c + v * (1 + I)))) :
    lineUp c (fun x => F x + G x) = lineUp c F + lineUp c G := by
  unfold lineUp
  rw [← integral_add (hF.mul_const _) (hG.mul_const _)]
  congr 1; ext v; ring

theorem lineUp_sub_mul {F G : ℂ → ℂ} {c : ℝ} (k : ℂ)
    (hF : Integrable (fun v : ℝ => F (c + v * (1 + I))))
    (hG : Integrable (fun v : ℝ => G (c + v * (1 + I)))) :
    lineUp c (fun x => F x - k * G x) = lineUp c F - k * lineUp c G := by
  unfold lineUp
  rw [← integral_const_mul, ← integral_sub (hF.mul_const _) ((hG.mul_const _).const_mul _)]
  congr 1; ext v; ring

theorem lineUp_add_one (c : ℝ) (F : ℂ → ℂ) :
    lineUp (c + 1) F = lineUp c (fun x => F (x + 1)) := by
  unfold lineUp; congr 1; ext v; congr 2; push_cast; ring

/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn

theorem differentiableAt_rsG {x : ℂ} (h : rsD x ≠ 0) : DifferentiableAt ℂ rsG x := by
  unfold rsG
  exact ((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (↑π * I * x ^ 2))) x).div
    (differentiable_rsD x) h

theorem differentiableAt_rsH {x : ℂ} (h : rsD x ≠ 0) : DifferentiableAt ℂ rsH x := by
  unfold rsH
  exact ((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (-(↑π * I * x ^ 2)))) x).div
    (differentiable_rsD x) h

/-- A point of the slope-(+1) line through a non-integer `c` is never an integer. -/
theorem lineUp_pt_ne_int {c : ℝ} (hc : ∀ m : ℤ, (m : ℝ) ≠ c) (v : ℝ) (n : ℤ) :
    (c : ℂ) + v * (1 + I) ≠ n := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rw [him] at hre
  exact hc n (by linarith)

theorem lineDn_pt_ne_int {c : ℝ} (hc : ∀ m : ℤ, (m : ℝ) ≠ c) (v : ℝ) (n : ℤ) :
    (c : ℂ) + v * (1 - I) ≠ n := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rw [him] at hre
  exact hc n (by linarith)

theorem notInt_of_Ioo {c : ℝ} {n : ℤ} (h₁ : (n : ℝ) < c) (h₂ : c < n + 1) :
    ∀ m : ℤ, (m : ℝ) ≠ c := by
  intro m hm
  rw [← hm] at h₁ h₂
  have a : n < m := by exact_mod_cast h₁
  have b : m < n + 1 := by exact_mod_cast h₂
  omega

/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/

theorem fresnel_pt (c : ℝ) (B : ℂ) (v : ℝ) :
    cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2) =
      cexp ((-2 * ↑π) * (v : ℂ) ^ 2 + (2 * ↑π * I * (c + B) * (1 + I)) * v + ↑π * I * (c + B) ^ 2) := by
  congr 1
  linear_combination (↑π * I * (v : ℂ) ^ 2) * one_add_I_sq + (2 * ↑π * (v : ℂ) ^ 2) * I_sq

theorem integrable_fresnel (c : ℝ) (B : ℂ) :
    Integrable (fun v : ℝ => cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2)) := by
  have := integrable_cexp_quadratic' (b := -2 * ↑π) (by simp [Real.pi_pos])
    (2 * ↑π * I * (c + B) * (1 + I)) (↑π * I * (c + B) ^ 2)
  refine this.congr (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [fresnel_pt]

theorem gauss_pt (y x : ℂ) :
    cexp (↑π * I * (x ^ 2 + x) - x * y) =
      cexp (↑π * I * (x + (1 / 2 + I * y / (2 * ↑π))) ^ 2) *
        cexp (-(↑π * I * (1 / 2 + I * y / (2 * ↑π)) ^ 2)) := by
  rw [← Complex.exp_add]
  congr 1
  have hpi := pi_ne_zero'
  field_simp
  linear_combination (-(4 * ↑π * x * y)) * I_sq

theorem integrable_lineUp_gauss (c : ℝ) (y : ℂ) :
    Integrable (fun v : ℝ => cexp (↑π * I * (((c : ℂ) + v * (1 + I)) ^ 2 + ((c : ℂ) + v * (1 + I)))
      - ((c : ℂ) + v * (1 + I)) * y)) := by
  have := (integrable_fresnel c (1 / 2 + I * y / (2 * ↑π))).mul_const
    (cexp (-(↑π * I * (1 / 2 + I * y / (2 * ↑π)) ^ 2)))
  refine this.congr (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [gauss_pt]

/-! ## 8. Moving the line inside a gap, and across a pole -/

/-- **Same gap.**  If the closed crossing interval `[c1, c2]` contains no integer, the slope-(+1)
    integral of `rsG * phi` does not depend on the crossing point. -/
theorem lineUp_same_gap {φ : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hno : ∀ m : ℤ, (m : ℝ) ∉ Icc c₁ c₂)
    (hφ : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ φ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineUp c₁ (fun x => rsG x * φ x) = lineUp c₂ (fun x => rsG x * φ x) := by
  have hD : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → rsD x ≠ 0 := by
    intro x hx
    refine rsD_ne_zero_of_ne fun n hn => hno n ?_
    rw [hn] at hx; simpa using hx
  have hdA : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ (fun x => rsG x * φ x) x :=
    fun x hx => (differentiableAt_rsG (hD x hx)).mul (hφ x hx)
  exact lineUp_eq_of_strip' hc (fun x hx => (hdA x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hdA x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt) (a := 2 * π)
    (by positivity) (fun x hx h1 => norm_rsG_mul_le hx h1 (hgrow x hx))

theorem integrable_lineUp_rsG_mul {φ : ℂ → ℂ} {c₁ c₂ c : ℝ} (hc : c ∈ Icc c₁ c₂)
    (hcl : ∀ m : ℤ, (m : ℝ) ≠ c)
    (hφ : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ContinuousAt φ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    Integrable (fun v : ℝ => rsG (c + v * (1 + I)) * φ (c + v * (1 + I))) := by
  have hcont : ContinuousOn (fun x => rsG x * φ x) {x : ℂ | x.re - x.im ∈ Icc c c} := by
    intro x hx
    have hxc : x.re - x.im = c := le_antisymm hx.2 hx.1
    have hD : rsD x ≠ 0 := by
      refine rsD_ne_zero_of_ne fun n hn => hcl n ?_
      rw [hn] at hxc; simpa using hxc
    exact ((differentiableAt_rsG hD).continuousAt.mul
      (hφ x (by rw [hxc]; exact hc))).continuousWithinAt
  exact integrable_lineUp (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcont (a := 2 * π) (by positivity)
    (fun x hx h1 => norm_rsG_mul_le hx h1 (hgrow x (by
      have hxc : x.re - x.im = c := le_antisymm hx.2 hx.1
      rw [hxc]; exact hc)))

theorem integrable_lineUp_rsG {c : ℝ} (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Integrable (fun v : ℝ => rsG (c + v * (1 + I))) := by
  have := integrable_lineUp_rsG_mul (φ := fun _ => (1 : ℂ)) (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩
    hcl (fun x _ => continuousAt_const) (A := 1) (B := 0) (fun x _ => by simp)
  simpa using this

/-- **The jump of the bare kernel across a pole.**  `lineUp c2 rsG = lineUp c1 rsG + 1` for
    `n - 1 < c1 < n < c2 < n + 1`: translation by 1, the difference equation, and the Fresnel
    integral `lineUp c (e^{i pi (x^2+x)}) = 1`. -/
theorem lineUp_rsG_jump {n : ℤ} {c₁ c₂ : ℝ}
    (h₁ : (n : ℝ) - 1 < c₁) (h₁' : c₁ < n) (h₂ : (n : ℝ) < c₂) (h₂' : c₂ < n + 1) :
    lineUp c₂ rsG = lineUp c₁ rsG + 1 := by
  have hcl₁ : ∀ m : ℤ, (m : ℝ) ≠ c₁ :=
    notInt_of_Ioo (n := n - 1) (by push_cast; linarith) (by push_cast; linarith)
  have hstep : lineUp (c₁ + 1) rsG = lineUp c₁ rsG + 1 := by
    rw [lineUp_add_one]
    have h1 : lineUp c₁ (fun x => rsG (x + 1)) =
        lineUp c₁ (fun x => rsG x + cexp (↑π * I * (x ^ 2 + x))) := by
      refine lineUp_congr fun v => ?_
      exact rsG_add_one _ (rsD_ne_zero_of_ne (lineUp_pt_ne_int hcl₁ v))
    have hg : Integrable (fun v : ℝ => cexp (↑π * I * (((c₁ : ℂ) + v * (1 + I)) ^ 2 +
        ((c₁ : ℂ) + v * (1 + I))))) := by
      simpa using integrable_lineUp_gauss c₁ 0
    rw [h1, lineUp_add (integrable_lineUp_rsG hcl₁) hg, lineUp_gauss_zero]
  have hmid : lineUp c₂ rsG = lineUp (c₁ + 1) rsG := by
    have hno : ∀ c c' : ℝ, c ≤ c' → (n : ℝ) < c → c' < n + 1 →
        lineUp c rsG = lineUp c' rsG := by
      intro c c' hcc hc hc'
      have := lineUp_same_gap (φ := fun _ => (1 : ℂ)) hcc
        (fun m hm => notInt_of_Ioo (n := n) (lt_of_lt_of_le hc hm.1) (lt_of_le_of_lt hm.2 hc') m
          rfl) (fun x _ => differentiableAt_const _) (A := 1) (B := 0) (fun x _ => by simp)
      simpa using this
    rcases le_total c₂ (c₁ + 1) with h | h
    · exact hno _ _ h h₂ (by linarith)
    · exact (hno _ _ h (by linarith) h₂').symm
  rw [hmid, hstep]

/-- **Crossing a pole.**  For `n - 1 < c1 < n < c2 < n + 1` and `phi` holomorphic on the closed
    strip between the two lines, with at most exponential growth there:
        lineUp c2 (rsG * phi) = lineUp c1 (rsG * phi) + phi n.
    (Riemann's residue `phi(n) / (2 pi i)` times `2 pi i`, with no residue theorem: the pole is
    removed with `dslope`.) -/
theorem lineUp_cross {φ : ℂ → ℂ} {n : ℤ} {c₁ c₂ : ℝ}
    (h₁ : (n : ℝ) - 1 < c₁) (h₁' : c₁ < n) (h₂ : (n : ℝ) < c₂) (h₂' : c₂ < n + 1)
    (hφ : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ φ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineUp c₂ (fun x => rsG x * φ x) = lineUp c₁ (fun x => rsG x * φ x) + φ n := by
  have hc : c₁ ≤ c₂ := by linarith
  have hcl₁ : ∀ m : ℤ, (m : ℝ) ≠ c₁ :=
    notInt_of_Ioo (n := n - 1) (by push_cast; linarith) (by push_cast; linarith)
  have hcl₂ : ∀ m : ℤ, (m : ℝ) ≠ c₂ := notInt_of_Ioo h₂ h₂'
  -- the only integer of the closed strip is `n`
  have honly : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → x ≠ n → rsD x ≠ 0 := by
    intro x hx hxn h0
    obtain ⟨m, rfl⟩ := (rsD_eq_zero_iff x).mp h0
    have hm : (m : ℝ) ∈ Icc c₁ c₂ := by simpa using hx
    have a : n - 1 < m := by exact_mod_cast (show ((n - 1 : ℤ) : ℝ) < m by push_cast; linarith [hm.1])
    have b : m < n + 1 := by exact_mod_cast (show (m : ℝ) < ((n + 1 : ℤ) : ℝ) by push_cast; linarith [hm.2])
    have : m = n := by omega
    exact hxn (by rw [this])
  have hnS : ((n : ℂ)).re - ((n : ℂ)).im ∈ Icc c₁ c₂ := by simp; exact ⟨h₁'.le, h₂.le⟩
  have hφn : DifferentiableAt ℂ φ n := hφ n hnS
  -- the regularised integrand
  set Q : ℂ → ℂ := fun x => cexp (↑π * I * x ^ 2) * dslope φ n x / dslope rsD n x with hQ
  have hdsD : Differentiable ℂ (dslope rsD n) := fun x =>
    ((differentiableOn_dslope Filter.univ_mem).mpr differentiable_rsD.differentiableOn).differentiableAt
      Filter.univ_mem
  have hden : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → dslope rsD n x ≠ 0 := by
    intro x hx
    by_cases hxn : x = n
    · rw [hxn, dslope_same]; exact deriv_rsD_int_ne_zero n
    · rw [dslope_of_ne _ hxn, slope_def_field, rsD_int, sub_zero]
      exact div_ne_zero (honly x hx hxn) (sub_ne_zero.mpr hxn)
  have hQeq : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → x ≠ n → Q x = rsG x * (φ x - φ n) := by
    intro x hx hxn
    simp only [hQ, rsG]
    rw [dslope_of_ne _ hxn, dslope_of_ne _ hxn, slope_def_field, slope_def_field, rsD_int, sub_zero]
    have h1 := honly x hx hxn
    have h2 : x - n ≠ 0 := sub_ne_zero.mpr hxn
    field_simp
  have hcontQ : ContinuousOn Q {x : ℂ | x.re - x.im ∈ Icc c₁ c₂} := by
    intro x hx
    have hnum : ContinuousWithinAt (fun x => cexp (↑π * I * x ^ 2) * dslope φ n x)
        {x : ℂ | x.re - x.im ∈ Icc c₁ c₂} x := by
      refine (Continuous.continuousWithinAt (by fun_prop)).mul ?_
      by_cases hxn : x = n
      · rw [hxn]; exact (continuousAt_dslope_same.mpr hφn).continuousWithinAt
      · exact (continuousWithinAt_dslope_of_ne hxn).mpr (hφ x hx).continuousAt.continuousWithinAt
    exact hnum.div (hdsD x).continuousAt.continuousWithinAt (hden x hx)
  have hopen : IsOpen {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂} :=
    isOpen_Ioo.preimage (by fun_prop)
  have hnT : (n : ℂ) ∈ {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂} := by
    simp only [mem_setOf_eq]; simp; exact ⟨h₁', h₂⟩
  have hdiffQ : DifferentiableOn ℂ Q {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂} := by
    have hdsl : DifferentiableOn ℂ (dslope φ n) {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂} :=
      (differentiableOn_dslope (hopen.mem_nhds hnT)).mpr
        (fun x hx => (hφ x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt)
    intro x hx
    exact ((((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (↑π * I * x ^ 2))) x).differentiableWithinAt).mul
      (hdsl x hx)).div (hdsD x).differentiableWithinAt (hden x ⟨hx.1.le, hx.2.le⟩)
  -- growth of phi - phi n
  have hgrow' : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ →
      ‖φ x - φ n‖ ≤ (|A| + ‖φ n‖) * Real.exp (|B| * ‖x‖) := by
    intro x hx
    have h1 : 1 ≤ Real.exp (|B| * ‖x‖) := Real.one_le_exp (by positivity)
    have h2 : A * Real.exp (B * ‖x‖) ≤ |A| * Real.exp (|B| * ‖x‖) := by
      calc A * Real.exp (B * ‖x‖) ≤ |A| * Real.exp (B * ‖x‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
        _ ≤ |A| * Real.exp (|B| * ‖x‖) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _))
    calc ‖φ x - φ n‖ ≤ ‖φ x‖ + ‖φ n‖ := norm_sub_le _ _
      _ ≤ |A| * Real.exp (|B| * ‖x‖) + ‖φ n‖ * Real.exp (|B| * ‖x‖) := by
          have := hgrow x hx
          nlinarith [norm_nonneg (φ n)]
      _ = (|A| + ‖φ n‖) * Real.exp (|B| * ‖x‖) := by ring
  have hQbound : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖Q x‖ ≤ (|(|A| + ‖φ n‖)| * Real.exp (|(|B|)| * (|c₁| + |c₂|))) *
        Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |(|B|)|) * |x.im|) := by
    intro x hx h1
    have hxn : x ≠ n := by
      intro h; rw [h] at h1; norm_num at h1
    rw [hQeq x hx hxn]
    exact norm_rsG_mul_le (φ := fun x => φ x - φ n) hx h1 (hgrow' x hx)
  have hQline : lineUp c₁ Q = lineUp c₂ Q :=
    lineUp_eq_of_strip' hc hcontQ hdiffQ (by positivity) hQbound
  -- integrability of the pieces on both lines
  have hcontφ : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ContinuousAt φ x :=
    fun x hx => (hφ x hx).continuousAt
  have hi₁ := integrable_lineUp_rsG_mul ⟨le_rfl, hc⟩ hcl₁ hcontφ hgrow
  have hi₂ := integrable_lineUp_rsG_mul ⟨hc, le_rfl⟩ hcl₂ hcontφ hgrow
  have hQ₁ : lineUp c₁ Q = lineUp c₁ (fun x => rsG x * φ x) - φ n * lineUp c₁ rsG := by
    rw [← lineUp_sub_mul _ hi₁ (integrable_lineUp_rsG hcl₁)]
    refine lineUp_congr fun v => ?_
    have hmem : ((c₁ : ℂ) + v * (1 + I)).re - ((c₁ : ℂ) + v * (1 + I)).im ∈ Icc c₁ c₂ := by
      simp; exact hc
    rw [hQeq _ hmem (lineUp_pt_ne_int hcl₁ v n)]; ring
  have hQ₂ : lineUp c₂ Q = lineUp c₂ (fun x => rsG x * φ x) - φ n * lineUp c₂ rsG := by
    rw [← lineUp_sub_mul _ hi₂ (integrable_lineUp_rsG hcl₂)]
    refine lineUp_congr fun v => ?_
    have hmem : ((c₂ : ℂ) + v * (1 + I)).re - ((c₂ : ℂ) + v * (1 + I)).im ∈ Icc c₁ c₂ := by
      simp; exact hc
    rw [hQeq _ hmem (lineUp_pt_ne_int hcl₂ v n)]; ring
  have hjump := lineUp_rsG_jump h₁ h₁' h₂ h₂'
  rw [hQ₁, hQ₂, hjump] at hQline
  linear_combination -hQline

/-! ## 9. The slope-(-1) side by conjugation -/

open ComplexConjugate in
theorem conj_lineUp_pt (c v : ℝ) : conj ((c : ℂ) + v * (1 + I)) = (c : ℂ) + v * (1 - I) := by
  simp only [map_add, map_mul, Complex.conj_ofReal, map_one, Complex.conj_I]; ring

open ComplexConjugate in
theorem lineDn_eq_conj (c : ℝ) (F : ℂ → ℂ) :
    lineDn c F = conj (lineUp c (fun x => conj (F (conj x)))) := by
  unfold lineDn lineUp
  rw [← integral_conj]
  congr 1; ext v
  rw [map_mul, Complex.conj_conj, conj_lineUp_pt]
  congr 1
  simp only [map_add, map_one, Complex.conj_I]; ring

open ComplexConjugate in
theorem conj_rsD_conj (x : ℂ) : conj (rsD (conj x)) = -rsD x := by
  unfold rsD
  rw [map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  ring_nf

open ComplexConjugate in
theorem conj_rsH_conj (x : ℂ) : conj (rsH (conj x)) = -rsG x := by
  unfold rsH rsG
  rw [map_div₀, conj_rsD_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  rw [div_neg]
  ring_nf

open ComplexConjugate in
theorem lineDn_rsH_eq (c : ℝ) (ψ : ℂ → ℂ) :
    lineDn c (fun x => rsH x * ψ x) =
      -conj (lineUp c (fun x => rsG x * conj (ψ (conj x)))) := by
  rw [lineDn_eq_conj, ← map_neg]
  congr 1
  have : (fun x => conj (rsH (conj x) * ψ (conj x))) =
      fun x => (-1) * (rsG x * conj (ψ (conj x))) := by
    ext x; rw [map_mul, conj_rsH_conj]; ring
  rw [this, lineUp_const_mul]; ring

open ComplexConjugate in
theorem conj_mem_dnStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) :
    (conj x).re + (conj x).im ∈ Icc c₁ c₂ := by
  simpa [sub_eq_add_neg] using hx

/-- **Crossing a pole, slope (-1).**  For `n - 1 < c1 < n < c2 < n + 1` and `psi` holomorphic on the
    closed slope-(-1) strip with at most exponential growth:
        lineDn c2 (rsH * psi) = lineDn c1 (rsH * psi) - psi n. -/
theorem lineDn_cross {ψ : ℂ → ℂ} {n : ℤ} {c₁ c₂ : ℝ}
    (h₁ : (n : ℝ) - 1 < c₁) (h₁' : c₁ < n) (h₂ : (n : ℝ) < c₂) (h₂' : c₂ < n + 1)
    (hψ : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ ψ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → ‖ψ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineDn c₂ (fun x => rsH x * ψ x) = lineDn c₁ (fun x => rsH x * ψ x) - ψ n := by
  open ComplexConjugate in
  rw [lineDn_rsH_eq, lineDn_rsH_eq]
  have hc := lineUp_cross (φ := fun x => (starRingEnd ℂ) (ψ ((starRingEnd ℂ) x))) h₁ h₁' h₂ h₂'
    (fun x hx => differentiableAt_conj_conj_iff.mpr (hψ _ (conj_mem_dnStrip hx))) (A := A) (B := B)
    (fun x hx => by
      rw [RCLike.norm_conj]
      have := hgrow _ (conj_mem_dnStrip hx)
      rwa [RCLike.norm_conj] at this)
  rw [hc, map_add, Complex.conj_conj, map_intCast]
  ring

theorem lineDn_same_gap {ψ : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hno : ∀ m : ℤ, (m : ℝ) ∉ Icc c₁ c₂)
    (hψ : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ ψ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → ‖ψ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineDn c₁ (fun x => rsH x * ψ x) = lineDn c₂ (fun x => rsH x * ψ x) := by
  rw [lineDn_rsH_eq, lineDn_rsH_eq]
  congr 2
  exact lineUp_same_gap (φ := fun x => (starRingEnd ℂ) (ψ ((starRingEnd ℂ) x))) hc hno
    (fun x hx => differentiableAt_conj_conj_iff.mpr (hψ _ (conj_mem_dnStrip hx))) (A := A) (B := B)
    (fun x hx => by
      rw [RCLike.norm_conj]
      have := hgrow _ (conj_mem_dnStrip hx)
      rwa [RCLike.norm_conj] at this)

/-! ## 10. The Mordell closed form -/

/-- **Mordell's integral.**  For `0 < c < 1` and every complex `y`,
        lineUp c (x |-> rsG x e^{-x y}) (e^{-y/2} - e^{y/2}) = e^{-y/2} - e^{i y^2/(4 pi)}.
    Proof: cross the pole at `1` (`lineUp_cross`), translate the line back by `1` using the difference
    equation (`rsG_add_one`), and evaluate the Gaussian term (`lineUp_gauss`). -/
theorem lineUp_mordell {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (y : ℂ) :
    lineUp c (fun x => rsG x * cexp (-(x * y))) * (cexp (-y / 2) - cexp (y / 2)) =
      cexp (-y / 2) - cexp (I * y ^ 2 / (4 * ↑π)) := by
  set K := lineUp c (fun x => rsG x * cexp (-(x * y))) with hK
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ c :=
    notInt_of_Ioo (n := 0) (by simpa using hc) (by simpa using hc1)
  have hgrow : ∀ x : ℂ, ‖cexp (-(x * y))‖ ≤ 1 * Real.exp (‖y‖ * ‖x‖) := by
    intro x; rw [one_mul]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_neg, norm_mul, mul_comm]
  have hcross := lineUp_cross (φ := fun x => cexp (-(x * y))) (n := 1) (c₁ := c) (c₂ := c + 1)
    (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (fun x _ => by fun_prop) (A := 1) (B := ‖y‖) (fun x _ => hgrow x)
  have hi1 : Integrable (fun v : ℝ => rsG (c + v * (1 + I)) * cexp (-((c + v * (1 + I)) * y))) :=
    integrable_lineUp_rsG_mul (φ := fun x => cexp (-(x * y))) (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcl
      (fun x _ => by fun_prop) (A := 1) (B := ‖y‖) (fun x _ => hgrow x)
  have htr : lineUp (c + 1) (fun x => rsG x * cexp (-(x * y))) =
      cexp (-y) * K + cexp (-y) * cexp (y / 2 + I * y ^ 2 / (4 * ↑π)) := by
    rw [lineUp_add_one]
    have h1 : lineUp c (fun x => rsG (x + 1) * cexp (-((x + 1) * y))) =
        lineUp c (fun x => cexp (-y) * (rsG x * cexp (-(x * y))) +
          cexp (-y) * cexp (↑π * I * (x ^ 2 + x) - x * y)) := by
      refine lineUp_congr fun v => ?_
      rw [rsG_add_one _ (rsD_ne_zero_of_ne (lineUp_pt_ne_int hcl v))]
      have e1 : cexp (-(((c : ℂ) + v * (1 + I) + 1) * y)) =
          cexp (-y) * cexp (-(((c : ℂ) + v * (1 + I)) * y)) := by
        rw [← Complex.exp_add]; ring_nf
      have e2 : cexp (↑π * I * (((c : ℂ) + v * (1 + I)) ^ 2 + ((c : ℂ) + v * (1 + I)))) *
          cexp (-(((c : ℂ) + v * (1 + I)) * y)) =
          cexp (↑π * I * (((c : ℂ) + v * (1 + I)) ^ 2 + ((c : ℂ) + v * (1 + I))) -
            ((c : ℂ) + v * (1 + I)) * y) := by
        rw [← Complex.exp_add]; ring_nf
      rw [e1, ← e2]; ring
    rw [h1, lineUp_add (hi1.const_mul _) ((integrable_lineUp_gauss c y).const_mul _),
      lineUp_const_mul, lineUp_const_mul, lineUp_gauss]
  have h : cexp (-y) * K + cexp (-y) * cexp (y / 2 + I * y ^ 2 / (4 * ↑π)) = K + cexp (-y) := by
    rw [← htr, hcross, Int.cast_one, one_mul]
  have hEE : cexp (-y) = cexp (-y / 2) * cexp (-y / 2) := by
    rw [← Complex.exp_add]; ring_nf
  have hEG : cexp (-y) * cexp (y / 2 + I * y ^ 2 / (4 * ↑π)) =
      cexp (-y / 2) * cexp (I * y ^ 2 / (4 * ↑π)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have hE : cexp (-y / 2) * cexp (y / 2) = 1 := by
    rw [← Complex.exp_add, show -y / 2 + y / 2 = 0 by ring, Complex.exp_zero]
  rw [hEG, hEE] at h
  linear_combination cexp (y / 2) * h -
    (cexp (-y / 2) * K + cexp (I * y ^ 2 / (4 * ↑π)) - cexp (-y / 2)) * hE

end RSInt

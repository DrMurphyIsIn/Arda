/-  RS_B3Bound.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 3: the
    analytic estimates and THE B3 HEADLINE.  Mathlib-only (imports `RS_B3`).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0` : for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase phi with
      |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= 2 t^(-3/4),
      where rsRem t is the EXACT Riemann-Siegel remainder of B2 and Psi = Gabcke's C0.  With B2's
      `completed_re_eq_rs_cos` this is the classical
          Z(t) = 2 sum_{n<=N} n^(-1/2) cos(theta - t log n) + (-1)^(N-1) (t/2pi)^(-1/4) C0(p) + R,
          |R| <= 2 t^(-3/4)   (t >= 10000),
      with an explicit, kernel-checked constant (Gabcke's sharper 0.127 is NOT claimed).
      `rs_remainder_C0_alpha` is the same bound in the saddle variable a = sqrt(t/2pi):
      |...| <= (2/5) a^(-3/2).

    ## The estimates behind it

      * `integral_sq_mul_exp_neg_mul_sq` : int v^2 e^{-b v^2} dv = sqrt(pi/b) / (2b).
      * `norm_rsD_ge_two_pi_im` : |rsD z| >= 2 pi |Im z|;  `two_le_norm_rsD_midline` : |rsD| >= 2 on
        the line Re x - Im x = 1/2 (sin^2 + sinh^2 >= 1).
      * `norm_rsPhi_sub_one_le` : for |w| <= a/2 the saddle-point amplitude satisfies
            |rsPhi a w - 1| <= e e^e,   e = |w|/(2a) + |w|^2/(2a^2) + (4 pi/3)|w|^3/a
        (complex Taylor bounds for log(1+u), Mathlib `norm_log_sub_logTaylor_le`).
      * `saddle_arg_le` : along the steepest-descent line, 2 pi a^2 arg(1 + v(1+i)/a) - 2 pi (a+v) v
        <= -pi v^2 for every real v (a derivative-sign argument: the saddle is a global maximum);
        `norm_gauss_rsPhi_le` : |e^{2 pi i w^2} rsPhi a w| <= 2 e^{-pi v^2} on w = v(1+i).
      * `rsJ_eq_mid`, `norm_rsJ_le` : the tau = 2 Mordell integral moves (strip Cauchy, no pole) to the
        midline through 1/2 - p, where |rsJ p| <= 4 uniformly in p ∈ (0,1).
      * `norm_E1_integrand_near` (|v| <= a/9) / `norm_E1_integrand_far` (|v| >= a/9), `norm_rsE1_le`,
        `E1_const_le` : |rsE1 a p| <= (9/50)/a for a >= 39.

    conjecture1_proved = False.  An explicit remainder inequality for the Riemann-Siegel formula at
    finite height; nothing here bears on the Riemann Hypothesis.
-/
import RS_B3

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. The second Gaussian moment -/

theorem integral_Ioi_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-b * v ^ 2) = Real.sqrt π * b ^ (-(3 / 2 : ℝ)) / 4 := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := b) (by norm_num)
    (by norm_num) hb
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [hG, show -((2 : ℝ) + 1) / 2 = -(3 / 2) by norm_num] at h
  simp only [Real.rpow_two] at h
  rw [h]
  ring

theorem integral_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ v : ℝ, v ^ 2 * Real.exp (-b * v ^ 2) = Real.sqrt (π / b) / (2 * b) := by
  have hint : Integrable (fun v : ℝ => v ^ 2 * Real.exp (-b * v ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
    simpa only [Real.rpow_two] using this
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  have hneg : ∫ v in Iic (0 : ℝ), v ^ 2 * Real.exp (-b * v ^ 2) =
      ∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-b * v ^ 2) := by
    have := integral_comp_neg_Ioi (c := 0) (f := fun v : ℝ => v ^ 2 * Real.exp (-b * v ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  rw [hneg, integral_Ioi_sq_mul_exp_neg_mul_sq hb]
  have hb32 : b ^ (-(3 / 2 : ℝ)) = 1 / (b * Real.sqrt b) := by
    rw [Real.rpow_neg hb.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hb, Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring
  rw [hb32, Real.sqrt_div' π hb.le]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp
  ring

/-! ## 2. Lower bound for the denominator -/

theorem norm_rsD_ge_two_pi_im (z : ℂ) : 2 * π * |z.im| ≤ ‖rsD z‖ := by
  have h1 := norm_rsD_ge z
  have h2 := le_exp_sub_exp (ρ := 2 * π * |z.im|) (by positivity)
  rw [show 2 * π * |z.im| / 2 = π * |z.im| by ring] at h2
  linarith

/-! ## 3. The amplitude near the saddle point -/

theorem logTaylor_three (u : ℂ) : logTaylor 3 u = u - u ^ 2 / 2 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring

theorem rsPhi_eq_exp {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 + w / a ≠ 0) :
    rsPhi a w = cexp (-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + w / a) - logTaylor 3 (w / a)) -
      1 / 2 * Complex.log (1 + w / a)) := by
  unfold rsPhi
  rw [Complex.cpow_def_of_ne_zero hw, ← Complex.exp_add, logTaylor_three]
  congr 1
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  field_simp
  ring

theorem norm_rsPhi_sub_one_le {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : ‖w‖ ≤ a / 2) :
    ‖rsPhi a w - 1‖ ≤ (‖w‖ / (2 * a) + ‖w‖ ^ 2 / (2 * a ^ 2) + 4 * π / 3 * ‖w‖ ^ 3 / a) *
      Real.exp (‖w‖ / (2 * a) + ‖w‖ ^ 2 / (2 * a ^ 2) + 4 * π / 3 * ‖w‖ ^ 3 / a) := by
  set u : ℂ := w / a with hu
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hnu : ‖u‖ = ‖w‖ / a := by rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hu2 : ‖u‖ ≤ 1 / 2 := by rw [hnu, div_le_iff₀ ha]; linarith
  have hu1 : ‖u‖ < 1 := by linarith
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : u = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hu1; linarith
  set ε : ℂ := -(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 3 u) -
    1 / 2 * Complex.log (1 + u) with hε
  have hT := Complex.norm_log_sub_logTaylor_le 2 hu1
  have hL := Complex.norm_log_one_add_le hu1
  have hεb : ‖ε‖ ≤ ‖w‖ / (2 * a) + ‖w‖ ^ 2 / (2 * a ^ 2) + 4 * π / 3 * ‖w‖ ^ 3 / a := by
    have hnu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have e1 : ‖-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 3 u)‖ ≤
        2 * π * a ^ 2 * (‖u‖ ^ 3 * 2 / 3) := by
      rw [norm_mul, norm_neg]
      have hn : ‖(2 * ↑π * a ^ 2 * I : ℂ)‖ = 2 * π * a ^ 2 := by
        rw [norm_mul, Complex.norm_I, mul_one,
          show (2 * (π : ℂ) * (a : ℂ) ^ 2 : ℂ) = ((2 * π * a ^ 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hn]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc ‖Complex.log (1 + u) - logTaylor 3 u‖ ≤ ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / (2 + 1) := by
            exact_mod_cast hT
        _ ≤ ‖u‖ ^ 3 * 2 / 3 := by
            have : ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ ≤ ‖u‖ ^ 3 * 2 :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
            norm_num at this ⊢
            linarith
    have e2 : ‖(1 / 2 : ℂ) * Complex.log (1 + u)‖ ≤ 1 / 2 * (‖u‖ ^ 2 + ‖u‖) := by
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have : ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 ≤ ‖u‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖u‖)
        linarith
      linarith
    calc ‖ε‖ ≤ ‖-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 3 u)‖ +
          ‖(1 / 2 : ℂ) * Complex.log (1 + u)‖ := norm_sub_le _ _
      _ ≤ 2 * π * a ^ 2 * (‖u‖ ^ 3 * 2 / 3) + 1 / 2 * (‖u‖ ^ 2 + ‖u‖) := add_le_add e1 e2
      _ = ‖w‖ / (2 * a) + ‖w‖ ^ 2 / (2 * a ^ 2) + 4 * π / 3 * ‖w‖ ^ 3 / a := by
          rw [hnu]; field_simp; ring
  rw [rsPhi_eq_exp ha h1u, ← hε]
  have hexp := Complex.norm_exp_sub_sum_le_norm_mul_exp ε 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one] at hexp
  calc ‖cexp ε - 1‖ ≤ ‖ε‖ * Real.exp ‖ε‖ := hexp
    _ ≤ _ := mul_le_mul hεb (Real.exp_le_exp.mpr hεb) (Real.exp_pos _).le (by positivity)

/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/

theorem saddle_X_mem {a : ℝ} (ha : 0 < a) (v : ℝ) : (1 : ℂ) + v * (1 + I) / a ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne v 0 with rfl | hv
  · left; simp
  · right; simp [Complex.div_im, hv, ha.ne']

theorem saddle_hasDerivAt {a : ℝ} (ha : 0 < a) (v : ℝ) :
    HasDerivAt (fun v : ℝ => 2 * π * a ^ 2 * (Complex.log (1 + v * (1 + I) / a)).im -
      2 * π * (a + v) * v + π * v ^ 2)
      (-(2 * π * v * (3 * a ^ 2 + 4 * a * v + 2 * v ^ 2) / ((a + v) ^ 2 + v ^ 2))) v := by
  have hX : HasDerivAt (fun v : ℝ => (1 : ℂ) + v * (1 + I) / a) ((1 + I) / a) v := by
    have := ((hasDerivAt_id (v : ℂ)).mul_const ((1 + I) / (a : ℂ))).const_add (1 : ℂ)
    have h2 := this.comp_ofReal (z := v)
    convert h2 using 1
    · ext y; simp; ring
    · simp
  have hlog := (Complex.hasDerivAt_log (saddle_X_mem ha v)).comp v hX
  have him := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt v hlog
  have hpoly : HasDerivAt (fun v : ℝ => -(2 * π * (a + v) * v) + π * v ^ 2)
      (-(2 * π * (a + 2 * v)) + 2 * π * v) v := by
    have h1 : HasDerivAt (fun v : ℝ => 2 * π * (a + v) * v) (2 * π * (a + 2 * v)) v := by
      have := (((hasDerivAt_id' v).const_add a).const_mul (2 * π)).mul (hasDerivAt_id' v)
      convert this using 1 <;> first | rfl | ring
    have h2 : HasDerivAt (fun v : ℝ => π * v ^ 2) (2 * π * v) v := by
      have := (hasDerivAt_pow 2 v).const_mul π
      convert this using 1 <;> first | rfl | (norm_num <;> ring)
    exact h1.neg.add h2
  have htot := (him.const_mul (2 * π * a ^ 2)).add hpoly
  refine htot.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · -- the derivative value
    have hden : (a + v) ^ 2 + v ^ 2 ≠ 0 := by
      have : 0 < (a + v) ^ 2 + v ^ 2 := by
        rcases eq_or_ne v 0 with rfl | hv
        · simp; positivity
        · have := sq_pos_of_ne_zero hv; positivity
      exact this.ne'
    simp only [Complex.imCLM_apply]
    have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
    have hXv : (1 : ℂ) + v * (1 + I) / a = ((a + v) + v * I) / a := by
      field_simp; ring
    rw [hXv]
    have hz : ((a : ℂ) + v) + v * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
      have h2 := congrArg Complex.im h; simp at h2
      rw [h2] at this; linarith
    rw [show (((a : ℂ) + v + v * I) / a)⁻¹ * ((1 + I) / a) = (1 + I) / ((a : ℂ) + v + v * I) by
      field_simp]
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
    ring
  · exact Eventually.of_forall fun y => by simp; ring

/-- **The saddle point is a global maximum.**  For `a > 0` and every real `v`:
    `2 pi a^2 arg(1 + v(1+i)/a) - 2 pi (a + v) v <= -pi v^2`. -/
theorem saddle_arg_le {a : ℝ} (ha : 0 < a) (v : ℝ) :
    2 * π * a ^ 2 * Complex.arg (1 + v * (1 + I) / a) - 2 * π * (a + v) * v ≤ -(π * v ^ 2) := by
  set h : ℝ → ℝ := fun v => 2 * π * a ^ 2 * (Complex.log (1 + v * (1 + I) / a)).im -
    2 * π * (a + v) * v + π * v ^ 2 with hh
  have hderiv := saddle_hasDerivAt ha
  have hcont : Continuous h := continuous_iff_continuousAt.mpr fun v => (hderiv v).continuousAt
  have hdiff : Differentiable ℝ h := fun v => (hderiv v).differentiableAt
  have h0 : h 0 = 0 := by simp [hh]
  have hpos : ∀ v, 0 < 3 * a ^ 2 + 4 * a * v + 2 * v ^ 2 := by
    intro v; nlinarith [sq_nonneg (v + a), sq_nonneg a, ha]
  have hden : ∀ v : ℝ, 0 < (a + v) ^ 2 + v ^ 2 := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp; positivity
    · have := sq_pos_of_ne_zero hv; positivity
  have hle : h v ≤ 0 := by
    rcases le_total 0 v with hv | hv
    · have hanti : AntitoneOn h (Ici 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn
          hdiff.differentiableOn (fun x hx => ?_)
        rw [interior_Ici] at hx
        rw [(hderiv x).deriv]
        have hx' : 0 < x := hx
        have := hpos x; have := hden x
        rw [neg_nonpos]; positivity
      have := hanti (self_mem_Ici) hv hv
      rw [h0] at this; exact this
    · have hmono : MonotoneOn h (Iic 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont.continuousOn
          hdiff.differentiableOn (fun x hx => ?_)
        rw [interior_Iic] at hx
        rw [(hderiv x).deriv]
        have hx' : x < 0 := hx
        have h1 := hpos x; have h2 := hden x
        rw [le_neg, neg_zero, div_nonpos_iff]
        right
        refine ⟨?_, h2.le⟩
        have hx0 : 0 < -x := by linarith
        have hq : 0 < 2 * π * (-x) * (3 * a ^ 2 + 4 * a * x + 2 * x ^ 2) :=
          mul_pos (mul_pos (by positivity) hx0) h1
        linarith
      have := hmono hv (self_mem_Iic) hv
      rw [h0] at this; exact this
  simp only [hh, Complex.log_im] at hle
  linarith

theorem norm_gauss_rsPhi_le {a : ℝ} (ha : 0 < a) (v : ℝ) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) * rsPhi a ((v : ℂ) * (1 + I))‖ ≤
      2 * Real.exp (-(π * v ^ 2)) := by
  set w : ℂ := (v : ℂ) * (1 + I) with hw
  set X : ℂ := 1 + w / a with hX
  have hXs : X ∈ slitPlane := by
    have := saddle_X_mem ha v
    rw [hX, hw]; simpa [mul_div_assoc] using this
  have hX0 : X ≠ 0 := slitPlane_ne_zero hXs
  have hXnorm : 1 / 4 ≤ ‖X‖ := by
    have h1 := Complex.abs_re_le_norm X
    have h2 := Complex.abs_im_le_norm X
    have hre : X.re = 1 + v / a := by rw [hX, hw]; simp [Complex.div_re]; field_simp
    have him : X.im = v / a := by rw [hX, hw]; simp [Complex.div_im]; field_simp
    rw [hre] at h1; rw [him] at h2
    rcases le_total (v / a) (-(1 / 2)) with h | h
    · have : 1 / 2 ≤ |v / a| := by rw [abs_of_neg (by linarith)]; linarith
      linarith
    · have : 1 / 2 ≤ |1 + v / a| := by rw [abs_of_nonneg (by linarith)]; linarith
      linarith
  unfold rsPhi
  rw [← hX, ← mul_assoc, ← Complex.exp_add, norm_mul, Complex.norm_exp,
    Complex.norm_cpow_of_ne_zero hX0]
  have hre : (2 * (π : ℂ) * I * w ^ 2 + (2 * (π : ℂ) * I * a * w - (π : ℂ) * I * w ^ 2)).re =
      -(2 * π * (a + v) * v) := by
    rw [hw]; simp [pow_two, mul_re, mul_im]; ring
  have hsre : (-((1 / 2 : ℂ) + 2 * (π : ℂ) * a ^ 2 * I)).re = -(1 / 2) := by simp [pow_two]
  have hsim : (-((1 / 2 : ℂ) + 2 * (π : ℂ) * a ^ 2 * I)).im = -(2 * π * a ^ 2) := by
    simp [pow_two]
  rw [hre, hsre, hsim]
  have hargb := saddle_arg_le ha v
  have hXeq : (1 : ℂ) + (v : ℂ) * (1 + I) / a = X := by rw [hX, hw]
  rw [hXeq] at hargb
  have hpow : ‖X‖ ^ (-(1 / 2 : ℝ)) ≤ 2 := by
    calc ‖X‖ ^ (-(1 / 2 : ℝ)) ≤ (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hXnorm (by norm_num)
      _ = 2 := by
          rw [Real.rpow_neg (by norm_num), show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
  have hexp : Real.exp (-(2 * π * (a + v) * v)) / Real.exp (X.arg * -(2 * π * a ^ 2)) =
      Real.exp (2 * π * a ^ 2 * X.arg - 2 * π * (a + v) * v) := by
    rw [← Real.exp_sub]; congr 1; ring
  calc Real.exp (-(2 * π * (a + v) * v)) * (‖X‖ ^ (-(1 / 2 : ℝ)) /
        Real.exp (X.arg * -(2 * π * a ^ 2)))
      = ‖X‖ ^ (-(1 / 2 : ℝ)) * (Real.exp (-(2 * π * (a + v) * v)) /
          Real.exp (X.arg * -(2 * π * a ^ 2))) := by ring
    _ = ‖X‖ ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * a ^ 2 * X.arg - 2 * π * (a + v) * v) := by
          rw [hexp]
    _ ≤ 2 * Real.exp (-(π * v ^ 2)) :=
          mul_le_mul hpow (Real.exp_le_exp.mpr hargb) (Real.exp_pos _).le (by norm_num)

/-! ## 4b. Integrability of the second Gaussian moment -/

theorem integrable_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : ℝ => v ^ 2 * Real.exp (-b * v ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
  simpa only [Real.rpow_two] using this

/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/

theorem rsD_midline_re_im (v : ℝ) :
    (rsD ((1 / 2 : ℂ) + v * (1 + I))).re =
        (Real.exp (π * v) - Real.exp (-(π * v))) * Real.sin (π * v) ∧
      (rsD ((1 / 2 : ℂ) + v * (1 + I))).im =
        (Real.exp (π * v) + Real.exp (-(π * v))) * Real.cos (π * v) := by
  unfold rsD
  have h1 : (↑π * I * ((1 / 2 : ℂ) + v * (1 + I))) =
      ((-(π * v) : ℝ) : ℂ) + ((π * v + π / 2 : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (↑π * (v : ℂ)) * I_sq
  have h2 : -(↑π * I * ((1 / 2 : ℂ) + v * (1 + I))) =
      ((π * v : ℝ) : ℂ) + ((-(π * v + π / 2) : ℝ) : ℂ) * I := by
    rw [h1]; push_cast; ring
  rw [h2, h1]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_re, Complex.exp_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  rw [Real.cos_neg, Real.sin_neg, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  constructor <;> ring

/-- On the midline `Re x - Im x = 1/2`, `|e^{i pi x} - e^{-i pi x}| >= 2`. -/
theorem two_le_norm_rsD_midline (v : ℝ) : 2 ≤ ‖rsD ((1 / 2 : ℂ) + v * (1 + I))‖ := by
  obtain ⟨hre, him⟩ := rsD_midline_re_im v
  set z := rsD ((1 / 2 : ℂ) + v * (1 + I))
  set E := Real.exp (π * v)
  set F := Real.exp (-(π * v))
  set s := Real.sin (π * v)
  set c := Real.cos (π * v)
  have hEF : E * F = 1 := by rw [← Real.exp_add]; simp
  have hsinh : (π * v) ^ 2 ≤ Real.sinh (π * v) ^ 2 :=
    sq_le_sq.mpr (by rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have hsin : s ^ 2 ≤ (π * v) ^ 2 := Real.sin_sq_le_sq
  have hsh : Real.sinh (π * v) = (E - F) / 2 := Real.sinh_eq _
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have key : 4 * s ^ 2 ≤ (E - F) ^ 2 := by
    rw [hsh, show ((E - F) / 2) ^ 2 = (E - F) ^ 2 / 4 by ring] at hsinh
    linarith
  have hsq : 4 ≤ ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have e1 : (E - F) * s * ((E - F) * s) + (E + F) * c * ((E + F) * c) =
        (E - F) ^ 2 * (s ^ 2 + c ^ 2) + 4 * (E * F) * c ^ 2 := by ring
    rw [e1, hsc, hEF]
    nlinarith
  nlinarith [norm_nonneg z]

theorem rsJ_line_eq {p : ℝ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (h₁ : -p < c₁) (h₂ : c₂ < 1 - p) (hc1 : -1 ≤ c₁) (hc2 : c₂ ≤ 1) :
    lineUp c₁ (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) =
      lineUp c₂ (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) := by
  have hD : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → rsD (p + x) ≠ 0 := by
    intro x hx
    refine rsD_ne_zero_of_ne fun n hn => ?_
    have him : x.im = 0 := by simpa using congrArg Complex.im hn
    have hre : p + x.re = n := by simpa using congrArg Complex.re hn
    rw [him, sub_zero] at hx
    have h1 : (0 : ℝ) < n := by linarith [hx.1]
    have h2 : (n : ℝ) < 1 := by linarith [hx.2]
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hdA : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ →
      DifferentiableAt ℂ (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) x := by
    intro x hx
    exact ((by fun_prop : Differentiable ℂ (fun w : ℂ => cexp (2 * ↑π * I * w ^ 2))) x).div
      ((differentiable_rsD.comp (by fun_prop : Differentiable ℂ (fun w : ℂ => (p : ℂ) + w))) x)
      (hD x hx)
  refine lineUp_eq_of_strip' hc (fun x hx => (hdA x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hdA x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt) (C := 1) (a := 4 * π)
    (b := 4 * π) (by positivity) (fun x hx h1 => ?_)
  have hD1 : 1 ≤ ‖rsD (p + x)‖ := one_le_norm_rsD (by simpa using h1)
  rw [norm_div, Complex.norm_exp]
  have hre : (2 * (π : ℂ) * I * x ^ 2).re = -(4 * π * x.re * x.im) := by
    simp [pow_two, mul_re, mul_im]; ring
  rw [hre, one_mul]
  refine (div_le_self (Real.exp_pos _).le hD1).trans (Real.exp_le_exp.mpr ?_)
  have hd : |x.re - x.im| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hbd : -((x.re - x.im) * x.im) ≤ |x.im| := by
    calc -((x.re - x.im) * x.im) ≤ |(x.re - x.im) * x.im| := neg_le_abs _
      _ = |x.re - x.im| * |x.im| := abs_mul _ _
      _ ≤ 1 * |x.im| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = |x.im| := one_mul _
  have key : -(4 * π * x.re * x.im) =
      -(4 * π) * x.im ^ 2 + 4 * π * (-((x.re - x.im) * x.im)) := by ring
  rw [key]
  have := mul_le_mul_of_nonneg_left hbd (by positivity : (0 : ℝ) ≤ 4 * π)
  linarith

/-- The tau = 2 Mordell integral may be computed on the midline through `1/2 - p`. -/
theorem rsJ_eq_mid {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = lineUp (1 / 2 - p) (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) := by
  unfold rsJ
  rcases le_total p (1 / 2) with h | h
  · exact rsJ_line_eq (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · exact (rsJ_line_eq (c₁ := 1 / 2 - p) (c₂ := 0) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)).symm

/-- **`|rsJ p| <= 4` uniformly in `p ∈ (0, 1)`.** -/
theorem norm_rsJ_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : ‖rsJ p‖ ≤ 4 := by
  rw [rsJ_eq_mid hp hp1]
  unfold lineUp
  set c : ℝ := 1 / 2 - p with hc
  have hcb : c ^ 2 ≤ 1 / 4 := by
    have h1 : -(1 / 2) < c := by linarith
    have h2 : c < 1 / 2 := by linarith
    nlinarith
  have hbound : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((c : ℂ) + v * (1 + I)) ^ 2) /
      rsD (p + ((c : ℂ) + v * (1 + I))) * (1 + I)‖ ≤
      Real.sqrt 2 / 2 * Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) := by
    intro v
    have hpt : (p : ℂ) + ((c : ℂ) + v * (1 + I)) = (1 / 2 : ℂ) + v * (1 + I) := by
      rw [hc]; push_cast; ring
    rw [hpt, norm_mul, norm_div, norm_one_add_I, Complex.norm_exp]
    have hre : (2 * (π : ℂ) * I * ((c : ℂ) + v * (1 + I)) ^ 2).re = -(4 * π * (c + v) * v) := by
      simp [pow_two, mul_re, mul_im]; ring
    rw [hre]
    have hD := two_le_norm_rsD_midline v
    have hexp : Real.exp (-(4 * π * (c + v) * v)) ≤ Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ 2 * π * (c + v) ^ 2 := by positivity
      have hpi : π ≤ 4 := by linarith [Real.pi_lt_d2]
      have h3 : 2 * π * c ^ 2 ≤ 2 := by nlinarith [Real.pi_pos]
      nlinarith
    calc Real.exp (-(4 * π * (c + v) * v)) / ‖rsD ((1 / 2 : ℂ) + v * (1 + I))‖ * Real.sqrt 2
        ≤ Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) / 2 * Real.sqrt 2 := by
          gcongr
      _ = Real.sqrt 2 / 2 * Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) := by ring
  have hint : Integrable (fun v : ℝ => Real.sqrt 2 / 2 * Real.exp 2 * Real.exp (-(2 * π) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall fun v => ?_)) ?_
  · exact hbound v
  · rw [integral_const_mul, integral_gaussian]
    have h1 : Real.sqrt (π / (2 * π)) = Real.sqrt (1 / 2) := by
      congr 1; field_simp
    have h2 : Real.sqrt 2 * Real.sqrt (1 / 2) = 1 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he1 := Real.exp_one_lt_d9
    have he0 := Real.exp_pos 1
    rw [h1]
    calc Real.sqrt 2 / 2 * Real.exp 2 * Real.sqrt (1 / 2)
        = Real.exp 2 / 2 * (Real.sqrt 2 * Real.sqrt (1 / 2)) := by ring
      _ ≤ 4 := by rw [h2, he]; nlinarith

/-! ## 6. The error integral `rsE1` is `O(1/a)` -/

theorem norm_w_eq (v : ℝ) : ‖(v : ℂ) * (1 + I)‖ = Real.sqrt 2 * |v| := by
  rw [norm_mul, Complex.norm_real, norm_one_add_I, Real.norm_eq_abs, mul_comm]

theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem rsPhi_zero (a : ℝ) : rsPhi a 0 = 1 := by
  simp [rsPhi]

theorem norm_exp_gauss_diag (v : ℝ) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) := by
  rw [Complex.norm_exp]; congr 1; simp [pow_two, mul_re, mul_im]; ring

/-- Pointwise bound near the saddle point (`|v| <= a/9`). -/
theorem norm_E1_integrand_near {a p v : ℝ} (ha : 39 ≤ a) (hv : |v| ≤ a / 9) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      Real.exp (1 / 10000) / (π * a) * (51 / 100 + 17 / 2 * v ^ 2) * Real.exp (-10 * v ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hRHS : 0 ≤ Real.exp (1 / 10000) / (π * a) * (51 / 100 + 17 / 2 * v ^ 2) *
      Real.exp (-10 * v ^ 2) := by positivity
  rcases eq_or_ne v 0 with rfl | hv0
  · have h0 : rsPhi a ((0 : ℝ) * (1 + I) : ℂ) = 1 := by simp [rsPhi]
    rw [h0, sub_self, mul_zero, zero_mul, norm_zero]
    exact hRHS
  set w : ℂ := (v : ℂ) * (1 + I) with hwdef
  set n : ℝ := ‖w‖ with hn
  have hnv : n = Real.sqrt 2 * |v| := norm_w_eq v
  have hn2 : n ^ 2 = 2 * v ^ 2 := by
    rw [hnv, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
  have hn0 : 0 ≤ n := norm_nonneg _
  have hna : n ≤ a / 6 := by
    rw [hnv]
    calc Real.sqrt 2 * |v| ≤ 3 / 2 * (a / 9) :=
          mul_le_mul sqrt_two_le_three_halves hv (abs_nonneg _) (by norm_num)
      _ = a / 6 := by ring
  have hphi := norm_rsPhi_sub_one_le ha0 (show ‖w‖ ≤ a / 2 by rw [← hn]; linarith)
  rw [← hn] at hphi
  set ε := n / (2 * a) + n ^ 2 / (2 * a ^ 2) + 4 * π / 3 * n ^ 3 / a with hε
  have hε1 : ε ≤ n * ((51 / 100 + 17 / 2 * v ^ 2) / a) := by
    have hv2 : 17 / 2 * v ^ 2 = 17 / 4 * n ^ 2 := by rw [hn2]; ring
    rw [hv2]
    have e : n * ((51 / 100 + 17 / 4 * n ^ 2) / a) - ε =
        n / a * (1 / 100 + (17 / 4 - 4 * π / 3) * n ^ 2 - n / (2 * a)) := by
      rw [hε]; field_simp; ring
    have h1 : n / (2 * a) ≤ n / 78 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) (by linarith)
    have h2 : (1 / 20 : ℝ) ≤ 17 / 4 - 4 * π / 3 := by linarith [Real.pi_lt_d2]
    have h3 : 0 ≤ 1 / 100 + 1 / 20 * n ^ 2 - n / 78 := by nlinarith [sq_nonneg (n - 10 / 78)]
    have h4 : 1 / 20 * n ^ 2 ≤ (17 / 4 - 4 * π / 3) * n ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg n)
    have h5 : 0 ≤ n / a * (1 / 100 + (17 / 4 - 4 * π / 3) * n ^ 2 - n / (2 * a)) :=
      mul_nonneg (div_nonneg hn0 ha0.le) (by linarith)
    linarith
  have hε2 : ε ≤ 5 / 2 * v ^ 2 + 1 / 10000 := by
    have h1 : n / (2 * a) ≤ n / 78 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) (by linarith)
    have e1 : n / (2 * a) ≤ n ^ 2 / 2 + 1 / 12168 := by nlinarith [sq_nonneg (n - 1 / 78)]
    have e2 : n ^ 2 / (2 * a ^ 2) ≤ n ^ 2 / 3042 :=
      div_le_div_of_nonneg_left (sq_nonneg n) (by norm_num) (by nlinarith)
    have e3 : 4 * π / 3 * n ^ 3 / a ≤ 4 * π / 3 * n ^ 2 / 6 := by
      have h : n ^ 3 / a ≤ n ^ 2 / 6 := by
        rw [div_le_div_iff₀ ha0 (by norm_num)]
        have e : n ^ 3 * 6 = n ^ 2 * (6 * n) := by ring
        rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg n)
      calc 4 * π / 3 * n ^ 3 / a = 4 * π / 3 * (n ^ 3 / a) := by ring
        _ ≤ 4 * π / 3 * (n ^ 2 / 6) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 4 * π / 3 * n ^ 2 / 6 := by ring
    have e4 : 4 * π / 3 * n ^ 2 / 6 ≤ 7 / 10 * n ^ 2 := by
      nlinarith [sq_nonneg n, Real.pi_lt_d2]
    rw [hε]
    linarith [sq_nonneg v]
  have hexpw : ‖cexp (2 * ↑π * I * w ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) := norm_exp_gauss_diag v
  have him : ((p : ℂ) + w).im = v := by simp [hwdef]
  have hD : 2 * π * |v| ≤ ‖rsD (p + w)‖ := by
    have := norm_rsD_ge_two_pi_im (p + w); rwa [him] at this
  have hvpos : 0 < |v| := abs_pos.mpr hv0
  have hDpos : 0 < 2 * π * |v| := by positivity
  have hΦ : ‖rsPhi a w - 1‖ ≤
      n * ((51 / 100 + 17 / 2 * v ^ 2) / a) * Real.exp (5 / 2 * v ^ 2 + 1 / 10000) :=
    hphi.trans (mul_le_mul hε1 (Real.exp_le_exp.mpr hε2) (Real.exp_pos _).le (by positivity))
  have hexp2 : Real.exp (-(4 * π) * v ^ 2) * Real.exp (5 / 2 * v ^ 2 + 1 / 10000) =
      Real.exp (1 / 10000) * Real.exp (-(4 * π - 5 / 2) * v ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc ‖cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * (rsPhi a w - 1) * (1 + I)‖
      = Real.exp (-(4 * π) * v ^ 2) * ‖rsPhi a w - 1‖ * Real.sqrt 2 / ‖rsD (p + w)‖ := by
        rw [norm_mul, norm_mul, norm_div, hexpw, norm_one_add_I]; ring
    _ ≤ Real.exp (-(4 * π) * v ^ 2) * (n * ((51 / 100 + 17 / 2 * v ^ 2) / a) *
          Real.exp (5 / 2 * v ^ 2 + 1 / 10000)) * Real.sqrt 2 / (2 * π * |v|) := by
        gcongr
    _ = (Real.exp (-(4 * π) * v ^ 2) * Real.exp (5 / 2 * v ^ 2 + 1 / 10000)) *
          (Real.sqrt 2 * Real.sqrt 2) * (51 / 100 + 17 / 2 * v ^ 2) / (2 * π * a) *
          (|v| / |v|) := by
        rw [hnv]; field_simp
    _ = Real.exp (1 / 10000) / (π * a) * (51 / 100 + 17 / 2 * v ^ 2) *
          Real.exp (-(4 * π - 5 / 2) * v ^ 2) := by
        rw [hexp2, hss, div_self hvpos.ne']; field_simp
    _ ≤ Real.exp (1 / 10000) / (π * a) * (51 / 100 + 17 / 2 * v ^ 2) * Real.exp (-10 * v ^ 2) := by
        gcongr
        nlinarith [Real.pi_gt_d2, sq_nonneg v]

/-- Pointwise bound away from the saddle point (`|v| >= a/9`). -/
theorem norm_E1_integrand_far {a p v : ℝ} (ha : 39 ≤ a) (hv : a / 9 ≤ |v|) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      5 * Real.exp (-(π * a ^ 2 / 162)) * Real.exp (-(π / 2) * v ^ 2) := by
  have ha0 : 0 < a := by linarith
  set w : ℂ := (v : ℂ) * (1 + I) with hwdef
  have him : ((p : ℂ) + w).im = v := by simp [hwdef]
  have hv1 : 1 ≤ |v| := by linarith
  have hD : 1 ≤ ‖rsD (p + w)‖ := one_le_norm_rsD (by rw [him]; exact hv1)
  have hexpw : ‖cexp (2 * ↑π * I * w ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) := norm_exp_gauss_diag v
  have hG := norm_gauss_rsPhi_le ha0 v
  have hnum : ‖cexp (2 * ↑π * I * w ^ 2) * (rsPhi a w - 1)‖ ≤ 3 * Real.exp (-(π * v ^ 2)) := by
    rw [mul_sub, mul_one]
    have h4 : Real.exp (-(4 * π) * v ^ 2) ≤ Real.exp (-(π * v ^ 2)) := by
      apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, sq_nonneg v]
    calc _ ≤ ‖cexp (2 * ↑π * I * w ^ 2) * rsPhi a w‖ + ‖cexp (2 * ↑π * I * w ^ 2)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * Real.exp (-(π * v ^ 2)) + Real.exp (-(π * v ^ 2)) := by
          rw [hexpw]; exact add_le_add hG h4
      _ = 3 * Real.exp (-(π * v ^ 2)) := by ring
  have hsplit : Real.exp (-(π * v ^ 2)) ≤
      Real.exp (-(π * a ^ 2 / 162)) * Real.exp (-(π / 2) * v ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have : (a / 9) ^ 2 ≤ v ^ 2 := by
      rw [← sq_abs v]; exact pow_le_pow_left₀ (by positivity) hv 2
    nlinarith [Real.pi_pos]
  calc ‖cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * (rsPhi a w - 1) * (1 + I)‖
      = ‖cexp (2 * ↑π * I * w ^ 2) * (rsPhi a w - 1)‖ * Real.sqrt 2 / ‖rsD (p + w)‖ := by
        simp only [norm_mul, norm_div]; rw [norm_one_add_I]; ring
    _ ≤ 3 * Real.exp (-(π * v ^ 2)) * (3 / 2) / 1 := by
        gcongr
        exact sqrt_two_le_three_halves
    _ ≤ 5 * Real.exp (-(π * a ^ 2 / 162)) * Real.exp (-(π / 2) * v ^ 2) := by
        have := Real.exp_pos (-(π * v ^ 2))
        rw [div_one]; nlinarith

/-- **The error integral.** -/
theorem norm_rsE1_le {a p : ℝ} (ha : 39 ≤ a) :
    ‖rsE1 a p‖ ≤ Real.exp (1 / 10000) / (π * a) * (51 / 100) * Real.sqrt (π / 10) +
      Real.exp (1 / 10000) / (π * a) * (17 / 2) * (Real.sqrt (π / 10) / (2 * 10)) +
      5 * Real.exp (-(π * a ^ 2 / 162)) * Real.sqrt (π / (π / 2)) := by
  have ha0 : 0 < a := by linarith
  set K₁ := Real.exp (1 / 10000) / (π * a) with hK₁
  set K₂ := 5 * Real.exp (-(π * a ^ 2 / 162)) with hK₂
  have hi1 : Integrable (fun v : ℝ => Real.exp (-10 * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hi2 : Integrable (fun v : ℝ => v ^ 2 * Real.exp (-10 * v ^ 2)) :=
    integrable_sq_mul_exp_neg_mul_sq (by norm_num)
  have hi3 : Integrable (fun v : ℝ => Real.exp (-(π / 2) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hint : Integrable (fun v : ℝ => K₁ * (51 / 100) * Real.exp (-10 * v ^ 2) +
      K₁ * (17 / 2) * (v ^ 2 * Real.exp (-10 * v ^ 2)) + K₂ * Real.exp (-(π / 2) * v ^ 2)) :=
    ((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hpt : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) /
      rsD (p + (v : ℂ) * (1 + I)) * (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      K₁ * (51 / 100) * Real.exp (-10 * v ^ 2) +
        K₁ * (17 / 2) * (v ^ 2 * Real.exp (-10 * v ^ 2)) + K₂ * Real.exp (-(π / 2) * v ^ 2) := by
    intro v
    have h1 : 0 ≤ K₁ * (51 / 100) * Real.exp (-10 * v ^ 2) +
        K₁ * (17 / 2) * (v ^ 2 * Real.exp (-10 * v ^ 2)) := by positivity
    have h2 : 0 ≤ K₂ * Real.exp (-(π / 2) * v ^ 2) := by positivity
    rcases le_total |v| (a / 9) with hv | hv
    · have := norm_E1_integrand_near (p := p) ha hv
      have e : K₁ * (51 / 100 + 17 / 2 * v ^ 2) * Real.exp (-10 * v ^ 2) =
          K₁ * (51 / 100) * Real.exp (-10 * v ^ 2) +
            K₁ * (17 / 2) * (v ^ 2 * Real.exp (-10 * v ^ 2)) := by ring
      rw [← hK₁, e] at this
      linarith
    · have := norm_E1_integrand_far (p := p) ha hv
      rw [← hK₂] at this
      linarith
  have hA : Integrable (fun v : ℝ => K₁ * (51 / 100) * Real.exp (-10 * v ^ 2) +
      K₁ * (17 / 2) * (v ^ 2 * Real.exp (-10 * v ^ 2))) := (hi1.const_mul _).add (hi2.const_mul _)
  have hB1 : Integrable (fun v : ℝ => K₁ * (51 / 100) * Real.exp (-10 * v ^ 2)) := hi1.const_mul _
  have hB2 : Integrable (fun v : ℝ => K₁ * (17 / 2) * (v ^ 2 * Real.exp (-10 * v ^ 2))) :=
    hi2.const_mul _
  have hB3 : Integrable (fun v : ℝ => K₂ * Real.exp (-(π / 2) * v ^ 2)) := hi3.const_mul _
  unfold rsE1 lineUp
  simp only [ofReal_zero, zero_add]
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)) (le_of_eq ?_)
  rw [integral_add hA hB3, integral_add hB1 hB2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gaussian, integral_sq_mul_exp_neg_mul_sq (by norm_num),
    integral_gaussian]

/-- Numerics: for `a >= 39` the right side of `norm_rsE1_le` is at most `(9/50)/a`. -/
theorem E1_const_le {a : ℝ} (ha : 39 ≤ a) :
    Real.exp (1 / 10000) / (π * a) * (51 / 100) * Real.sqrt (π / 10) +
      Real.exp (1 / 10000) / (π * a) * (17 / 2) * (Real.sqrt (π / 10) / (2 * 10)) +
      5 * Real.exp (-(π * a ^ 2 / 162)) * Real.sqrt (π / (π / 2)) ≤ 9 / 50 / a := by
  have ha0 : 0 < a := by linarith
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d6
  have he : Real.exp (1 / 10000) ≤ 10000 / 9999 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 10000) (by norm_num) (by norm_num)
    have e : (1 : ℝ) / (1 - 1 / 10000) = 10000 / 9999 := by norm_num
    linarith
  have hs : Real.sqrt (π / 10) ≤ 5606 / 10000 := by
    calc Real.sqrt (π / 10) ≤ Real.sqrt ((5606 / 10000) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 5606 / 10000 := Real.sqrt_sq (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (π / 10) := Real.sqrt_nonneg _
  have hT12 : Real.exp (1 / 10000) / (π * a) * (51 / 100) * Real.sqrt (π / 10) +
      Real.exp (1 / 10000) / (π * a) * (17 / 2) * (Real.sqrt (π / 10) / (2 * 10)) ≤
      17 / 100 / a := by
    have e : Real.exp (1 / 10000) / (π * a) * (51 / 100) * Real.sqrt (π / 10) +
        Real.exp (1 / 10000) / (π * a) * (17 / 2) * (Real.sqrt (π / 10) / (2 * 10)) =
        (Real.exp (1 / 10000) * Real.sqrt (π / 10) * (187 / 200) / π) / a := by
      field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ ha0.le
    rw [div_le_iff₀ Real.pi_pos]
    have := mul_le_mul he hs hs0 (by norm_num)
    nlinarith
  have hT3 : 5 * Real.exp (-(π * a ^ 2 / 162)) * Real.sqrt (π / (π / 2)) ≤ 1 / 100 / a := by
    set x := π * a ^ 2 / 162 with hx
    have ha2 : 1521 ≤ a ^ 2 := by nlinarith
    have hx29 : 29 ≤ x := by
      rw [hx, le_div_iff₀ (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_right hpi1.le (sq_nonneg a)]
    have hax : a ≤ 2 * x := by
      have h81 : 81 ≤ π * a := by nlinarith
      rw [hx]
      nlinarith
    have hexp : Real.exp (-x) ≤ 120 / x ^ 5 := by
      rw [Real.exp_neg]
      have h5 := Real.pow_div_factorial_le_exp x (by linarith) 5
      have hpos : 0 < x ^ 5 / (Nat.factorial 5) := by positivity
      calc (Real.exp x)⁻¹ ≤ (x ^ 5 / (Nat.factorial 5))⁻¹ := inv_anti₀ hpos h5
        _ = 120 / x ^ 5 := by norm_num [Nat.factorial]
    have hs2 : Real.sqrt (π / (π / 2)) = Real.sqrt 2 := by
      congr 1; field_simp
    rw [hs2, le_div_iff₀ ha0]
    have hx0 : 0 < x := by linarith
    calc 5 * Real.exp (-x) * Real.sqrt 2 * a ≤ 5 * (120 / x ^ 5) * (3 / 2) * (2 * x) := by
          gcongr
          exact sqrt_two_le_three_halves
      _ = 1800 / x ^ 4 := by field_simp; ring
      _ ≤ 1 / 100 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have : (29 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx29 4
          nlinarith
  calc _ ≤ 17 / 100 / a + 1 / 100 / a := add_le_add hT12 hT3
    _ = 9 / 50 / a := by ring

/-! ## 7. The explicit C0 remainder bound -/

theorem rsAlpha_ge_39 {t : ℝ} (ht : 10000 ≤ t) : 39 ≤ rsAlpha t := by
  unfold rsAlpha
  rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d2]

/-- **The C0-corrected Riemann-Siegel remainder, `a`-form.**  For `t >= 10000`, `0 < p = rsFrac t`,
    `cos(2 pi p) ≠ 0`, and any phase `phi` with `|phi - rsThetaMain t| <= 1/t`:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (2/5) a^(-3/2),   a = sqrt(t/2pi). -/
theorem rs_remainder_C0_alpha {t : ℝ} (ht : 10000 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      2 / 5 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  rw [rs_remainder_exact ht0 hp hcos φ]
  have ha39 : 39 ≤ rsAlpha t := rsAlpha_ge_39 ht
  have hta : t = 2 * π * rsAlpha t ^ 2 := t_eq_rsAlpha ht0.le
  set a := rsAlpha t with ha_def
  have ha0 : 0 < a := by linarith
  have hJ : ‖rsJ (rsFrac t)‖ ≤ 4 := norm_rsJ_le hp rsFrac_lt_one
  have hE : ‖rsE1 a (rsFrac t)‖ ≤ 9 / 50 / a := (norm_rsE1_le ha39).trans (E1_const_le ha39)
  have hA : |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
      rsJ (rsFrac t)).re| ≤ 2 * (|φ - rsThetaMain t| * 4) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (-(↑π / 8 * I))‖ = 1 := by rw [Complex.norm_exp]; simp
    have h2 : ‖cexp (I * (φ - rsThetaMain t)) - 1‖ ≤ |φ - rsThetaMain t| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ - rsThetaMain t)
      push_cast at this; rwa [Real.norm_eq_abs] at this
    rw [h1, one_mul]
    exact mul_le_mul h2 hJ (norm_nonneg _) (abs_nonneg _)
  have hB : |2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 a (rsFrac t)).re| ≤
      2 * (9 / 50 / a) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h1 : ‖cexp (I * (φ - rsThetaMain t - π / 8))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [h1, one_mul]; exact hE
  have hδ : |φ - rsThetaMain t| ≤ 1 / (2 * π * a ^ 2) := by rw [← hta]; exact hφ
  have h8 : 8 * |φ - rsThetaMain t| ≤ 1 / 25 / a := by
    have h1 : 8 * |φ - rsThetaMain t| ≤ 8 * (1 / (2 * π * a ^ 2)) := by linarith
    refine h1.trans ?_
    rw [show 8 * (1 / (2 * π * a ^ 2)) = 4 / (π * a ^ 2) by field_simp; ring,
      div_le_div_iff₀ (by positivity) ha0]
    have : 100 ≤ π * a := by nlinarith [Real.pi_gt_d2]
    nlinarith
  rw [abs_mul, abs_mul]
  have hsign : |(-1 : ℝ) ^ (rsNn t + 1)| = 1 := by simp
  rw [hsign, one_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  have hapos := Real.rpow_pos_of_pos ha0 (-(1 / 2 : ℝ))
  calc a ^ (-(1 / 2 : ℝ)) * |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
        rsJ (rsFrac t)).re + 2 * (cexp (I * (φ - rsThetaMain t - π / 8)) *
        rsE1 a (rsFrac t)).re|
      ≤ a ^ (-(1 / 2 : ℝ)) * (2 * (|φ - rsThetaMain t| * 4) + 2 * (9 / 50 / a)) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add hA hB)
    _ ≤ a ^ (-(1 / 2 : ℝ)) * (2 / 5 / a) := by
        gcongr
        have e : (2 : ℝ) / 5 / a = 1 / 25 / a + 2 * (9 / 50 / a) := by ring
        rw [e]; linarith
    _ = 2 / 5 * a ^ (-(3 / 2 : ℝ)) := by
        rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num, Real.rpow_add ha0, Real.rpow_neg_one]
        ring

theorem rsAlpha_rpow_neg_half {t : ℝ} (ht : 0 ≤ t) :
    (rsAlpha t) ^ (-(1 / 2 : ℝ)) = (t / (2 * π)) ^ (-(1 / 4 : ℝ)) := by
  unfold rsAlpha
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

theorem rsAlpha_rpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    (rsAlpha t) ^ (-(3 / 2 : ℝ)) = (2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ)) := by
  unfold rsAlpha
  have e : (1 / 2 : ℝ) * (-(3 / 2)) = -(3 / 4) := by norm_num
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), e, Real.div_rpow ht.le (by positivity),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * π), div_inv_eq_mul]
  ring

theorem two_pi_rpow_three_quarters_le : (2 * π) ^ (3 / 4 : ℝ) ≤ 4 := by
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hπ : 2 * π ≤ 63 / 10 := by linarith [Real.pi_lt_d2]
  have e : (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_natCast]
  calc (2 * π) ^ 3 ≤ (63 / 10) ^ 3 := pow_le_pow_left₀ (by positivity) hπ 3
    _ ≤ 4 ^ 4 := by norm_num

/-- **THE B3 HEADLINE: the explicit C0-corrected Riemann-Siegel remainder bound.**
    For `t >= 10000`, `0 < p = rsFrac t`, `cos(2 pi p) ≠ 0`, and any phase `phi` with
    `|phi - rsThetaMain t| <= 1/t`:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= 2 t^(-3/4). -/
theorem rs_remainder_C0 {t : ℝ} (ht : 10000 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      2 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := rs_remainder_C0_alpha ht hp hcos hφ
  rw [rsAlpha_rpow_neg_half ht0.le, rsAlpha_rpow_neg_three_halves ht0] at h
  have ht34 := Real.rpow_pos_of_pos ht0 (-(3 / 4 : ℝ))
  calc _ ≤ 2 / 5 * ((2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) := h
    _ ≤ 2 / 5 * (4 * t ^ (-(3 / 4 : ℝ))) := by gcongr; exact two_pi_rpow_three_quarters_le
    _ ≤ 2 * t ^ (-(3 / 4 : ℝ)) := by nlinarith

end RSInt

/-  KernelGammaEnvelope.lean -- ANDURIL G2 kernel discharge: a crude but RIGOROUS two-sided
    envelope for the magnitude of the Gamma_R factor on the critical line, and the EXPLICIT
    polar decomposition of `gLine` that consumes it.

    ## Why this file exists

    `ZeroSignDecomp_t14.gLine_sign_decomp_t` writes

        gLine t = M * (cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it)),   M > 0,

    but hides `M` behind an existential, because the sign route never needs its size.  A VALUE box
    for `gLine t` (the `memR` facts that `CheckBand.checkLine_correct` consumes) does need it: a box
    that excludes 0 carries a positive lower bound on `|gLine t|`, hence on `M`.  Nothing in the corpus
    bounds `|Gamma_R(1/2+it)|` (the `CheckBand` / `ZeroSignDecomp_t14` headers call it "the single
    precisely identified blocker").  This file supplies the missing piece in its cheapest honest form:

      * `norm_Gamma_le_Gamma_re` : `|Gamma(s)| <= Gamma(Re s)` for `Re s > 0` (Euler's integral and
        `norm_integral_le_integral_norm`).
      * `norm_sin_le_exp_abs_im` : `|sin z| <= exp |Im z|`.
      * `norm_Gamma_quarter_lower` : `(9/4) * exp(-pi |y|) <= |Gamma(1/4 + i y)|`, from the reflection
        formula `Gamma(s) Gamma(1-s) = pi / sin(pi s)` and the two upper bounds above.
      * `norm_Gamma_quarter_upper` : `|Gamma(1/4 + i y)| <= 4`.
      * `gLine_decomp_explicit` : the decomposition with `M = pi^(-1/4) * |Gamma(1/4 + i t/2)|` named.
      * `gammaRMag_bounds` : `(3/4) * exp(-pi |t| / 2) <= M <= 4`, `M = gammaRMag t`.

    The lower bound is loose (at t = 22 it undershoots the true `M = 3.2e-8` by a factor of about
    4e7), but it is a theorem, and it is all a sign-definite box needs: the reflected-band checker
    only reads signs.

    conjecture1_proved = False.  Elementary Gamma-function inequalities, not a proof of RH.
-/
import ZeroSignDecomp_t14
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Complex Real MeasureTheory XiLineZeros ThetaGap

namespace KernelGammaEnvelope

/-! ## 1.  `|Gamma(s)| <= Gamma(Re s)` -/

/-- **Euler-integral norm bound.**  For `0 < Re s`, `|Gamma(s)| <= Gamma(Re s)`: the norm of Euler's
    integral is at most the integral of the norm, and `|exp(-x) x^(s-1)| = exp(-x) x^(Re s - 1)`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp

/-- `Gamma(x) <= 1` on `[1, 2]` (convexity of `Gamma` with `Gamma 1 = Gamma 2 = 1`). -/
theorem Gamma_le_one_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have hc := Real.convexOn_Gamma
  have hseg : x ∈ segment ℝ (1 : ℝ) 2 := by
    rw [segment_eq_Icc (by norm_num)]; exact ⟨h1, h2⟩
  have h := hc.le_on_segment (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) hseg
  rwa [Real.Gamma_one, Real.Gamma_two, max_self] at h

/-- `Gamma(1/4) <= 4`  (`Gamma(5/4) = Gamma(1/4)/4` and `Gamma(5/4) <= 1`). -/
theorem Gamma_quarter_le : Real.Gamma (1 / 4) ≤ 4 := by
  have h := Real.Gamma_add_one (s := (1 / 4 : ℝ)) (by norm_num)
  have hle : Real.Gamma (1 / 4 + 1) ≤ 1 := Gamma_le_one_of_mem_Icc (by norm_num) (by norm_num)
  rw [h] at hle
  linarith

/-- `Gamma(3/4) <= 4/3`  (`Gamma(7/4) = (3/4) Gamma(3/4)` and `Gamma(7/4) <= 1`). -/
theorem Gamma_three_quarter_le : Real.Gamma (3 / 4) ≤ 4 / 3 := by
  have h := Real.Gamma_add_one (s := (3 / 4 : ℝ)) (by norm_num)
  have hle : Real.Gamma (3 / 4 + 1) ≤ 1 := Gamma_le_one_of_mem_Icc (by norm_num) (by norm_num)
  rw [h] at hle
  linarith

/-! ## 2.  `|sin z| <= exp |Im z|` -/

/-- **Complex sine envelope.**  `sin z = (exp(-zI) - exp(zI)) I / 2`, and
    `|exp(-zI)| = exp(Im z)`, `|exp(zI)| = exp(-Im z)`, both `<= exp |Im z|`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_sub, neg_neg]
    exact le_abs_self _
  have h2 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
    exact neg_le_abs _
  rw [Complex.sin]
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by gcongr
    _ = Real.exp |z.im| := by ring

/-! ## 3.  Two-sided bounds for `|Gamma(1/4 + i y)|` -/

/-- **Upper bound** `|Gamma(1/4 + i y)| <= 4`. -/
theorem norm_Gamma_quarter_upper (y : ℝ) :
    ‖Complex.Gamma (((1/4 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 4 := by
  have hre : (((1/4 : ℝ) : ℂ) + (y : ℂ) * I).re = 1 / 4 := by simp
  have h := norm_Gamma_le_Gamma_re (s := ((1/4 : ℝ) : ℂ) + (y : ℂ) * I) (by rw [hre]; norm_num)
  rw [hre] at h
  exact le_trans h Gamma_quarter_le

/-- **Lower bound (reflection formula)** `(9/4) * exp(-pi |y|) <= |Gamma(1/4 + i y)|`.
    `Gamma(s) Gamma(1-s) = pi / sin(pi s)` with `s = 1/4 + i y`; `|Gamma(1-s)| <= Gamma(3/4) <= 4/3`
    and `|sin(pi s)| <= exp(pi |y|)`, so `|Gamma(s)| >= pi / ((4/3) exp(pi |y|)) >= (9/4) exp(-pi |y|)`. -/
theorem norm_Gamma_quarter_lower (y : ℝ) :
    (9 / 4) * Real.exp (-(Real.pi * |y|)) ≤ ‖Complex.Gamma (((1/4 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
  set s : ℂ := ((1/4 : ℝ) : ℂ) + (y : ℂ) * I with hs
  have hsre : s.re = 1 / 4 := by rw [hs]; simp
  have hs1re : (1 - s).re = 3 / 4 := by rw [Complex.sub_re, hsre]; simp; norm_num
  have hG1 : ‖Complex.Gamma (1 - s)‖ ≤ 4 / 3 := by
    have h := norm_Gamma_le_Gamma_re (s := 1 - s) (by rw [hs1re]; norm_num)
    rw [hs1re] at h
    exact le_trans h Gamma_three_quarter_le
  have hGs0 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hGs10 : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hs1re]; norm_num)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- norms of the reflection identity
  have hprod_ne : Complex.Gamma s * Complex.Gamma (1 - s) ≠ 0 := mul_ne_zero hGs0 hGs10
  have hsin_ne : Complex.sin (↑Real.pi * s) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hrefl; exact hprod_ne hrefl
  have hnorm : ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖
      = Real.pi / ‖Complex.sin (↑Real.pi * s)‖ := by
    rw [← norm_mul, hrefl, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi_pos]
  -- |sin(pi s)| <= exp(pi |y|)
  have hsinle : ‖Complex.sin (↑Real.pi * s)‖ ≤ Real.exp (Real.pi * |y|) := by
    have h := norm_sin_le_exp_abs_im (↑Real.pi * s)
    have him : (↑Real.pi * s).im = Real.pi * y := by rw [hs]; simp
    rw [him, abs_mul, abs_of_pos hpi_pos] at h
    exact h
  have hsinpos : 0 < ‖Complex.sin (↑Real.pi * s)‖ := norm_pos_iff.mpr hsin_ne
  have hG1pos : 0 < ‖Complex.Gamma (1 - s)‖ := norm_pos_iff.mpr hGs10
  have hexp_pos : 0 < Real.exp (Real.pi * |y|) := Real.exp_pos _
  -- |Gamma s| = pi / (|sin| * |Gamma(1-s)|)
  have h3 : ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin (↑Real.pi * s)‖
      = Real.pi := by
    rw [hnorm]; field_simp
  have hGs : ‖Complex.Gamma s‖
      = Real.pi / (‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖) := by
    rw [eq_div_iff (ne_of_gt (mul_pos hsinpos hG1pos))]
    calc ‖Complex.Gamma s‖ * (‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖)
        = ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin (↑Real.pi * s)‖ := by ring
      _ = Real.pi := h3
  rw [hGs]
  have hden : ‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖
      ≤ Real.exp (Real.pi * |y|) * (4 / 3) :=
    mul_le_mul hsinle hG1 (le_of_lt hG1pos) (le_of_lt hexp_pos)
  have hdenpos : 0 < ‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖ :=
    mul_pos hsinpos hG1pos
  have hstep : Real.pi / (Real.exp (Real.pi * |y|) * (4 / 3))
      ≤ Real.pi / (‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖) :=
    div_le_div_of_nonneg_left (le_of_lt hpi_pos) hdenpos hden
  have hexpneg : Real.exp (-(Real.pi * |y|)) = (Real.exp (Real.pi * |y|))⁻¹ := Real.exp_neg _
  have hpi3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  calc (9 / 4) * Real.exp (-(Real.pi * |y|))
      = (9 / 4) / Real.exp (Real.pi * |y|) := by rw [hexpneg]; ring
    _ ≤ Real.pi / (Real.exp (Real.pi * |y|) * (4 / 3)) := by
        rw [div_le_div_iff₀ hexp_pos (by positivity)]
        nlinarith [hexp_pos]
    _ ≤ _ := hstep

/-! ## 4.  The explicit polar decomposition of `gLine` -/

/-- **`Gamma_R` polar form with the magnitude NAMED.**  Same proof as
    `ZeroSignDecomp.gamma_r_polar_t`, but the magnitude is the explicit
    `M = pi^(-1/4) * |Gamma(1/4 + i t/2)|` instead of an existential witness. -/
theorem gamma_r_polar_explicit (t : ℝ) (Λ : ℝ)
    (hbranch : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)
        = (‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ : ℂ) * Complex.exp (Complex.I * (Λ:ℂ))) :
    Gammaℝ ((1/2:ℂ) + (t:ℂ)*I)
      = ((Real.pi ^ (-(1/4):ℝ) * ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((Λ - (t/2) * Real.log Real.pi : ℝ):ℂ)) := by
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  set NG : ℝ := ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ with hNG
  have hhalf : ((1/2:ℂ) + (t:ℂ)*I)/2 = ((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I := by push_cast; ring
  have hpi : (Real.pi : ℂ) ^ (-((1/2:ℂ) + (t:ℂ)*I)/2)
      = ((Real.pi ^ (-(1/4):ℝ) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((- (t/2) * Real.log Real.pi : ℝ):ℂ)) := by
    have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      rw [Complex.ofReal_log hpipos.le]
    have hne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.cpow_def_of_ne_zero hne, hlog,
      show (Real.log Real.pi : ℂ) * (-((1/2:ℂ) + (t:ℂ)*I)/2)
          = (((-(1/4):ℝ) * Real.log Real.pi : ℝ):ℂ)
            + Complex.I * ((-(t/2) * Real.log Real.pi : ℝ):ℂ) by push_cast; ring,
      Complex.exp_add]
    congr 1
    rw [Real.rpow_def_of_pos hpipos, Complex.ofReal_exp, mul_comm]
  rw [Gammaℝ_def, hhalf, hbranch, hpi,
    show Complex.exp (Complex.I * ((Λ - (t/2) * Real.log Real.pi : ℝ):ℂ))
        = Complex.exp (Complex.I * ((- (t/2) * Real.log Real.pi : ℝ):ℂ))
          * Complex.exp (Complex.I * (Λ:ℂ)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
  push_cast; ring

/-- The magnitude factor `M(t) = pi^(-1/4) * |Gamma(1/4 + i t/2)|`. -/
noncomputable def gammaRMag (t : ℝ) : ℝ :=
  Real.pi ^ (-(1/4):ℝ) * ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖

/-- **The explicit `gLine` decomposition.**  For `t ≠ 0` there is the theta-limit `Λ` (from the
    discharged `ThetaConverge.convergence_obligation`, exposed as a `Tendsto` fact) with

        gLine t = gammaRMag t * (cos(Λ - (t/2) log pi) * Re zeta(1/2+it)
                                 - sin(Λ - (t/2) log pi) * Im zeta(1/2+it)). -/
theorem gLine_decomp_explicit (t : ℝ) (ht : t ≠ 0) :
    ∃ Λ : ℝ, Filter.Tendsto (imLnVal (1/4) (t/2)) Filter.atTop (nhds Λ) ∧
      gLine t = gammaRMag t *
        (Real.cos (Λ - (t/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(t:ℂ)*I)).re
          - Real.sin (Λ - (t/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(t:ℂ)*I)).im) := by
  have hGne : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    exact ht (by linarith [him])
  obtain ⟨Λ, hΛtend, hbranch⟩ :=
    ThetaConverge.convergence_obligation (1/4) (t/2) (by norm_num) hGne
  have hG := gamma_r_polar_explicit t Λ hbranch
  refine ⟨Λ, hΛtend, ?_⟩
  set φ : ℝ := Λ - (t/2) * Real.log Real.pi with hφ
  set Z : ℂ := riemannZeta ((1/2:ℂ)+(t:ℂ)*I) with hZ
  have hs0 : ((1/2 : ℂ) + (t:ℂ)*I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hGRne : Gammaℝ ((1/2:ℂ) + (t:ℂ)*I) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos; simp [Complex.add_re, Complex.mul_re]
  have hcomp : completedRiemannZeta ((1/2:ℂ)+(t:ℂ)*I) = Gammaℝ ((1/2:ℂ) + (t:ℂ)*I) * Z := by
    rw [hZ, riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hGRne]
  have hgl : gLine t = (completedRiemannZeta ((1/2:ℂ)+(t:ℂ)*I)).re := rfl
  rw [hgl, hcomp, hG,
    show Complex.exp (Complex.I * (φ:ℂ)) = Complex.exp ((φ:ℂ) * Complex.I) by rw [mul_comm],
    Complex.exp_ofReal_mul_I]
  unfold gammaRMag
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The magnitude envelope** `(3/4) exp(-pi |t|/2) <= gammaRMag t <= 4`. -/
theorem gammaRMag_bounds (t : ℝ) :
    (3 / 4) * Real.exp (-(Real.pi * |t / 2|)) ≤ gammaRMag t ∧ gammaRMag t ≤ 4 := by
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hlo := norm_Gamma_quarter_lower (t / 2)
  have hhi := norm_Gamma_quarter_upper (t / 2)
  have hGnn : 0 ≤ ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ := norm_nonneg _
  have hp_le : Real.pi ^ (-(1/4):ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have hp_pos : 0 < Real.pi ^ (-(1/4):ℝ) := Real.rpow_pos_of_pos hpipos _
  -- pi^(-1/4) >= 1/2 (crude): pi <= 16, so pi^(1/4) <= 16^(1/4) = 2.
  have hp_ge : (1 / 2) ≤ Real.pi ^ (-(1/4):ℝ) := by
    rw [Real.rpow_neg (le_of_lt hpipos)]
    have h16 : Real.pi ≤ 16 := by linarith [Real.pi_lt_d2]
    have hq : Real.pi ^ ((1:ℝ)/4) ≤ 2 := by
      calc Real.pi ^ ((1:ℝ)/4) ≤ (16:ℝ) ^ ((1:ℝ)/4) :=
            Real.rpow_le_rpow (le_of_lt hpipos) h16 (by norm_num)
        _ = 2 := by
            rw [show (16:ℝ) = 2 ^ (4:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
    have hqpos : 0 < Real.pi ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hpipos _
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num]
    exact inv_anti₀ hqpos hq
  unfold gammaRMag
  constructor
  · -- (3/4) e^{-pi|t/2|} <= (1/3) (9/4) e^{-pi|t/2|} <= pi^(-1/4) |Gamma|
    have hE : 0 ≤ Real.exp (-(Real.pi * |t / 2|)) := le_of_lt (Real.exp_pos _)
    calc (3 / 4) * Real.exp (-(Real.pi * |t / 2|))
        ≤ (1 / 2) * ((9 / 4) * Real.exp (-(Real.pi * |t / 2|))) := by nlinarith [hE]
      _ ≤ Real.pi ^ (-(1/4):ℝ) * ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ :=
          mul_le_mul hp_ge hlo (by positivity) (le_of_lt hp_pos)
  · calc Real.pi ^ (-(1/4):ℝ) * ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖
        ≤ 1 * 4 := mul_le_mul hp_le hhi hGnn (by norm_num)
      _ = 4 := by norm_num

end KernelGammaEnvelope

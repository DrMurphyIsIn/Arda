/- telperion 0.1.6 | family WindingCount | input-hash e4e30bc6e6e4ed7e
   5 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

open Complex intervalIntegral MeasureTheory Real

namespace WindingCount

/-!
# Kernel-verified boundary winding count (Stage 2A)

Each theorem below states that the four-segment boundary integral of a
log-derivative around a rectangle equals `2*pi*i*N`.

`winding_z2` is the from-scratch de-risking instance: for `f z = z^2` the
log-derivative `2z/z^2` reduces to `2*z^{-1}`, and the winding-ONE primitive
`box_inv_winding` (segment/`Complex.log` branch-split, pole 0) gives `N = 2`.

`winding_lambda_five` is the completedRiemannZeta instance on `[2/5,3/5]x[10,35]`:
GIVEN the 5 on-line zeros' enclosure brackets (`hin`, the documented Arb non-kernel
input as hypotheses) and the argument-principle residue decomposition of
`Lambda'/Lambda` on the boundary, the boundary integral equals `2*pi*i*5`.  The
per-pole winding is DISCHARGED from the interior-pole primitive `rect_winding_lambda`
(no Mathlib gap); Finset linearity telescopes the four sides.

conjecture1_proved = False.  This localizes a winding count from certified
enclosures; it does NOT prove RH.
-/

-- Monodromy jump: `log(-x) - log x = pi*i` when `Im x < 0` (principal branch).
theorem log_neg_sub_im_neg (x : ℂ) (hx : x.im < 0) :
    Complex.log (-x) - Complex.log x = ↑π * I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]

-- Monodromy jump: `log(-x) - log x = -(pi*i)` when `Im x > 0` (principal branch).
theorem log_neg_sub_im_pos (x : ℂ) (hx : 0 < x.im) :
    Complex.log (-x) - Complex.log x = -(↑π * I) := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]

/-- Winding number ONE about 0: `Bd((z)^{-1}) = 2*pi*i` on `[(-1),1]x[(-1),1]`.
    Segment/`Complex.log` branch-split proof (RectWinding with pole 0). -/
theorem winding_z2_box_inv_winding :
    (∫ x in ((-1) : ℝ)..1, ((↑x + (((-1) : ℝ) : ℂ) * I) - 0)⁻¹)
        - (∫ x in ((-1) : ℝ)..1, ((↑x + ((1 : ℝ) : ℂ) * I) - 0)⁻¹)
        + I • (∫ y in ((-1) : ℝ)..1, ((((1 : ℝ) : ℂ) + ↑y * I) - 0)⁻¹)
        - I • (∫ y in ((-1) : ℝ)..1, (((((-1) : ℝ) : ℂ) + ↑y * I) - 0)⁻¹)
      = 2 * ↑π * I := by
  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - 0).im ≠ 0) →
      (∫ x in ((-1) : ℝ)..1, ((↑x + c) - 0)⁻¹)
        = Complex.log ((↑(1 : ℝ) + c) - 0) - Complex.log ((↑((-1) : ℝ) + c) - 0) := by
    intro c hc
    have hderiv : ∀ x ∈ Set.uIcc ((-1) : ℝ) 1,
        HasDerivAt (fun x : ℝ => Complex.log ((↑x + c) - 0)) (((↑x + c) - 0)⁻¹) x := by
      intro x _
      have hpath : HasDerivAt (fun x : ℝ => ((↑x : ℂ) + c) - 0) 1 x := by
        have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
        exact (h1.add_const c).sub_const 0
      have hslit : ((↑x + c) - 0) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; exact Or.inr (hc x)
      have hd := hpath.clog_real hslit
      rwa [one_div] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine Continuous.inv₀ (by fun_prop) (fun x => ?_)
    rw [sub_ne_zero]; intro h
    exact hc x (by rw [h]; simp)
  have vert : ∀ c : ℂ, (∀ y : ℝ, ((c + ↑y * I) - 0) ∈ Complex.slitPlane) →
      I • (∫ y in ((-1) : ℝ)..1, ((c + ↑y * I) - 0)⁻¹)
        = Complex.log ((c + ↑(1 : ℝ) * I) - 0) - Complex.log ((c + ↑((-1) : ℝ) * I) - 0) := by
    intro c hslit
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc ((-1) : ℝ) 1,
        HasDerivAt (fun y : ℝ => Complex.log ((c + ↑y * I) - 0)) (I • ((c + ↑y * I) - 0)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => (c + (↑y : ℂ) * I) - 0) I y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add c).sub_const 0
      have hd := hpath.clog_real (hslit y)
      rwa [div_eq_mul_inv, ← smul_eq_mul] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    have := hslit y
    rw [Complex.mem_slitPlane_iff] at this
    intro h; rw [h] at this; simp at this
  have hbot := horiz ((((-1) : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num)
  have htop := horiz (((1 : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num)
  have hright := vert ((1 : ℝ) : ℂ) (by
    intro y; rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; norm_num)
  have hleftJ : I • (∫ y in ((-1) : ℝ)..1, (((((-1) : ℝ) : ℂ) + ↑y * I) - 0)⁻¹)
      = Complex.log (0 - ((((-1) : ℝ) : ℂ) + ↑(1 : ℝ) * I)) - Complex.log (0 - ((((-1) : ℝ) : ℂ) + ↑((-1) : ℝ) * I)) := by
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc ((-1) : ℝ) 1,
        HasDerivAt (fun y : ℝ => Complex.log (0 - ((((-1) : ℝ) : ℂ) + ↑y * I)))
          (I • (((((-1) : ℝ) : ℂ) + ↑y * I) - 0)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => 0 - ((((-1) : ℝ) : ℂ) + (↑y : ℂ) * I)) (-I) y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add (((((-1) : ℝ) : ℂ)))).const_sub 0
      have hslit : (0 - ((((-1) : ℝ) : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]; norm_num
      have hd := hpath.clog_real hslit
      have hval : (-I) / (0 - ((((-1) : ℝ) : ℂ) + ↑y * I)) = I • (((((-1) : ℝ) : ℂ) + ↑y * I) - 0)⁻¹ := by
        rw [smul_eq_mul, div_eq_mul_inv,
          show (0 : ℂ) - ((((-1) : ℝ) : ℂ) + ↑y * I) = -(((((-1) : ℝ) : ℂ) + ↑y * I) - 0) from by ring, inv_neg]
        ring
      rwa [hval] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    rw [sub_ne_zero]; intro h
    have : (((((-1) : ℝ) : ℂ) + ↑y * I)).re = (0 : ℂ).re := by rw [h]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this
  rw [hbot, htop, hright, hleftJ,
    show (0 : ℂ) - ((((-1) : ℝ) : ℂ) + ↑(1 : ℝ) * I) = -((↑((-1) : ℝ) + ((1 : ℝ) : ℂ) * I) - 0) from by ring,
    show (0 : ℂ) - ((((-1) : ℝ) : ℂ) + ↑((-1) : ℝ) * I) = -((↑((-1) : ℝ) + (((-1) : ℝ) : ℂ) * I) - 0) from by ring]
  have hAim : ((↑((-1) : ℝ) + (((-1) : ℝ) : ℂ) * I) - 0).im < 0 := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num
  have hDim : 0 < ((↑((-1) : ℝ) + ((1 : ℝ) : ℂ) * I) - 0).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num
  linear_combination log_neg_sub_im_neg ((↑((-1) : ℝ) + (((-1) : ℝ) : ℂ) * I) - 0) hAim
    - log_neg_sub_im_pos ((↑((-1) : ℝ) + ((1 : ℝ) : ℂ) * I) - 0) hDim

/-- Pointwise: for `w != 0`, the log-derivative of `w^2`, `2*w/w^2`, is `2*w^{-1}`. -/
theorem winding_z2_logderiv_sq_eq (w : ℂ) (hw : w ≠ 0) : 2 * w / w ^ 2 = 2 * w⁻¹ := by
  field_simp

/-- TOY winding-count theorem (`f z = z^2`, `N = 2` on `[(-1),1]x[(-1),1]`).
    The four-segment boundary integral of the log-derivative `f'/f = 2z/z^2`
    equals `2*pi*i*2`.  The integrand reduces pointwise to `2*z^{-1}` (path value
    nonzero on the boundary); the winding-ONE primitive + linearity closes it. -/
theorem winding_z2 :
    (∫ x in ((-1) : ℝ)..1, 2 * (↑x + (((-1) : ℝ) : ℂ) * I) / (↑x + (((-1) : ℝ) : ℂ) * I) ^ 2)
        - (∫ x in ((-1) : ℝ)..1, 2 * (↑x + ((1 : ℝ) : ℂ) * I) / (↑x + ((1 : ℝ) : ℂ) * I) ^ 2)
        + I • (∫ y in ((-1) : ℝ)..1, 2 * (((1 : ℝ) : ℂ) + ↑y * I) / (((1 : ℝ) : ℂ) + ↑y * I) ^ 2)
        - I • (∫ y in ((-1) : ℝ)..1, 2 * ((((-1) : ℝ) : ℂ) + ↑y * I) / ((((-1) : ℝ) : ℂ) + ↑y * I) ^ 2)
      = 2 * ↑π * I * 2 := by
  have hbot_ne : ∀ x : ℝ, (↑x + (((-1) : ℝ) : ℂ) * I) ≠ 0 := by
    intro x h
    have : ((↑x + (((-1) : ℝ) : ℂ) * I)).im = (0 : ℂ).im := by rw [h]
    simp at this
  have htop_ne : ∀ x : ℝ, (↑x + ((1 : ℝ) : ℂ) * I) ≠ 0 := by
    intro x h
    have : ((↑x + ((1 : ℝ) : ℂ) * I)).im = (0 : ℂ).im := by rw [h]
    simp at this
  have hright_ne : ∀ y : ℝ, (((1 : ℝ) : ℂ) + ↑y * I) ≠ 0 := by
    intro y h
    have : ((((1 : ℝ) : ℂ) + ↑y * I)).re = (0 : ℂ).re := by rw [h]
    simp at this
  have hleft_ne : ∀ y : ℝ, ((((-1) : ℝ) : ℂ) + ↑y * I) ≠ 0 := by
    intro y h
    have : (((((-1) : ℝ) : ℂ) + ↑y * I)).re = (0 : ℂ).re := by rw [h]
    simp at this
  have ebot : (∫ x in ((-1) : ℝ)..1, 2 * (↑x + (((-1) : ℝ) : ℂ) * I) / (↑x + (((-1) : ℝ) : ℂ) * I) ^ 2)
      = ∫ x in ((-1) : ℝ)..1, 2 * ((↑x + (((-1) : ℝ) : ℂ) * I) - 0)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x _; simp only [sub_zero]; exact winding_z2_logderiv_sq_eq _ (hbot_ne x)
  have etop : (∫ x in ((-1) : ℝ)..1, 2 * (↑x + ((1 : ℝ) : ℂ) * I) / (↑x + ((1 : ℝ) : ℂ) * I) ^ 2)
      = ∫ x in ((-1) : ℝ)..1, 2 * ((↑x + ((1 : ℝ) : ℂ) * I) - 0)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x _; simp only [sub_zero]; exact winding_z2_logderiv_sq_eq _ (htop_ne x)
  have eright : (∫ y in ((-1) : ℝ)..1, 2 * (((1 : ℝ) : ℂ) + ↑y * I) / (((1 : ℝ) : ℂ) + ↑y * I) ^ 2)
      = ∫ y in ((-1) : ℝ)..1, 2 * ((((1 : ℝ) : ℂ) + ↑y * I) - 0)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro y _; simp only [sub_zero]; exact winding_z2_logderiv_sq_eq _ (hright_ne y)
  have eleft : (∫ y in ((-1) : ℝ)..1, 2 * ((((-1) : ℝ) : ℂ) + ↑y * I) / ((((-1) : ℝ) : ℂ) + ↑y * I) ^ 2)
      = ∫ y in ((-1) : ℝ)..1, 2 * (((((-1) : ℝ) : ℂ) + ↑y * I) - 0)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro y _; simp only [sub_zero]; exact winding_z2_logderiv_sq_eq _ (hleft_ne y)
  rw [ebot, etop, eright, eleft]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    smul_eq_mul, smul_eq_mul]
  have key := winding_z2_box_inv_winding
  rw [smul_eq_mul, smul_eq_mul] at key
  linear_combination (2 : ℂ) * key
example : (∫ x in ((-1) : ℝ)..1, 2 * (↑x + (((-1) : ℝ) : ℂ) * I) / (↑x + (((-1) : ℝ) : ℂ) * I) ^ 2)
        - (∫ x in ((-1) : ℝ)..1, 2 * (↑x + ((1 : ℝ) : ℂ) * I) / (↑x + ((1 : ℝ) : ℂ) * I) ^ 2)
        + I • (∫ y in ((-1) : ℝ)..1, 2 * (((1 : ℝ) : ℂ) + ↑y * I) / (((1 : ℝ) : ℂ) + ↑y * I) ^ 2)
        - I • (∫ y in ((-1) : ℝ)..1, 2 * ((((-1) : ℝ) : ℂ) + ↑y * I) / ((((-1) : ℝ) : ℂ) + ↑y * I) ^ 2)
      = 2 * ↑π * I * 2 := winding_z2

/-- Winding number ONE about an interior pole ρ of `[(2 / 5),(3 / 5)]x[10,35]`:
    `Bd((z-ρ)^{-1}) = 2*pi*i`.  Segment/`Complex.log` branch-split proof. -/
theorem winding_lambda_five_rect_winding (ρ : ℂ)
    (hre0 : ((2 / 5) : ℝ) < ρ.re) (hre1 : ρ.re < (3 / 5))
    (him0 : (10 : ℝ) < ρ.im) (him1 : ρ.im < 35) :
    (∫ x in ((2 / 5) : ℝ)..(3 / 5), ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
        - (∫ x in ((2 / 5) : ℝ)..(3 / 5), ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in (10 : ℝ)..35, (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (10 : ℝ)..35, (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I := by
  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - ρ).im ≠ 0) →
      (∫ x in ((2 / 5) : ℝ)..(3 / 5), ((↑x + c) - ρ)⁻¹)
        = Complex.log ((↑((3 / 5) : ℝ) + c) - ρ) - Complex.log ((↑((2 / 5) : ℝ) + c) - ρ) := by
    intro c hc
    have hderiv : ∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5),
        HasDerivAt (fun x : ℝ => Complex.log ((↑x + c) - ρ)) (((↑x + c) - ρ)⁻¹) x := by
      intro x _
      have hpath : HasDerivAt (fun x : ℝ => ((↑x : ℂ) + c) - ρ) 1 x := by
        have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
        exact (h1.add_const c).sub_const ρ
      have hslit : ((↑x + c) - ρ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; exact Or.inr (hc x)
      have hd := hpath.clog_real hslit
      rwa [one_div] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine Continuous.inv₀ (by fun_prop) (fun x => ?_)
    rw [sub_ne_zero]; intro h
    exact hc x (by rw [h]; simp)
  have vert : ∀ c : ℂ, (∀ y : ℝ, ((c + ↑y * I) - ρ) ∈ Complex.slitPlane) →
      I • (∫ y in (10 : ℝ)..35, ((c + ↑y * I) - ρ)⁻¹)
        = Complex.log ((c + ↑(35 : ℝ) * I) - ρ) - Complex.log ((c + ↑(10 : ℝ) * I) - ρ) := by
    intro c hslit
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc (10 : ℝ) 35,
        HasDerivAt (fun y : ℝ => Complex.log ((c + ↑y * I) - ρ)) (I • ((c + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => (c + (↑y : ℂ) * I) - ρ) I y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add c).sub_const ρ
      have hd := hpath.clog_real (hslit y)
      rwa [div_eq_mul_inv, ← smul_eq_mul] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    have := hslit y
    rw [Complex.mem_slitPlane_iff] at this
    intro h; rw [h] at this; simp at this
  have hbot := horiz (((10 : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have htop := horiz (((35 : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have hright := vert (((3 / 5) : ℝ) : ℂ) (by
    intro y; rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith)
  have hleftJ : I • (∫ y in (10 : ℝ)..35, (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
      = Complex.log (ρ - ((((2 / 5) : ℝ) : ℂ) + ↑(35 : ℝ) * I)) - Complex.log (ρ - ((((2 / 5) : ℝ) : ℂ) + ↑(10 : ℝ) * I)) := by
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc (10 : ℝ) 35,
        HasDerivAt (fun y : ℝ => Complex.log (ρ - ((((2 / 5) : ℝ) : ℂ) + ↑y * I)))
          (I • (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => ρ - ((((2 / 5) : ℝ) : ℂ) + (↑y : ℂ) * I)) (-I) y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add ((((2 / 5) : ℝ) : ℂ))).const_sub ρ
      have hslit : (ρ - ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith
      have hd := hpath.clog_real hslit
      have hval : (-I) / (ρ - ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) = I • (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ := by
        rw [smul_eq_mul, div_eq_mul_inv,
          show ρ - ((((2 / 5) : ℝ) : ℂ) + ↑y * I) = -(((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ) from by ring, inv_neg]
        ring
      rwa [hval] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    rw [sub_ne_zero]; intro h
    have : (((((2 / 5) : ℝ) : ℂ) + ↑y * I)).re = ρ.re := by rw [h]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this; linarith
  rw [hbot, htop, hright, hleftJ,
    show ρ - ((((2 / 5) : ℝ) : ℂ) + ↑(35 : ℝ) * I) = -((↑((2 / 5) : ℝ) + ((35 : ℝ) : ℂ) * I) - ρ) from by ring,
    show ρ - ((((2 / 5) : ℝ) : ℂ) + ↑(10 : ℝ) * I) = -((↑((2 / 5) : ℝ) + ((10 : ℝ) : ℂ) * I) - ρ) from by ring]
  have hAim : ((↑((2 / 5) : ℝ) + ((10 : ℝ) : ℂ) * I) - ρ).im < 0 := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  have hDim : 0 < ((↑((2 / 5) : ℝ) + ((35 : ℝ) : ℂ) * I) - ρ).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  linear_combination log_neg_sub_im_neg ((↑((2 / 5) : ℝ) + ((10 : ℝ) : ℂ) * I) - ρ) hAim
    - log_neg_sub_im_pos ((↑((2 / 5) : ℝ) + ((35 : ℝ) : ℂ) * I) - ρ) hDim

/-- Λ boundary log-derivative winding count on `[(2 / 5),(3 / 5)]x[10,35]`, `N = 5`.
    GIVEN the 5 zeros' enclosure brackets (`hin`, the documented Arb non-kernel
    input as hypotheses) and the argument-principle residue decomposition of
    `Lambda'/Lambda` on the boundary (`hd*`), the boundary integral equals
    `2*pi*i*5`.  The per-pole winding `Bd((z-ρ)^{-1}) = 2*pi*i` is DISCHARGED
    from the interior-pole primitive `winding_lambda_five_rect_winding`; Finset linearity telescopes
    the four sides.  conjecture1_proved = False. -/
theorem winding_lambda_five
    (Ld : ℂ → ℂ) (s : Finset ℂ) (m : ℂ → ℤ)
    (hcard : s.card = 5)
    (hm : ∀ ρ ∈ s, m ρ = 1)
    (hin : ∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35)
    (hb : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (ht : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hr : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (hl : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (hdb : ∀ x : ℝ, Ld (↑x + ((10 : ℝ) : ℂ) * I) = ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
    (hdt : ∀ x : ℝ, Ld (↑x + ((35 : ℝ) : ℂ) * I) = ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
    (hdr : ∀ y : ℝ, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I) = ∑ ρ ∈ s, (m ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
    (hdl : ∀ y : ℝ, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I) = ∑ ρ ∈ s, (m ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) :
    (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((10 : ℝ) : ℂ) * I))
        - (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((35 : ℝ) : ℂ) * I))
        + I • (∫ y in (10 : ℝ)..35, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (10 : ℝ)..35, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = 2 * ↑π * I * 5 := by
  have eb : (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((10 : ℝ) : ℂ) * I))
      = ∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹ :=
    intervalIntegral.integral_congr (fun x _ => hdb x)
  have et : (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((35 : ℝ) : ℂ) * I))
      = ∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹ :=
    intervalIntegral.integral_congr (fun x _ => hdt x)
  have er : (∫ y in (10 : ℝ)..35, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
      = ∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (m ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ :=
    intervalIntegral.integral_congr (fun y _ => hdr y)
  have el : (∫ y in (10 : ℝ)..35, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = ∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (m ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ :=
    intervalIntegral.integral_congr (fun y _ => hdl y)
  rw [eb, et, er, el]
  rw [intervalIntegral.integral_finsetSum (μ := volume) (a := ((2 / 5):ℝ)) (b := ((3 / 5):ℝ)) (s := s)
        (f := fun (ρ : ℂ) (x : ℝ) => (m ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
        (fun ρ hρ => (hb ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (μ := volume) (a := ((2 / 5):ℝ)) (b := ((3 / 5):ℝ)) (s := s)
        (f := fun (ρ : ℂ) (x : ℝ) => (m ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
        (fun ρ hρ => (ht ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (μ := volume) (a := (10:ℝ)) (b := (35:ℝ)) (s := s)
        (f := fun (ρ : ℂ) (y : ℝ) => (m ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        (fun ρ hρ => (hr ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (μ := volume) (a := (10:ℝ)) (b := (35:ℝ)) (s := s)
        (f := fun (ρ : ℂ) (y : ℝ) => (m ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        (fun ρ hρ => (hl ρ hρ).const_mul (m ρ : ℂ))]
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hsum : (∑ ρ ∈ s,
      ((m ρ : ℂ) * (∫ x in ((2 / 5) : ℝ)..(3 / 5), ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
        - (m ρ : ℂ) * (∫ x in ((2 / 5) : ℝ)..(3 / 5), ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + I * ((m ρ : ℂ) * (∫ y in (10 : ℝ)..35, (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹))
        - I * ((m ρ : ℂ) * (∫ y in (10 : ℝ)..35, (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹))))
      = ∑ _ρ ∈ s, (2 * ↑π * I : ℂ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    obtain ⟨hre0, hre1, him0, him1⟩ := hin ρ hρ
    have hw := winding_lambda_five_rect_winding ρ hre0 hre1 him0 him1
    rw [smul_eq_mul, smul_eq_mul] at hw
    rw [hm ρ hρ, Int.cast_one]
    linear_combination hw
  rw [hsum, Finset.sum_const, hcard]
  simp only [nsmul_eq_mul]
  push_cast
  ring
example : ∀ (Ld : ℂ → ℂ) (s : Finset ℂ) (m : ℂ → ℤ), (s.card = 5) → (∀ ρ ∈ s, m ρ = 1) → (∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35) → (∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) → (∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) → (∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) → (∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) → (∀ x : ℝ, Ld (↑x + ((10 : ℝ) : ℂ) * I) = ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) → (∀ x : ℝ, Ld (↑x + ((35 : ℝ) : ℂ) * I) = ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) → (∀ y : ℝ, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I) = ∑ ρ ∈ s, (m ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) → (∀ y : ℝ, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I) = ∑ ρ ∈ s, (m ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) → (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((10 : ℝ) : ℂ) * I))
        - (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((35 : ℝ) : ℂ) * I))
        + I • (∫ y in (10 : ℝ)..35, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (10 : ℝ)..35, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = 2 * ↑π * I * 5 := winding_lambda_five

end WindingCount

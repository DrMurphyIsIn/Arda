/- telperion 0.1.6 | family RectWinding | input-hash bd8d87da55955523
   4 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace RectWinding

open Complex intervalIntegral Real

/-- Monodromy jump: `log(-x) - log x = π i` when `Im x < 0` (principal branch). -/
theorem log_neg_sub_im_neg (x : ℂ) (hx : x.im < 0) :
    Complex.log (-x) - Complex.log x = ↑π * I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]

/-- Monodromy jump: `log(-x) - log x = -(π i)` when `Im x > 0` (principal branch). -/
theorem log_neg_sub_im_pos (x : ℂ) (hx : 0 < x.im) :
    Complex.log (-x) - Complex.log x = -(↑π * I) := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]

/-- Winding number ONE: `∮_∂[0,2]×[0,1] (z-ρ)⁻¹ = 2πi` for `ρ` strictly
    inside.  Segment/log branch-split proof — the winding-NONZERO primitive. -/
theorem rect_winding_unit (ρ : ℂ)
    (hre0 : (0 : ℝ) < ρ.re) (hre1 : ρ.re < 2)
    (him0 : (0 : ℝ) < ρ.im) (him1 : ρ.im < 1) :
    (∫ x in (0 : ℝ)..2, ((↑x + ((0 : ℝ) : ℂ) * I) - ρ)⁻¹)
        - (∫ x in (0 : ℝ)..2, ((↑x + ((1 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in (0 : ℝ)..1, ((((2 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (0 : ℝ)..1, ((((0 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I := by
  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - ρ).im ≠ 0) →
      (∫ x in (0 : ℝ)..2, ((↑x + c) - ρ)⁻¹)
        = Complex.log ((↑(2 : ℝ) + c) - ρ) - Complex.log ((↑(0 : ℝ) + c) - ρ) := by
    intro c hc
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
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
      I • (∫ y in (0 : ℝ)..1, ((c + ↑y * I) - ρ)⁻¹)
        = Complex.log ((c + ↑(1 : ℝ) * I) - ρ) - Complex.log ((c + ↑(0 : ℝ) * I) - ρ) := by
    intro c hslit
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
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
  have hbot := horiz (((0 : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have htop := horiz (((1 : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have hright := vert ((2 : ℝ) : ℂ) (by
    intro y; rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith)
  have hleftJ : I • (∫ y in (0 : ℝ)..1, ((((0 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
      = Complex.log (ρ - (((0 : ℝ) : ℂ) + ↑(1 : ℝ) * I)) - Complex.log (ρ - (((0 : ℝ) : ℂ) + ↑(0 : ℝ) * I)) := by
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => Complex.log (ρ - (((0 : ℝ) : ℂ) + ↑y * I)))
          (I • ((((0 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => ρ - (((0 : ℝ) : ℂ) + (↑y : ℂ) * I)) (-I) y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add (((0 : ℝ) : ℂ))).const_sub ρ
      have hslit : (ρ - (((0 : ℝ) : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith
      have hd := hpath.clog_real hslit
      have hval : (-I) / (ρ - (((0 : ℝ) : ℂ) + ↑y * I)) = I • ((((0 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ := by
        rw [smul_eq_mul, div_eq_mul_inv,
          show ρ - (((0 : ℝ) : ℂ) + ↑y * I) = -((((0 : ℝ) : ℂ) + ↑y * I) - ρ) from by ring, inv_neg]
        ring
      rwa [hval] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    rw [sub_ne_zero]; intro h
    have : ((((0 : ℝ) : ℂ) + ↑y * I)).re = ρ.re := by rw [h]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this; linarith
  rw [hbot, htop, hright, hleftJ,
    show ρ - (((0 : ℝ) : ℂ) + ↑(1 : ℝ) * I) = -((↑(0 : ℝ) + ((1 : ℝ) : ℂ) * I) - ρ) from by ring,
    show ρ - (((0 : ℝ) : ℂ) + ↑(0 : ℝ) * I) = -((↑(0 : ℝ) + ((0 : ℝ) : ℂ) * I) - ρ) from by ring]
  have hAim : ((↑(0 : ℝ) + ((0 : ℝ) : ℂ) * I) - ρ).im < 0 := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  have hDim : 0 < ((↑(0 : ℝ) + ((1 : ℝ) : ℂ) * I) - ρ).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  linear_combination log_neg_sub_im_neg ((↑(0 : ℝ) + ((0 : ℝ) : ℂ) * I) - ρ) hAim
    - log_neg_sub_im_pos ((↑(0 : ℝ) + ((1 : ℝ) : ℂ) * I) - ρ) hDim
/-- Winding number ONE: `∮_∂[1,3]×[0,2] (z-ρ)⁻¹ = 2πi` for `ρ` strictly
    inside.  Segment/log branch-split proof — the winding-NONZERO primitive. -/
theorem rect_winding_shifted (ρ : ℂ)
    (hre0 : (1 : ℝ) < ρ.re) (hre1 : ρ.re < 3)
    (him0 : (0 : ℝ) < ρ.im) (him1 : ρ.im < 2) :
    (∫ x in (1 : ℝ)..3, ((↑x + ((0 : ℝ) : ℂ) * I) - ρ)⁻¹)
        - (∫ x in (1 : ℝ)..3, ((↑x + ((2 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in (0 : ℝ)..2, ((((3 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (0 : ℝ)..2, ((((1 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I := by
  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - ρ).im ≠ 0) →
      (∫ x in (1 : ℝ)..3, ((↑x + c) - ρ)⁻¹)
        = Complex.log ((↑(3 : ℝ) + c) - ρ) - Complex.log ((↑(1 : ℝ) + c) - ρ) := by
    intro c hc
    have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) 3,
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
      I • (∫ y in (0 : ℝ)..2, ((c + ↑y * I) - ρ)⁻¹)
        = Complex.log ((c + ↑(2 : ℝ) * I) - ρ) - Complex.log ((c + ↑(0 : ℝ) * I) - ρ) := by
    intro c hslit
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 2,
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
  have hbot := horiz (((0 : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have htop := horiz (((2 : ℝ) : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have hright := vert ((3 : ℝ) : ℂ) (by
    intro y; rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith)
  have hleftJ : I • (∫ y in (0 : ℝ)..2, ((((1 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
      = Complex.log (ρ - (((1 : ℝ) : ℂ) + ↑(2 : ℝ) * I)) - Complex.log (ρ - (((1 : ℝ) : ℂ) + ↑(0 : ℝ) * I)) := by
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 2,
        HasDerivAt (fun y : ℝ => Complex.log (ρ - (((1 : ℝ) : ℂ) + ↑y * I)))
          (I • ((((1 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => ρ - (((1 : ℝ) : ℂ) + (↑y : ℂ) * I)) (-I) y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add (((1 : ℝ) : ℂ))).const_sub ρ
      have hslit : (ρ - (((1 : ℝ) : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith
      have hd := hpath.clog_real hslit
      have hval : (-I) / (ρ - (((1 : ℝ) : ℂ) + ↑y * I)) = I • ((((1 : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ := by
        rw [smul_eq_mul, div_eq_mul_inv,
          show ρ - (((1 : ℝ) : ℂ) + ↑y * I) = -((((1 : ℝ) : ℂ) + ↑y * I) - ρ) from by ring, inv_neg]
        ring
      rwa [hval] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    rw [sub_ne_zero]; intro h
    have : ((((1 : ℝ) : ℂ) + ↑y * I)).re = ρ.re := by rw [h]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this; linarith
  rw [hbot, htop, hright, hleftJ,
    show ρ - (((1 : ℝ) : ℂ) + ↑(2 : ℝ) * I) = -((↑(1 : ℝ) + ((2 : ℝ) : ℂ) * I) - ρ) from by ring,
    show ρ - (((1 : ℝ) : ℂ) + ↑(0 : ℝ) * I) = -((↑(1 : ℝ) + ((0 : ℝ) : ℂ) * I) - ρ) from by ring]
  have hAim : ((↑(1 : ℝ) + ((0 : ℝ) : ℂ) * I) - ρ).im < 0 := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  have hDim : 0 < ((↑(1 : ℝ) + ((2 : ℝ) : ℂ) * I) - ρ).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  linear_combination log_neg_sub_im_neg ((↑(1 : ℝ) + ((0 : ℝ) : ℂ) * I) - ρ) hAim
    - log_neg_sub_im_pos ((↑(1 : ℝ) + ((2 : ℝ) : ℂ) * I) - ρ) hDim

end RectWinding

/- Hand-written Lean (Task 5, Stage 2C): box argument principle for Lambda.
   Composes three kernel-verified atoms at box B = [2/5, 3/5] x [10, 35]:
     - the analytic E-term arg-principle (Bd(E) = 0 for holomorphic E),
     - the residue-sum linearity (Bd(sum divisor/(z-rho)) = 2*pi*I*sum divisor),
       whose per-pole winding is discharged from the box-B interior-pole primitive
       WindingCount.winding_lambda_five_rect_winding,
   together with the boundary split (H1) and the winding value (H4) as HYPOTHESES.

   conjecture1_proved = False.  This is the composition step; it does NOT prove RH. -/

import Mathlib
import WindingCount

open Complex intervalIntegral MeasureTheory Real

namespace BoxArgPrinciple

/-- Box-B analytic argument principle (E-term): the four-segment boundary integral
    of a function holomorphic on `[2/5, 3/5] x [10, 35]` vanishes.  Box-B instance
    of `RectArgumentPrinciple.rect_arg_principle_*`. -/
theorem rect_arg_principle_lambda (f : ℂ → ℂ)
    (H : DifferentiableOn ℂ f
      (Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) (35))) :
    (∫ x : ℝ in ((2 / 5) : ℝ)..(3 / 5), f (↑x + (((10) : ℝ) : ℂ) * I))
        - (∫ x : ℝ in ((2 / 5) : ℝ)..(3 / 5), f (↑x + (((35) : ℝ) : ℂ) * I))
        + I • (∫ y : ℝ in ((10) : ℝ)..(35), f ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y : ℝ in ((10) : ℝ)..(35), f ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) = 0 := by
  have key := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((((2 / 5) : ℝ) : ℂ) + (((10) : ℝ) : ℂ) * I) ((((3 / 5) : ℝ) : ℂ) + (((35) : ℝ) : ℂ) * I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at key
  norm_num at key ⊢
  exact key H

/-- Box-B residue-sum: the four-segment boundary integral of a Herglotz sum equals
    `2*pi*I * sum m`, using the per-pole winding primitive
    `WindingCount.winding_lambda_five_rect_winding` (H3 gives strict interior) and
    Finset linearity over the four sides.  Box-B instance of
    `BoxResidueSum.box_residue_sum_*` with `hwind` discharged internally. -/
theorem box_residue_sum_lambda {s : Finset ℂ} (m : ℂ → ℤ)
    (hin : ∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35)
    (hb : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (ht : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hr : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (hl : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) :
    (∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
        - (∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (m ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (m ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  rw [intervalIntegral.integral_finsetSum (fun ρ hρ => (hb ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (ht ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hr ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hl ρ hρ).const_mul (m ρ : ℂ))]
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨hre0, hre1, him0, him1⟩ := hin ρ hρ
  have hw := WindingCount.winding_lambda_five_rect_winding ρ hre0 hre1 him0 him1
  simp only [smul_eq_mul] at hw
  linear_combination (m ρ : ℂ) * hw

/-- **Box argument principle for Lambda (Stage 2C).**

    Let `Ld = Lambda'/Lambda` (as an abstract boundary function).  GIVEN
    - (H1) the boundary split of `Ld` into a residue part plus a holomorphic error
      `E`, stated as the four per-segment pointwise identities `hsplit_*`,
    - (H2) holomorphy of `E` on the closed box,
    - (H3) strict interiority of every pole `ρ ∈ s`,
    - (H4) the boundary winding value `Bd(Ld) = 2*pi*I*N` (from WindingCount),
    conclude that the total (multiplicity-weighted) pole count equals the winding:
      `∑ ρ ∈ s, (divisor ρ : ℂ) = N`.

    The split (H1) and E-holomorphy (H2) enter ONLY as hypotheses; N is generic.
    conjecture1_proved = False. -/
theorem box_arg_principle_lambda
    (Ld : ℂ → ℂ) (E : ℂ → ℂ) (s : Finset ℂ) (divisor : ℂ → ℤ) (N : ℂ)
    -- (H3) each pole strictly interior to B = [2/5, 3/5] x [10, 35]
    (hin : ∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35)
    -- IntervalIntegrable side-hypotheses of the residue sum (follow from H3;
    -- supplied here so the statement is self-contained over the boundary)
    (hb : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (ht : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hr : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (hl : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    -- (H2) E holomorphic on the closed box
    (hE : DifferentiableOn ℂ E
      (Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) (35)))
    -- (H1) boundary split of Ld into residues + E along the four sides
    (hsplit_b : ∀ x : ℝ, Ld (↑x + ((10 : ℝ) : ℂ) * I)
      = (∑ ρ ∈ s, (divisor ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) + E (↑x + ((10 : ℝ) : ℂ) * I))
    (hsplit_t : ∀ x : ℝ, Ld (↑x + ((35 : ℝ) : ℂ) * I)
      = (∑ ρ ∈ s, (divisor ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) + E (↑x + ((35 : ℝ) : ℂ) * I))
    (hsplit_r : ∀ y : ℝ, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I)
      = (∑ ρ ∈ s, (divisor ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) + E ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
    (hsplit_l : ∀ y : ℝ, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I)
      = (∑ ρ ∈ s, (divisor ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) + E ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
    -- integrability of the residue sums on each side (for splitting the integral of Ld)
    (hsb : IntervalIntegrable
      (fun x : ℝ => ∑ ρ ∈ s, (divisor ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hst : IntervalIntegrable
      (fun x : ℝ => ∑ ρ ∈ s, (divisor ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hsr : IntervalIntegrable
      (fun y : ℝ => ∑ ρ ∈ s, (divisor ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (hsl : IntervalIntegrable
      (fun y : ℝ => ∑ ρ ∈ s, (divisor ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    -- integrability of E on each side (for splitting the integral of Ld)
    (heb : IntervalIntegrable (fun x : ℝ => E (↑x + ((10 : ℝ) : ℂ) * I)) volume ((2 / 5)) ((3 / 5)))
    (het : IntervalIntegrable (fun x : ℝ => E (↑x + ((35 : ℝ) : ℂ) * I)) volume ((2 / 5)) ((3 / 5)))
    (her : IntervalIntegrable (fun y : ℝ => E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35))
    (hel : IntervalIntegrable (fun y : ℝ => E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35))
    -- (H4) the boundary winding value of Ld (from WindingCount) is 2*pi*I*N
    (hwind : (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((10 : ℝ) : ℂ) * I))
        - (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((35 : ℝ) : ℂ) * I))
        + I • (∫ y in (10 : ℝ)..35, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (10 : ℝ)..35, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * N) :
    (∑ ρ ∈ s, (divisor ρ : ℂ)) = N := by
  -- Rewrite each boundary integral of Ld via the split (H1) into residue + E.
  have eb : (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((10 : ℝ) : ℂ) * I))
      = (∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (divisor ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + (∫ x in ((2 / 5) : ℝ)..(3 / 5), E (↑x + ((10 : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add hsb heb]
    exact intervalIntegral.integral_congr (fun x _ => hsplit_b x)
  have et : (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((35 : ℝ) : ℂ) * I))
      = (∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (divisor ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + (∫ x in ((2 / 5) : ℝ)..(3 / 5), E (↑x + ((35 : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add hst het]
    exact intervalIntegral.integral_congr (fun x _ => hsplit_t x)
  have er : (∫ y in (10 : ℝ)..35, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
      = (∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (divisor ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        + (∫ y in (10 : ℝ)..35, E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) := by
    rw [← intervalIntegral.integral_add hsr her]
    exact intervalIntegral.integral_congr (fun y _ => hsplit_r y)
  have el : (∫ y in (10 : ℝ)..35, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = (∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (divisor ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        + (∫ y in (10 : ℝ)..35, E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) := by
    rw [← intervalIntegral.integral_add hsl hel]
    exact intervalIntegral.integral_congr (fun y _ => hsplit_l y)
  -- Bd(E) = 0 (analytic argument principle atom applied to H2).
  have hE0 := rect_arg_principle_lambda E hE
  -- Bd(residue sum) = 2*pi*I * sum divisor (residue-sum atom + per-pole winding).
  have hRes := box_residue_sum_lambda divisor hin hb ht hr hl
  -- Substitute the split into H4, cancel Bd(E) = 0, and match the residue winding.
  rw [eb, et, er, el, smul_add, smul_add] at hwind
  -- hwind now expands Bd(Ld) into (Bd(residues) + Bd(E)) telescoped over 4 sides.
  have key : 2 * π * I * (∑ ρ ∈ s, (divisor ρ : ℂ)) = 2 * π * I * N := by
    rw [← hRes]
    -- rearrange hwind: the E-terms cancel via hE0.
    linear_combination hwind - hE0
  -- Cancel the nonzero factor 2*pi*I.
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact mul_left_cancel₀ h2pi key

end BoxArgPrinciple

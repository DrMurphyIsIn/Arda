/- Task 7 (Stage 2B), capstone wiring: instantiate the box argument principle for `zeta'/zeta`
   with the KERNEL-DERIVED local Blaschke split.

   `box_arg_principle_lambda` (Task 5) is stated over an abstract boundary function `Ld` and takes
   BOTH the boundary split (H1) and the error-term holomorphy (H2) as hypotheses.  Task 7's
   `BlaschkeBox.zeta_blaschke_split_box` DERIVES the split and the E-holomorphy in-kernel for
   `Ld = logDeriv riemannZeta`.  This file discharges H1 AND H2 against that kernel lemma.

   * H2 (E holomorphic on the box): DISCHARGED IN-KERNEL.  `E`, its finite pole set `s`, the divisor
     `d`, and `DifferentiableOn ℂ E boxB` all come from `zeta_blaschke_split_box`.

   * H1 (the four per-segment boundary split identities): DERIVED from the kernel split.  The kernel
     split holds at every `z ∈ ball cB 13` with `zeta z ≠ 0`; the box boundary lies inside that ball,
     so H1 holds at every boundary point that is not a zeta zero.  The only remaining input is that
     the four boundary EDGES carry no zeta zero -- the SAME numeric/enclosure trust boundary as the
     Arb zero-enclosures feeding the winding count.  It enters here as the named boundary hypotheses
     `hnz_b/t/r/l` (documented, NOT faked; identical trust level to Stage-1 enclosures).

   Net effect vs Task 5: BOTH the split and the error holomorphy are now kernel-derived; the residual
   inputs are the boundary non-vanishing (Arb), the routine integrability, and the winding (Task 9).

   conjecture1_proved = False.  This composition step does NOT prove RH. -/
import Mathlib
import BoxArgPrinciple
import BlaschkeBox

open Complex MeasureTheory Real

namespace BoxArgPrincipleZeta

/-! ### Edge points of the box lie in the localization ball `ball cB 13`. -/

private theorem bottom_edge_mem {x : ℝ} (hx : x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5)) :
    (↑x + ((10 : ℝ) : ℂ) * I) ∈ Metric.ball BlaschkeBox.cB 13 := by
  apply BlaschkeBox.boxB_subset_ball
  rw [Set.uIcc_of_le (by norm_num)] at hx
  show _ ∈ Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) 35
  rw [Complex.mem_reProdIm]
  refine ⟨by simpa using hx, ?_⟩
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.ofReal_re,
    Complex.I_im]
  norm_num

private theorem top_edge_mem {x : ℝ} (hx : x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5)) :
    (↑x + ((35 : ℝ) : ℂ) * I) ∈ Metric.ball BlaschkeBox.cB 13 := by
  apply BlaschkeBox.boxB_subset_ball
  rw [Set.uIcc_of_le (by norm_num)] at hx
  show _ ∈ Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) 35
  rw [Complex.mem_reProdIm]
  refine ⟨by simpa using hx, ?_⟩
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.ofReal_re,
    Complex.I_im]
  norm_num

private theorem right_edge_mem {y : ℝ} (hy : y ∈ Set.uIcc ((10) : ℝ) 35) :
    ((((3 / 5) : ℝ) : ℂ) + ↑y * I) ∈ Metric.ball BlaschkeBox.cB 13 := by
  apply BlaschkeBox.boxB_subset_ball
  rw [Set.uIcc_of_le (by norm_num)] at hy
  show _ ∈ Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) 35
  rw [Complex.mem_reProdIm]
  refine ⟨?_, by simpa using hy⟩
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im]
  norm_num

private theorem left_edge_mem {y : ℝ} (hy : y ∈ Set.uIcc ((10) : ℝ) 35) :
    ((((2 / 5) : ℝ) : ℂ) + ↑y * I) ∈ Metric.ball BlaschkeBox.cB 13 := by
  apply BlaschkeBox.boxB_subset_ball
  rw [Set.uIcc_of_le (by norm_num)] at hy
  show _ ∈ Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) 35
  rw [Complex.mem_reProdIm]
  refine ⟨?_, by simpa using hy⟩
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im]
  norm_num

/-- Convert the kernel split at a point (`d ρ / (z - ρ)`) to the residue form of Task 5's boundary
    hypotheses (`d ρ * (z - ρ)⁻¹`). -/
private theorem split_residue_form
    (s : Finset ℂ) (d : ℂ → ℤ) (E : ℂ → ℂ) (z : ℂ)
    (h : logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) :
    logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) * (z - ρ)⁻¹) + E z := by
  rw [h]; simp only [div_eq_mul_inv]

/-- **Box argument principle for `zeta'/zeta`, with kernel-derived split AND error holomorphy.**

    `E`, its pole set `s`, the divisor `d`, and the error holomorphy on the box come from the kernel
    `BlaschkeBox.zeta_blaschke_split_box` (H2 kernel-discharged).  The four boundary split identities
    (H1) are DERIVED from the kernel split, using only that the four edges carry no zeta zero
    (`hnz_*`, the Arb-enclosure boundary input).  Given strict interiority (H3), the routine boundary
    integrability side-conditions, and the winding value (H4, from WindingCount / Task 9), the total
    multiplicity-weighted pole count equals the winding `N`.

    conjecture1_proved = False. -/
theorem box_arg_principle_zeta
    (N : ℂ) (s : Finset ℂ) (d : ℂ → ℤ) (E : ℂ → ℂ)
    -- the kernel split bundle (H1 source + H2).
    (hEholo : DifferentiableOn ℂ E BlaschkeBox.boxB)
    (hker : ∀ z ∈ Metric.ball BlaschkeBox.cB 13, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z)
    -- boundary non-vanishing on the four edges (Arb-enclosure trust boundary).
    (hnz_b : ∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((10 : ℝ) : ℂ) * I) ≠ 0)
    (hnz_t : ∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((35 : ℝ) : ℂ) * I) ≠ 0)
    (hnz_r : ∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0)
    (hnz_l : ∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0)
    -- H3: each pole strictly interior.
    (hin : ∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35)
    (hb : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (ht : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hr : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (hl : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    -- integrability of the residue sums and of E on each side (routine).
    (hsb : IntervalIntegrable
      (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hst : IntervalIntegrable
      (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5)))
    (hsr : IntervalIntegrable
      (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (hsl : IntervalIntegrable
      (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35))
    (heb : IntervalIntegrable (fun x : ℝ => E (↑x + ((10 : ℝ) : ℂ) * I)) volume ((2 / 5)) ((3 / 5)))
    (het : IntervalIntegrable (fun x : ℝ => E (↑x + ((35 : ℝ) : ℂ) * I)) volume ((2 / 5)) ((3 / 5)))
    (her : IntervalIntegrable (fun y : ℝ => E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35))
    (hel : IntervalIntegrable (fun y : ℝ => E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35))
    -- H4: the boundary winding value of `logDeriv zeta` (from WindingCount / Task 9).
    (hwind : (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((10 : ℝ) : ℂ) * I))
        - (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((35 : ℝ) : ℂ) * I))
        + I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * N) :
    (∑ ρ ∈ s, (d ρ : ℂ)) = N := by
  -- Per-edge interval split identities (H1), derived from the kernel split + boundary non-vanishing.
  -- Only the interval instance is needed (via `integral_congr`), sidestepping any `∀ x` obstruction.
  have hsp_b : ∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5),
      logDeriv riemannZeta (↑x + ((10 : ℝ) : ℂ) * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
          + E (↑x + ((10 : ℝ) : ℂ) * I) :=
    fun x hx => split_residue_form s d E _ (hker _ (bottom_edge_mem hx) (hnz_b x hx))
  have hsp_t : ∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5),
      logDeriv riemannZeta (↑x + ((35 : ℝ) : ℂ) * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
          + E (↑x + ((35 : ℝ) : ℂ) * I) :=
    fun x hx => split_residue_form s d E _ (hker _ (top_edge_mem hx) (hnz_t x hx))
  have hsp_r : ∀ y ∈ Set.uIcc ((10) : ℝ) 35,
      logDeriv riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
          + E ((((3 / 5) : ℝ) : ℂ) + ↑y * I) :=
    fun y hy => split_residue_form s d E _ (hker _ (right_edge_mem hy) (hnz_r y hy))
  have hsp_l : ∀ y ∈ Set.uIcc ((10) : ℝ) 35,
      logDeriv riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
          + E ((((2 / 5) : ℝ) : ℂ) + ↑y * I) :=
    fun y hy => split_residue_form s d E _ (hker _ (left_edge_mem hy) (hnz_l y hy))
  -- Inline Task 5's argument-principle composition, using the interval-restricted split.
  set Ld : ℂ → ℂ := logDeriv riemannZeta with hLd
  have eb : (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((10 : ℝ) : ℂ) * I))
      = (∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + (∫ x in ((2 / 5) : ℝ)..(3 / 5), E (↑x + ((10 : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add hsb heb]
    exact intervalIntegral.integral_congr (fun x hx => hsp_b x hx)
  have et : (∫ x in ((2 / 5) : ℝ)..(3 / 5), Ld (↑x + ((35 : ℝ) : ℂ) * I))
      = (∫ x in ((2 / 5) : ℝ)..(3 / 5), ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹)
        + (∫ x in ((2 / 5) : ℝ)..(3 / 5), E (↑x + ((35 : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add hst het]
    exact intervalIntegral.integral_congr (fun x hx => hsp_t x hx)
  have er : (∫ y in (10 : ℝ)..35, Ld ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
      = (∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (d ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        + (∫ y in (10 : ℝ)..35, E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) := by
    rw [← intervalIntegral.integral_add hsr her]
    exact intervalIntegral.integral_congr (fun y hy => hsp_r y hy)
  have el : (∫ y in (10 : ℝ)..35, Ld ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = (∫ y in (10 : ℝ)..35, ∑ ρ ∈ s, (d ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)
        + (∫ y in (10 : ℝ)..35, E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) := by
    rw [← intervalIntegral.integral_add hsl hel]
    exact intervalIntegral.integral_congr (fun y hy => hsp_l y hy)
  -- Bd(E) = 0 (analytic argument principle atom applied to H2, kernel-derived).
  have hE0 := BoxArgPrinciple.rect_arg_principle_lambda E hEholo
  -- Bd(residue sum) = 2*pi*I * sum divisor.
  have hRes := BoxArgPrinciple.box_residue_sum_lambda d hin hb ht hr hl
  rw [eb, et, er, el, smul_add, smul_add] at hwind
  have key : 2 * π * I * (∑ ρ ∈ s, (d ρ : ℂ)) = 2 * π * I * N := by
    rw [← hRes]
    linear_combination hwind - hE0
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact mul_left_cancel₀ h2pi key

/-- **Hypothesis-free-on-(H1,H2) box argument principle for `zeta'/zeta`.**

    Unlike `box_arg_principle_zeta`, this corollary does NOT take the split (H1) or the error
    holomorphy (H2) as free hypotheses: it OBTAINS the error `E`, the zero set `s`, the divisor `d`,
    `DifferentiableOn ℂ E boxB`, and the pointwise split directly from the kernel lemma
    `BlaschkeBox.zeta_blaschke_split_box`.  The conclusion existentially exposes the kernel's `s` and
    `d` so that the residual, purely-Arb inputs can be stated about them; those inputs are supplied
    by `hArb`, which -- crucially -- is applied to the kernel witnesses and therefore contains ONLY
    the honest non-kernel facts: edge non-vanishing (`hnz_*`, Arb enclosures), strict interiority of
    the zeros (H3), routine boundary integrability, and the winding value `N` (H4, from Task 9).  No
    split and no E-holomorphy appear among the residual inputs.

    conjecture1_proved = False. -/
theorem box_arg_principle_zeta' (N : ℂ)
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E BlaschkeBox.boxB →
      (∀ z ∈ Metric.ball BlaschkeBox.cB 13, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      -- edge non-vanishing (Arb enclosures)
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((10 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((35 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      -- H3: strict interiority
      (∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35) ∧
      -- residue-inverse integrability
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      -- residue-sum / E integrability
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((10 : ℝ) : ℂ) * I)) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((35 : ℝ) : ℂ) * I)) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35)) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35)) ∧
      -- H4: winding value
      ((∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((10 : ℝ) : ℂ) * I))
          - (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((35 : ℝ) : ℂ) * I))
          + I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * N)) :
    ∃ (s : Finset ℂ) (d : ℂ → ℤ), (∑ ρ ∈ s, (d ρ : ℂ)) = N := by
  -- Obtain the split (H1) and E-holomorphy (H2) FROM THE KERNEL LEMMA -- not as hypotheses.
  obtain ⟨E, s, d, hEholo, _, hker⟩ := BlaschkeBox.zeta_blaschke_split_box
  refine ⟨s, d, ?_⟩
  -- Feed the kernel witnesses to hArb to extract the purely-Arb residual facts.
  obtain ⟨hnz_b, hnz_t, hnz_r, hnz_l, hin, hb, ht, hr, hl,
          hsb, hst, hsr, hsl, heb, het, her, hel, hwind⟩ := hArb E s d hEholo hker
  exact box_arg_principle_zeta N s d E hEholo hker hnz_b hnz_t hnz_r hnz_l
    hin hb ht hr hl hsb hst hsr hsl heb het her hel hwind

end BoxArgPrincipleZeta

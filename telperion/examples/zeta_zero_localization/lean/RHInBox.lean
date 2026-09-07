/-  Task 3 (parameterized RH-in-a-box): the GENERIC capstone + the regression instantiation.

    `conjecture1_proved = False`.  This composes the corner/count-generic counting core
    (`RHInBoxCore.rh_in_box_core`, Task 1) with the variable-ball parameterized argument-principle
    count (`RHInBoxAnalytic.zeta_count_eq_winding_generic`, Task 2) into the ONE generic theorem
    `RHInBox.rh_in_box_of_certificate`, instantiable on ANY finite box `[sigma0,sigma1]x[T0,T1]` with
    ANY Blaschke ball `(c, R)` and ANY on-line-zero count `N`.

    It then proves the regression `RHInBox.rh_in_box_10_35`: the generic theorem, instantiated at the
    ORIGINAL merged box's values `sigma0=2/5, sigma1=3/5, T0=10, T1=35, c=cB, R=13, N=5` with `T` the
    five known on-line zeros, reproduces the SAME conclusion as the merged capstone
    `BoxLocalization.all_nontrivial_zeros_in_box_on_critical_line`.

    `N` is a FREE VARIABLE in the generic theorem; the regression fixes it to 5.

    conjecture1_proved = False.  This VERIFIES RH inside a box for supplied Arb data; it is NOT a
    proof of the Riemann Hypothesis. -/
import Mathlib
import RHInBoxCore        -- Task 1: rh_in_box_core
import RHInBoxAnalytic    -- Task 2: zeta_count_eq_winding_generic + zeroFinset
import BoxLocalization    -- zeta_zero_iff_completed_zero bridge + merged capstone (for regression)
import BlaschkeBox        -- cB / boxB for the regression instantiation

open Complex MeasureTheory Real
open scoped Topology

namespace RHInBox

/-! ## Part A: the generic capstone. -/

/-- **RH-in-a-box, fully generic capstone.**

    For ARBITRARY box corners `sigma0 sigma1 T0 T1 : R`, an ARBITRARY Blaschke ball `(c, R)` whose
    interior avoids `1` and contains the box, an ARBITRARY on-line-zero count `N : Z`, and an
    ARBITRARY Finset `T` of on-line zeros of `riemannZeta` inside the box whose cardinality matches
    the winding count `N`, together with the routine Arb boundary bundle `harb`: every zero of
    `riemannZeta` in the box lies on the critical line `Re = 1/2`.

    The proof composes the two prior atoms:
    * `zeta_count_eq_winding_generic` (Task 2) — KERNEL-derives the actual divisor `(s, d)` of
      `riemannZeta` over `ball c R`, its nonnegativity, its capture of every box zero, and
      `sum d = N` from the boundary winding `hwind`.  (The split + E-holomorphy are kernel-derived
      there, NOT assumed.)
    * `rh_in_box_core` (Task 1) — the corner/count-generic Finset counting argument: `T subset s`,
      `sum d = T.card`, and `d >= 1` on `s` force `s = T`, so every box zero (being in `s = T`) is
      on the line.

    Geometry enters only as `hRpos`/`hbox_ball`/`hs1` (and the box-ordering `hsig`/`hT`, discharged
    by `norm_num` at any concrete box).  `N` is FREE.

    conjecture1_proved = False. -/
theorem rh_in_box_of_certificate
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ)
    (hRpos : 0 < R)
    (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (T : Finset ℂ)
    (hTline : ∀ z ∈ T, z.re = 1 / 2)
    (hTzero : ∀ z ∈ T, riemannZeta z = 0)
    (hTbox : ∀ z ∈ T, (sigma0 ≤ z.re ∧ z.re ≤ sigma1) ∧ (T0 ≤ z.im ∧ z.im ≤ T1))
    (hwind : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
      = 2 * π * I * (N : ℂ))
    (harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset c R hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) →
      (∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (T0 : ℂ) * I)) volume sigma0 sigma1) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (T1 : ℂ) * I)) volume sigma0 sigma1) ∧
      (IntervalIntegrable (fun y : ℝ => E ((sigma1 : ℂ) + ↑y * I)) volume T0 T1) ∧
      (IntervalIntegrable (fun y : ℝ => E ((sigma0 : ℂ) + ↑y * I)) volume T0 T1))
    (hcount : (N : ℤ) = (T.card : ℤ)) :
    ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  obtain ⟨s, d, hd1, hzero_in, hsum⟩ :=
    RHInBoxAnalytic.zeta_count_eq_winding_generic
      sigma0 sigma1 T0 T1 c R N hRpos hsig hT hbox_ball hs1 hwind harb
  have hTsub : T ⊆ s := fun z hz =>
    hzero_in z (hTbox z hz).1 (hTbox z hz).2 (hTzero z hz)
  have hcount' : (∑ ρ ∈ s, d ρ) = (T.card : ℤ) := by rw [hsum, hcount]
  exact RHInBoxCore.rh_in_box_core sigma0 sigma1 T0 T1 s T d hd1 hTsub hTline hcount' hzero_in

/-! ## Part B: the regression instantiation on the original box `[2/5, 3/5] x [10, 35]`.

    We instantiate `rh_in_box_of_certificate` with the ORIGINAL merged box's parameters — corners
    `2/5, 3/5, 10, 35`, ball `(cB, 13)`, count `N = 5` — and supply the on-line Finset `T` as the
    five bridged on-line zeros from Stage 1 (`hLine`).  Geometry (`hRpos`/`hbox_ball`/`hs1`/
    `hsig`/`hT`) is discharged by `norm_num`/the merged `BlaschkeBox` facts.  The Arb bundle and
    winding value carry over verbatim from the merged `all_nontrivial_zeros_in_box_on_critical_line`
    input shape; the winding value `= 2*pi*I*5` supplies `hwind`, and `hcount : (5:Z) = T.card`
    holds because the five on-line zeros are distinct.

    The conclusion is DEFINITIONALLY the merged capstone's conclusion — this is the regression. -/

/-- **Regression: the generic capstone, instantiated on the original `[2/5,3/5]x[10,35]` box.**

    Takes the SAME two documented inputs the merged capstone
    `BoxLocalization.all_nontrivial_zeros_in_box_on_critical_line` takes: the Stage-1 on-line zeros
    `hLine` and the honest Arb bundle+winding `hArb` (at `N = 5`).  Concludes the SAME statement:
    every `riemannZeta` zero in `B = [2/5,3/5] x [10,35]` lies on `Re = 1/2`.

    Unlike the merged capstone (which routes through `box_localization_core` and
    `BoxArgPrincipleZeta.box_arg_principle_zeta`), this routes through the GENERIC
    `rh_in_box_of_certificate` with all box/ball/count parameters instantiated to the fixed values —
    demonstrating the generic theorem reproduces the fixed-box result.

    conjecture1_proved = False. -/
theorem rh_in_box_10_35
    (hLine : ∃ x1 x2 x3 x4 x5 : ℝ,
      (10 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 ≤ 35) ∧
      (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0))
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E BlaschkeBox.boxB →
      (∀ z ∈ Metric.ball BlaschkeBox.cB 13, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((10 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((35 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
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
      ((∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((10 : ℝ) : ℂ) * I))
          - (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((35 : ℝ) : ℂ) * I))
          + I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (5 : ℂ))) :
    (∀ ρ, (((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) → ((10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  -- Fixed-box geometry.
  have hRpos : (0 : ℝ) < 13 := by norm_num
  have hsig : ((2 / 5) : ℝ) ≤ (3 / 5) := by norm_num
  have hTle : ((10) : ℝ) ≤ 35 := by norm_num
  have hbox_ball : ∀ ρ : ℂ, (((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) →
      ((10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) → ρ ∈ Metric.ball BlaschkeBox.cB 13 :=
    fun ρ hre him => BoxLocalization.box_mem_ball hre him
  have hs1 : (1 : ℂ) ∉ Metric.ball BlaschkeBox.cB 13 := by
    intro hmem
    exact (BlaschkeBox.ball_subset_compl_one hmem) rfl
  -- Bridge the five on-line completed-zeta zeros to distinct on-line zeta zeros; build `T`.
  obtain ⟨x1, x2, x3, x4, x5, ⟨hx1lo, h12, h23, h34, h45, hx5hi⟩,
          hΛ1, hΛ2, hΛ3, hΛ4, hΛ5⟩ := hLine
  set z1 : ℂ := 1 / 2 + (x1 : ℂ) * Complex.I with hz1def
  set z2 : ℂ := 1 / 2 + (x2 : ℂ) * Complex.I with hz2def
  set z3 : ℂ := 1 / 2 + (x3 : ℂ) * Complex.I with hz3def
  set z4 : ℂ := 1 / 2 + (x4 : ℂ) * Complex.I with hz4def
  set z5 : ℂ := 1 / 2 + (x5 : ℂ) * Complex.I with hz5def
  have hre_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by
    intro t
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have him_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).im = t := by
    intro t
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have hzeta : ∀ (t : ℝ), completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 →
      riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 :=
    fun t h => BoxLocalization.line_zeta_zero_of_completed h
  set T : Finset ℂ := {z1, z2, z3, z4, z5} with hTdef
  -- The five points are strictly increasing in `Im`, hence distinct; `T.card = 5`.
  have distinct : ∀ (s' t : ℝ), s' < t →
      (1 / 2 + (s' : ℂ) * Complex.I) ≠ (1 / 2 + (t : ℂ) * Complex.I) := by
    intro s' t hst hEq
    have := congrArg Complex.im hEq
    rw [him_line s', him_line t] at this
    linarith
  have n12 : z1 ≠ z2 := distinct x1 x2 (by linarith)
  have n13 : z1 ≠ z3 := distinct x1 x3 (by linarith)
  have n14 : z1 ≠ z4 := distinct x1 x4 (by linarith)
  have n15 : z1 ≠ z5 := distinct x1 x5 (by linarith)
  have n23 : z2 ≠ z3 := distinct x2 x3 (by linarith)
  have n24 : z2 ≠ z4 := distinct x2 x4 (by linarith)
  have n25 : z2 ≠ z5 := distinct x2 x5 (by linarith)
  have n34 : z3 ≠ z4 := distinct x3 x4 (by linarith)
  have n35 : z3 ≠ z5 := distinct x3 x5 (by linarith)
  have n45 : z4 ≠ z5 := distinct x4 x5 (by linarith)
  have hTcard : T.card = 5 := by
    rw [hTdef]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n12, n13, n14, n15⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n23, n24, n25⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n34, n35⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]; exact n45)]
    simp
  -- `T`'s membership facts: on-line, zeta-zero, inside the box.
  have hmem_iff : ∀ z ∈ T, z = z1 ∨ z = z2 ∨ z = z3 ∨ z = z4 ∨ z = z5 := by
    intro z hz
    rw [hTdef] at hz
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    intro z hz
    rcases hmem_iff z hz with h | h | h | h | h <;> subst h <;>
      simp only [hz1def, hz2def, hz3def, hz4def, hz5def] <;> exact hre_line _
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    intro z hz
    rcases hmem_iff z hz with h | h | h | h | h <;> subst h <;>
      simp only [hz1def, hz2def, hz3def, hz4def, hz5def]
    · exact hzeta x1 hΛ1
    · exact hzeta x2 hΛ2
    · exact hzeta x3 hΛ3
    · exact hzeta x4 hΛ4
    · exact hzeta x5 hΛ5
  have hTbox : ∀ z ∈ T, (((2 / 5) : ℝ) ≤ z.re ∧ z.re ≤ (3 / 5)) ∧ ((10 : ℝ) ≤ z.im ∧ z.im ≤ 35) := by
    intro z hz
    rcases hmem_iff z hz with h | h | h | h | h <;> subst h <;>
      simp only [hz1def, hz2def, hz3def, hz4def, hz5def] <;>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      first
        | (rw [hre_line]; norm_num)
        | (rw [him_line]; linarith)
  -- Extract the winding value from the Arb bundle for `hwind`.  We feed the KERNEL `s`, `d`, `E`
  -- witnesses so that the generic `harb` — which is stated about exactly those witnesses — matches.
  -- The generic `harb` uses `s := zeroFinset cB 13 hs1`, `d := divisor riemannZeta (ball cB 13)`.
  set s0 : Finset ℂ := RHInBoxAnalytic.zeroFinset BlaschkeBox.cB 13 hs1 with hs0def
  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball BlaschkeBox.cB 13) : ℂ → ℤ)
    with hd0def
  -- The winding value: extract it from `hArb` applied to the kernel split (which exists).
  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball ((2 / 5) : ℝ) (3 / 5) (10) 35
      BlaschkeBox.cB 13 hRpos hbox_ball hs1
  -- `hE0holo` is over `Icc ×ℂ Icc = boxB`.
  have hE0boxB : DifferentiableOn ℂ E0 BlaschkeBox.boxB := hE0holo
  have hker0' : ∀ z ∈ Metric.ball BlaschkeBox.cB 13, riemannZeta z ≠ 0 →
      logDeriv riemannZeta z = (∑ ρ ∈ s0, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by
    intro z hz hnz
    have := hker0 z hz hnz
    rw [hs0def, hd0def]; exact this
  obtain ⟨hnz_b, hnz_t, hnz_r, hnz_l, hin, hb, ht, hr, hl,
          hsb, hst, hsr, hsl, heb, het, her, hel, hwind5⟩ :=
    hArb E0 s0 d0 hE0boxB hker0'
  -- Assemble `hwind : ... = 2*pi*I*(5:C)` in the shape the generic theorem expects
  -- (corners as real casts `(10:R):C`, `(35:R):C`, `((3/5):R):C`, `((2/5):R):C`).
  have hwind : (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + (((10 : ℝ)) : ℂ) * I))
        - (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + (((35 : ℝ)) : ℂ) * I))
        + I • (∫ y in ((10 : ℝ))..35, logDeriv riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((10 : ℝ))..35, logDeriv riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((5 : ℤ) : ℂ) := by
    rw [show (((5 : ℤ) : ℂ)) = (5 : ℂ) by norm_num]; exact hwind5
  -- Assemble the generic `harb` bundle at the kernel witnesses.
  have harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset BlaschkeBox.cB 13 hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball BlaschkeBox.cB 13) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) 35) →
      (∀ z ∈ Metric.ball BlaschkeBox.cB 13, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + (((10 : ℝ)) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + (((35 : ℝ)) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((10 : ℝ)) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((35 : ℝ)) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((10 : ℝ)) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((35 : ℝ)) : ℂ) * I) - ρ)⁻¹) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (10) (35)) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((10 : ℝ)) : ℂ) * I)) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((35 : ℝ)) : ℂ) * I)) volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35)) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) volume (10) (35)) := by
    intro E s d hEholo hkerE
    have hfull := hArb E s d hEholo hkerE
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1,
      hfull.2.2.2.2.2.1, hfull.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.1,
      hfull.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.1,
      hfull.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  -- Instantiate the generic capstone at the fixed box.
  have hcount5 : (5 : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num
  exact rh_in_box_of_certificate ((2 / 5) : ℝ) (3 / 5) (10) 35 BlaschkeBox.cB 13 5
    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcount5

end RHInBox

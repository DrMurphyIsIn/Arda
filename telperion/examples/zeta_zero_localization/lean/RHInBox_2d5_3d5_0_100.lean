/-  Per-box instantiation of `RHInBox.rh_in_box_of_certificate` on the box
    `[(2 / 5),(3 / 5)] x [0,100]` with `N = 29` on-line zeros.

    Emitted by telperion `emit_per_box_instantiation` (Task 4 driver `--box`/`--height`).
    Geometry: ball center `c = ((1 / 2)) + (50)*I`, radius `R = Real.sqrt ((250013 / 100))`,
    chosen so the box is STRICTLY inside the ball and the pole `s = 1` is STRICTLY outside.
    The winding count `N` and on-line zeros are the documented Arb non-kernel inputs
    (supplied as the `hArb`/`hLine` hypotheses).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import RHInBoxAnalytic
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 400000

namespace RHInBox_2d5_3d5_0_100

/-- Chosen Blaschke ball center for the box `[(2 / 5),(3 / 5)] x [0,100]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (50)⟩

/-- Chosen Blaschke ball radius (squared radius `(250013 / 100)`). -/
noncomputable def RPB : ℝ := Real.sqrt ((250013 / 100))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- **RH-in-a-box on `[(2 / 5),(3 / 5)] x [0,100]` with `N = 29`.**  Instantiates the generic
    `RHInBox.rh_in_box_of_certificate` at this box's corners, chosen Blaschke ball
    `c = ((1 / 2)) + (50)*I`, `R = Real.sqrt ((250013 / 100))`, and count `N = 29`.  Takes the
    documented Arb inputs `hLine` (the 29 on-line zeros) and `hArb` (boundary bundle +
    winding `= 2*pi*I*29`).  conjecture1_proved = False. -/
theorem rh_in_box_2d5_3d5_0_100
    (hLine : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : ℝ,
      (0 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 ≤ 100) ∧
      (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x6 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x7 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x8 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x9 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x10 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x11 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x12 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x13 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x14 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x15 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x16 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x17 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x18 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x19 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x20 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x21 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x22 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x23 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x24 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x25 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x26 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x27 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x28 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x29 : ℂ) * Complex.I) = 0))
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((2 / 5)) : ℝ) ((3 / 5)) ×ℂ Set.Icc ((0) : ℝ) (100)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((2 / 5)) : ℝ) ((3 / 5)), riemannZeta (↑x + (((0) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((2 / 5)) : ℝ) ((3 / 5)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((3 / 5)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((2 / 5)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((2 / 5)) : ℝ) < ρ.re ∧ ρ.re < ((3 / 5)) ∧ ((0) : ℝ) < ρ.im ∧ ρ.im < (100)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((3 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((2 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((3 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((2 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((0) : ℝ) : ℂ) * I)) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((3 / 5)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((2 / 5)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      ((∫ x in (((2 / 5)) : ℝ)..((3 / 5)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
          - (∫ x in (((2 / 5)) : ℝ)..((3 / 5)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
          + I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((3 / 5)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((2 / 5)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (29 : ℂ))) :
    (∀ ρ, ((((2 / 5)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3 / 5))) → (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hsig : (((2 / 5)) : ℝ) ≤ ((3 / 5)) := by norm_num
  have hTle : ((0) : ℝ) ≤ (100) := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((((2 / 5)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3 / 5))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (50))]
  have hs1 : (1 : ℂ) ∉ Metric.ball cPB RPB := by
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    intro hlt
    simp only [Complex.one_re, Complex.one_im] at hlt
    have hle : Real.sqrt ((250013 / 100)) ≤
        Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (50)) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    linarith [hlt, hle]
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, ⟨hlo, hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hhi⟩, hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7, hΛ8, hΛ9, hΛ10, hΛ11, hΛ12, hΛ13, hΛ14, hΛ15, hΛ16, hΛ17, hΛ18, hΛ19, hΛ20, hΛ21, hΛ22, hΛ23, hΛ24, hΛ25, hΛ26, hΛ27, hΛ28, hΛ29⟩ := hLine
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
  set xsL : List ℝ := [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29] with hxsdef
  have hchain : xsL.IsChain (· < ·) := by
    rw [hxsdef]
    simp only [List.isChain_cons_cons]
    exact ⟨hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, List.IsChain.singleton _⟩
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = 29 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hxsdef]
    rfl
  have hmem_list : ∀ t ∈ xsL, t = x1 ∨ t = x2 ∨ t = x3 ∨ t = x4 ∨ t = x5 ∨ t = x6 ∨ t = x7 ∨ t = x8 ∨ t = x9 ∨ t = x10 ∨ t = x11 ∨ t = x12 ∨ t = x13 ∨ t = x14 ∨ t = x15 ∨ t = x16 ∨ t = x17 ∨ t = x18 ∨ t = x19 ∨ t = x20 ∨ t = x21 ∨ t = x22 ∨ t = x23 ∨ t = x24 ∨ t = x25 ∨ t = x26 ∨ t = x27 ∨ t = x28 ∨ t = x29 := by
    intro t ht
    rw [hxsdef] at ht
    simpa using ht
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    intro t ht
    rcases hmem_list t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hzeta _ hΛ1
    · exact hzeta _ hΛ2
    · exact hzeta _ hΛ3
    · exact hzeta _ hΛ4
    · exact hzeta _ hΛ5
    · exact hzeta _ hΛ6
    · exact hzeta _ hΛ7
    · exact hzeta _ hΛ8
    · exact hzeta _ hΛ9
    · exact hzeta _ hΛ10
    · exact hzeta _ hΛ11
    · exact hzeta _ hΛ12
    · exact hzeta _ hΛ13
    · exact hzeta _ hΛ14
    · exact hzeta _ hΛ15
    · exact hzeta _ hΛ16
    · exact hzeta _ hΛ17
    · exact hzeta _ hΛ18
    · exact hzeta _ hΛ19
    · exact hzeta _ hΛ20
    · exact hzeta _ hΛ21
    · exact hzeta _ hΛ22
    · exact hzeta _ hΛ23
    · exact hzeta _ hΛ24
    · exact hzeta _ hΛ25
    · exact hzeta _ hΛ26
    · exact hzeta _ hΛ27
    · exact hzeta _ hΛ28
    · exact hzeta _ hΛ29
  have hTbox : ∀ z ∈ T, ((((2 / 5)) : ℝ) ≤ z.re ∧ z.re ≤ ((3 / 5))) ∧ (((0) : ℝ) ≤ z.im ∧ z.im ≤ (100)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    intro t ht
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hre_line]; norm_num
    · rw [hre_line]; norm_num
    · rw [him_line]
      rcases hmem_list t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
    · rw [him_line]
      rcases hmem_list t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
  set s0f : Finset ℂ := RHInBoxAnalytic.zeroFinset cPB RPB hs1 with hs0def
  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ) with hd0def
  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (((2 / 5)) : ℝ) ((3 / 5)) (0) (100) cPB RPB hRpos hbox_ball hs1
  have hE0box : DifferentiableOn ℂ E0 (Set.Icc (((2 / 5)) : ℝ) ((3 / 5)) ×ℂ Set.Icc ((0) : ℝ) (100)) := hE0holo
  have hker0' : ∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
      logDeriv riemannZeta z = (∑ ρ ∈ s0f, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by
    intro z hz hnz
    have := hker0 z hz hnz
    rw [hs0def, hd0def]; exact this
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hwindA⟩ := hArb E0 s0f d0 hE0box hker0'
  have hwind : (∫ x in (((2 / 5)) : ℝ)..((3 / 5)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
        - (∫ x in (((2 / 5)) : ℝ)..((3 / 5)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
        + I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((3 / 5)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((2 / 5)) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((29 : ℤ) : ℂ) := by
    rw [show (((29 : ℤ) : ℂ)) = (29 : ℂ) by norm_num]; exact hwindA
  have harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc (((2 / 5)) : ℝ) ((3 / 5)) ×ℂ Set.Icc ((0) : ℝ) (100)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((2 / 5)) : ℝ) ((3 / 5)), riemannZeta (↑x + (((0) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((2 / 5)) : ℝ) ((3 / 5)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((3 / 5)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((2 / 5)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((2 / 5)) : ℝ) < ρ.re ∧ ρ.re < ((3 / 5)) ∧ ((0) : ℝ) < ρ.im ∧ ρ.im < (100)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((3 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((2 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((3 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((2 / 5)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((0) : ℝ) : ℂ) * I)) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((2 / 5))) (((3 / 5)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((3 / 5)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((2 / 5)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) := by
    intro E s d hEholo hkerE
    have hfull := hArb E s d hEholo hkerE
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1, hfull.2.2.2.2.2.1, hfull.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hcountN : (29 : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num
  exact RHInBox.rh_in_box_of_certificate (((2 / 5)) : ℝ) ((3 / 5)) (0) (100) cPB RPB 29
    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcountN

end RHInBox_2d5_3d5_0_100

/-  Per-box instantiation of `RHInBox.rh_in_box_of_certificate` on the box
    `[(1 / 2000000),(1999999 / 2000000)] x [400,450]` with `N = 33` on-line zeros.

    Emitted by telperion `emit_per_box_instantiation` (Task 4 driver `--box`/`--height`).
    Geometry: ball center `c = ((1 / 2)) + (425)*I`, radius `R = Real.sqrt ((725001999998000001 / 8000000000000))`,
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

namespace RHInBox_1d2000000_1999999d2000000_400_450

/-- Chosen Blaschke ball center for the box `[(1 / 2000000),(1999999 / 2000000)] x [400,450]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (425)⟩

/-- Chosen Blaschke ball radius (squared radius `(725001999998000001 / 8000000000000)`). -/
noncomputable def RPB : ℝ := Real.sqrt ((725001999998000001 / 8000000000000))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- **RH-in-a-box on `[(1 / 2000000),(1999999 / 2000000)] x [400,450]` with `N = 33`.**  Instantiates the generic
    `RHInBox.rh_in_box_of_certificate` at this box's corners, chosen Blaschke ball
    `c = ((1 / 2)) + (425)*I`, `R = Real.sqrt ((725001999998000001 / 8000000000000))`, and count `N = 33`.  Takes the
    documented Arb inputs `hLine` (the 33 on-line zeros) and `hArb` (boundary bundle +
    winding `= 2*pi*I*33`).  conjecture1_proved = False. -/
theorem rh_in_box_1d2000000_1999999d2000000_400_450
    (hLine : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 : ℝ,
      (400 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 ≤ 450) ∧
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
       completedRiemannZeta (1 / 2 + (x29 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x30 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x31 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x32 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x33 : ℂ) * Complex.I) = 0))
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((400) : ℝ) (450)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((400) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((450) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((400) : ℝ) (450), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((400) : ℝ) (450), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((400) : ℝ) < ρ.im ∧ ρ.im < (450)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((450) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((450) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((400) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((450) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((400)) ((450))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((400)) ((450))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((400) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((450) : ℝ) : ℂ) * I))
          + I • (∫ y in ((400) : ℝ)..(450), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((400) : ℝ)..(450), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (33 : ℂ))) :
    (∀ ρ, ((((1 / 2000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1999999 / 2000000))) → (((400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (450)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hsig : (((1 / 2000000)) : ℝ) ≤ ((1999999 / 2000000)) := by norm_num
  have hTle : ((400) : ℝ) ≤ (450) := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((((1 / 2000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1999999 / 2000000))) →
      (((400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (450)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (425))]
  have hs1 : (1 : ℂ) ∉ Metric.ball cPB RPB := by
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    intro hlt
    simp only [Complex.one_re, Complex.one_im] at hlt
    have hle : Real.sqrt ((725001999998000001 / 8000000000000)) ≤
        Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (425)) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    linarith [hlt, hle]
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, ⟨hlo, hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, hhi⟩, hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7, hΛ8, hΛ9, hΛ10, hΛ11, hΛ12, hΛ13, hΛ14, hΛ15, hΛ16, hΛ17, hΛ18, hΛ19, hΛ20, hΛ21, hΛ22, hΛ23, hΛ24, hΛ25, hΛ26, hΛ27, hΛ28, hΛ29, hΛ30, hΛ31, hΛ32, hΛ33⟩ := hLine
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
  set xsL : List ℝ := [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33] with hxsdef
  have hchain : xsL.IsChain (· < ·) := by
    rw [hxsdef]
    simp only [List.isChain_cons_cons]
    exact ⟨hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, List.IsChain.singleton _⟩
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = 33 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hxsdef]
    rfl
  have hb1 : ((400) : ℝ) ≤ x1 := hlo
  have hb2 : ((400) : ℝ) ≤ x2 := le_trans hb1 (le_of_lt hc12)
  have hb3 : ((400) : ℝ) ≤ x3 := le_trans hb2 (le_of_lt hc23)
  have hb4 : ((400) : ℝ) ≤ x4 := le_trans hb3 (le_of_lt hc34)
  have hb5 : ((400) : ℝ) ≤ x5 := le_trans hb4 (le_of_lt hc45)
  have hb6 : ((400) : ℝ) ≤ x6 := le_trans hb5 (le_of_lt hc56)
  have hb7 : ((400) : ℝ) ≤ x7 := le_trans hb6 (le_of_lt hc67)
  have hb8 : ((400) : ℝ) ≤ x8 := le_trans hb7 (le_of_lt hc78)
  have hb9 : ((400) : ℝ) ≤ x9 := le_trans hb8 (le_of_lt hc89)
  have hb10 : ((400) : ℝ) ≤ x10 := le_trans hb9 (le_of_lt hc910)
  have hb11 : ((400) : ℝ) ≤ x11 := le_trans hb10 (le_of_lt hc1011)
  have hb12 : ((400) : ℝ) ≤ x12 := le_trans hb11 (le_of_lt hc1112)
  have hb13 : ((400) : ℝ) ≤ x13 := le_trans hb12 (le_of_lt hc1213)
  have hb14 : ((400) : ℝ) ≤ x14 := le_trans hb13 (le_of_lt hc1314)
  have hb15 : ((400) : ℝ) ≤ x15 := le_trans hb14 (le_of_lt hc1415)
  have hb16 : ((400) : ℝ) ≤ x16 := le_trans hb15 (le_of_lt hc1516)
  have hb17 : ((400) : ℝ) ≤ x17 := le_trans hb16 (le_of_lt hc1617)
  have hb18 : ((400) : ℝ) ≤ x18 := le_trans hb17 (le_of_lt hc1718)
  have hb19 : ((400) : ℝ) ≤ x19 := le_trans hb18 (le_of_lt hc1819)
  have hb20 : ((400) : ℝ) ≤ x20 := le_trans hb19 (le_of_lt hc1920)
  have hb21 : ((400) : ℝ) ≤ x21 := le_trans hb20 (le_of_lt hc2021)
  have hb22 : ((400) : ℝ) ≤ x22 := le_trans hb21 (le_of_lt hc2122)
  have hb23 : ((400) : ℝ) ≤ x23 := le_trans hb22 (le_of_lt hc2223)
  have hb24 : ((400) : ℝ) ≤ x24 := le_trans hb23 (le_of_lt hc2324)
  have hb25 : ((400) : ℝ) ≤ x25 := le_trans hb24 (le_of_lt hc2425)
  have hb26 : ((400) : ℝ) ≤ x26 := le_trans hb25 (le_of_lt hc2526)
  have hb27 : ((400) : ℝ) ≤ x27 := le_trans hb26 (le_of_lt hc2627)
  have hb28 : ((400) : ℝ) ≤ x28 := le_trans hb27 (le_of_lt hc2728)
  have hb29 : ((400) : ℝ) ≤ x29 := le_trans hb28 (le_of_lt hc2829)
  have hb30 : ((400) : ℝ) ≤ x30 := le_trans hb29 (le_of_lt hc2930)
  have hb31 : ((400) : ℝ) ≤ x31 := le_trans hb30 (le_of_lt hc3031)
  have hb32 : ((400) : ℝ) ≤ x32 := le_trans hb31 (le_of_lt hc3132)
  have hb33 : ((400) : ℝ) ≤ x33 := le_trans hb32 (le_of_lt hc3233)
  have hu33 : x33 ≤ ((450) : ℝ) := hhi
  have hu32 : x32 ≤ ((450) : ℝ) := le_trans (le_of_lt hc3233) hu33
  have hu31 : x31 ≤ ((450) : ℝ) := le_trans (le_of_lt hc3132) hu32
  have hu30 : x30 ≤ ((450) : ℝ) := le_trans (le_of_lt hc3031) hu31
  have hu29 : x29 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2930) hu30
  have hu28 : x28 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2829) hu29
  have hu27 : x27 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2728) hu28
  have hu26 : x26 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2627) hu27
  have hu25 : x25 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2526) hu26
  have hu24 : x24 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2425) hu25
  have hu23 : x23 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2324) hu24
  have hu22 : x22 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2223) hu23
  have hu21 : x21 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2122) hu22
  have hu20 : x20 ≤ ((450) : ℝ) := le_trans (le_of_lt hc2021) hu21
  have hu19 : x19 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1920) hu20
  have hu18 : x18 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1819) hu19
  have hu17 : x17 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1718) hu18
  have hu16 : x16 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1617) hu17
  have hu15 : x15 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1516) hu16
  have hu14 : x14 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1415) hu15
  have hu13 : x13 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1314) hu14
  have hu12 : x12 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1213) hu13
  have hu11 : x11 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1112) hu12
  have hu10 : x10 ≤ ((450) : ℝ) := le_trans (le_of_lt hc1011) hu11
  have hu9 : x9 ≤ ((450) : ℝ) := le_trans (le_of_lt hc910) hu10
  have hu8 : x8 ≤ ((450) : ℝ) := le_trans (le_of_lt hc89) hu9
  have hu7 : x7 ≤ ((450) : ℝ) := le_trans (le_of_lt hc78) hu8
  have hu6 : x6 ≤ ((450) : ℝ) := le_trans (le_of_lt hc67) hu7
  have hu5 : x5 ≤ ((450) : ℝ) := le_trans (le_of_lt hc56) hu6
  have hu4 : x4 ≤ ((450) : ℝ) := le_trans (le_of_lt hc45) hu5
  have hu3 : x3 ≤ ((450) : ℝ) := le_trans (le_of_lt hc34) hu4
  have hu2 : x2 ≤ ((450) : ℝ) := le_trans (le_of_lt hc23) hu3
  have hu1 : x1 ≤ ((450) : ℝ) := le_trans (le_of_lt hc12) hu2
  have hre_lo : (((1 / 2000000)) : ℝ) ≤ 1 / 2 := by norm_num
  have hre_hi : (1 / 2 : ℝ) ≤ ((1999999 / 2000000)) := by norm_num
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    rw [hxsdef]
    simp only [List.forall_mem_cons]
    exact ⟨hzeta x1 hΛ1, hzeta x2 hΛ2, hzeta x3 hΛ3, hzeta x4 hΛ4, hzeta x5 hΛ5, hzeta x6 hΛ6, hzeta x7 hΛ7, hzeta x8 hΛ8, hzeta x9 hΛ9, hzeta x10 hΛ10, hzeta x11 hΛ11, hzeta x12 hΛ12, hzeta x13 hΛ13, hzeta x14 hΛ14, hzeta x15 hΛ15, hzeta x16 hΛ16, hzeta x17 hΛ17, hzeta x18 hΛ18, hzeta x19 hΛ19, hzeta x20 hΛ20, hzeta x21 hΛ21, hzeta x22 hΛ22, hzeta x23 hΛ23, hzeta x24 hΛ24, hzeta x25 hΛ25, hzeta x26 hΛ26, hzeta x27 hΛ27, hzeta x28 hΛ28, hzeta x29 hΛ29, hzeta x30 hΛ30, hzeta x31 hΛ31, hzeta x32 hΛ32, hzeta x33 hΛ33, List.forall_mem_nil _⟩
  have hTbox : ∀ z ∈ T, ((((1 / 2000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((1999999 / 2000000))) ∧ (((400) : ℝ) ≤ z.im ∧ z.im ≤ (450)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    rw [hxsdef]
    simp only [List.forall_mem_cons]
    exact ⟨⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb1, by rw [him_line]; exact hu1⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb2, by rw [him_line]; exact hu2⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb3, by rw [him_line]; exact hu3⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb4, by rw [him_line]; exact hu4⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb5, by rw [him_line]; exact hu5⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb6, by rw [him_line]; exact hu6⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb7, by rw [him_line]; exact hu7⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb8, by rw [him_line]; exact hu8⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb9, by rw [him_line]; exact hu9⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb10, by rw [him_line]; exact hu10⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb11, by rw [him_line]; exact hu11⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb12, by rw [him_line]; exact hu12⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb13, by rw [him_line]; exact hu13⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb14, by rw [him_line]; exact hu14⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb15, by rw [him_line]; exact hu15⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb16, by rw [him_line]; exact hu16⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb17, by rw [him_line]; exact hu17⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb18, by rw [him_line]; exact hu18⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb19, by rw [him_line]; exact hu19⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb20, by rw [him_line]; exact hu20⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb21, by rw [him_line]; exact hu21⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb22, by rw [him_line]; exact hu22⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb23, by rw [him_line]; exact hu23⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb24, by rw [him_line]; exact hu24⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb25, by rw [him_line]; exact hu25⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb26, by rw [him_line]; exact hu26⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb27, by rw [him_line]; exact hu27⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb28, by rw [him_line]; exact hu28⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb29, by rw [him_line]; exact hu29⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb30, by rw [him_line]; exact hu30⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb31, by rw [him_line]; exact hu31⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb32, by rw [him_line]; exact hu32⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb33, by rw [him_line]; exact hu33⟩, List.forall_mem_nil _⟩
  set s0f : Finset ℂ := RHInBoxAnalytic.zeroFinset cPB RPB hs1 with hs0def
  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ) with hd0def
  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) (400) (450) cPB RPB hRpos hbox_ball hs1
  have hE0box : DifferentiableOn ℂ E0 (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((400) : ℝ) (450)) := hE0holo
  have hker0' : ∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
      logDeriv riemannZeta z = (∑ ρ ∈ s0f, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by
    intro z hz hnz
    have := hker0 z hz hnz
    rw [hs0def, hd0def]; exact this
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hwindA⟩ := hArb E0 s0f d0 hE0box hker0'
  have hwind : (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((400) : ℝ) : ℂ) * I))
        - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((450) : ℝ) : ℂ) * I))
        + I • (∫ y in ((400) : ℝ)..(450), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((400) : ℝ)..(450), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((33 : ℤ) : ℂ) := by
    rw [show (((33 : ℤ) : ℂ)) = (33 : ℂ) by norm_num]; exact hwindA
  have harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((400) : ℝ) (450)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((400) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((450) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((400) : ℝ) (450), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((400) : ℝ) (450), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((400) : ℝ) < ρ.im ∧ ρ.im < (450)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((450) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((450) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((450))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((400) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((450) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((400)) ((450))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((400)) ((450))) := by
    intro E s d hEholo hkerE
    have hfull := hArb E s d hEholo hkerE
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1, hfull.2.2.2.2.2.1, hfull.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hcountN : (33 : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num
  exact RHInBox.rh_in_box_of_certificate (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) (400) (450) cPB RPB 33
    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcountN

end RHInBox_1d2000000_1999999d2000000_400_450

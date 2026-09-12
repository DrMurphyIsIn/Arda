/-  Per-box instantiation of `RHInBox.rh_in_box_of_certificate` on the box
    `[(1 / 4000000),(3999999 / 4000000)] x [12966,13000]` with `N = 41` on-line zeros.

    Emitted by telperion `emit_per_box_instantiation` (Task 4 driver `--box`/`--height`).
    Geometry: ball center `c = ((1 / 2)) + (12983)*I`, radius `R = Real.sqrt ((2696937255999996000001 / 32000000000000))`,
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

namespace RHInBox_1d4000000_3999999d4000000_12966_13000

/-- Chosen Blaschke ball center for the box `[(1 / 4000000),(3999999 / 4000000)] x [12966,13000]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (12983)⟩

/-- Chosen Blaschke ball radius (squared radius `(2696937255999996000001 / 32000000000000)`). -/
noncomputable def RPB : ℝ := Real.sqrt ((2696937255999996000001 / 32000000000000))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- **RH-in-a-box on `[(1 / 4000000),(3999999 / 4000000)] x [12966,13000]` with `N = 41`.**  Instantiates the generic
    `RHInBox.rh_in_box_of_certificate` at this box's corners, chosen Blaschke ball
    `c = ((1 / 2)) + (12983)*I`, `R = Real.sqrt ((2696937255999996000001 / 32000000000000))`, and count `N = 41`.  Takes the
    documented Arb inputs `hLine` (the 41 on-line zeros) and `hArb` (boundary bundle +
    winding `= 2*pi*I*41`).  conjecture1_proved = False. -/
theorem rh_in_box_1d4000000_3999999d4000000_12966_13000
    (hLine : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 : ℝ,
      (12966 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 ≤ 13000) ∧
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
       completedRiemannZeta (1 / 2 + (x33 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x34 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x35 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x36 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x37 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x38 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x39 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x40 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x41 : ℂ) * Complex.I) = 0))
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) ×ℂ Set.Icc ((12966) : ℝ) (13000)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 4000000)) : ℝ) ((3999999 / 4000000)), riemannZeta (↑x + (((12966) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 4000000)) : ℝ) ((3999999 / 4000000)), riemannZeta (↑x + (((13000) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((12966) : ℝ) (13000), riemannZeta (((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((12966) : ℝ) (13000), riemannZeta (((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 4000000)) : ℝ) < ρ.re ∧ ρ.re < ((3999999 / 4000000)) ∧ ((12966) : ℝ) < ρ.im ∧ ρ.im < (13000)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((12966) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((13000) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((12966) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((13000) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((12966) : ℝ) : ℂ) * I)) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((13000) : ℝ) : ℂ) * I)) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I)) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I)) volume ((12966)) ((13000))) ∧
      ((∫ x in (((1 / 4000000)) : ℝ)..((3999999 / 4000000)), logDeriv riemannZeta (↑x + (((12966) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 4000000)) : ℝ)..((3999999 / 4000000)), logDeriv riemannZeta (↑x + (((13000) : ℝ) : ℂ) * I))
          + I • (∫ y in ((12966) : ℝ)..(13000), logDeriv riemannZeta (((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((12966) : ℝ)..(13000), logDeriv riemannZeta (((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (41 : ℂ))) :
    (∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) → (((12966) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (13000)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hsig : (((1 / 4000000)) : ℝ) ≤ ((3999999 / 4000000)) := by norm_num
  have hTle : ((12966) : ℝ) ≤ (13000) := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((12966) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (13000)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (12983))]
  have hs1 : (1 : ℂ) ∉ Metric.ball cPB RPB := by
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    intro hlt
    simp only [Complex.one_re, Complex.one_im] at hlt
    have hle : Real.sqrt ((2696937255999996000001 / 32000000000000)) ≤
        Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (12983)) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    linarith [hlt, hle]
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, ⟨hlo, hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, hc3334, hc3435, hc3536, hc3637, hc3738, hc3839, hc3940, hc4041, hhi⟩, hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7, hΛ8, hΛ9, hΛ10, hΛ11, hΛ12, hΛ13, hΛ14, hΛ15, hΛ16, hΛ17, hΛ18, hΛ19, hΛ20, hΛ21, hΛ22, hΛ23, hΛ24, hΛ25, hΛ26, hΛ27, hΛ28, hΛ29, hΛ30, hΛ31, hΛ32, hΛ33, hΛ34, hΛ35, hΛ36, hΛ37, hΛ38, hΛ39, hΛ40, hΛ41⟩ := hLine
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
  set xsL : List ℝ := [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41] with hxsdef
  have hchain : xsL.IsChain (· < ·) := by
    rw [hxsdef]
    simp only [List.isChain_cons_cons]
    exact ⟨hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, hc3334, hc3435, hc3536, hc3637, hc3738, hc3839, hc3940, hc4041, List.IsChain.singleton _⟩
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = 41 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hxsdef]
    rfl
  have hb1 : ((12966) : ℝ) ≤ x1 := hlo
  have hb2 : ((12966) : ℝ) ≤ x2 := le_trans hb1 (le_of_lt hc12)
  have hb3 : ((12966) : ℝ) ≤ x3 := le_trans hb2 (le_of_lt hc23)
  have hb4 : ((12966) : ℝ) ≤ x4 := le_trans hb3 (le_of_lt hc34)
  have hb5 : ((12966) : ℝ) ≤ x5 := le_trans hb4 (le_of_lt hc45)
  have hb6 : ((12966) : ℝ) ≤ x6 := le_trans hb5 (le_of_lt hc56)
  have hb7 : ((12966) : ℝ) ≤ x7 := le_trans hb6 (le_of_lt hc67)
  have hb8 : ((12966) : ℝ) ≤ x8 := le_trans hb7 (le_of_lt hc78)
  have hb9 : ((12966) : ℝ) ≤ x9 := le_trans hb8 (le_of_lt hc89)
  have hb10 : ((12966) : ℝ) ≤ x10 := le_trans hb9 (le_of_lt hc910)
  have hb11 : ((12966) : ℝ) ≤ x11 := le_trans hb10 (le_of_lt hc1011)
  have hb12 : ((12966) : ℝ) ≤ x12 := le_trans hb11 (le_of_lt hc1112)
  have hb13 : ((12966) : ℝ) ≤ x13 := le_trans hb12 (le_of_lt hc1213)
  have hb14 : ((12966) : ℝ) ≤ x14 := le_trans hb13 (le_of_lt hc1314)
  have hb15 : ((12966) : ℝ) ≤ x15 := le_trans hb14 (le_of_lt hc1415)
  have hb16 : ((12966) : ℝ) ≤ x16 := le_trans hb15 (le_of_lt hc1516)
  have hb17 : ((12966) : ℝ) ≤ x17 := le_trans hb16 (le_of_lt hc1617)
  have hb18 : ((12966) : ℝ) ≤ x18 := le_trans hb17 (le_of_lt hc1718)
  have hb19 : ((12966) : ℝ) ≤ x19 := le_trans hb18 (le_of_lt hc1819)
  have hb20 : ((12966) : ℝ) ≤ x20 := le_trans hb19 (le_of_lt hc1920)
  have hb21 : ((12966) : ℝ) ≤ x21 := le_trans hb20 (le_of_lt hc2021)
  have hb22 : ((12966) : ℝ) ≤ x22 := le_trans hb21 (le_of_lt hc2122)
  have hb23 : ((12966) : ℝ) ≤ x23 := le_trans hb22 (le_of_lt hc2223)
  have hb24 : ((12966) : ℝ) ≤ x24 := le_trans hb23 (le_of_lt hc2324)
  have hb25 : ((12966) : ℝ) ≤ x25 := le_trans hb24 (le_of_lt hc2425)
  have hb26 : ((12966) : ℝ) ≤ x26 := le_trans hb25 (le_of_lt hc2526)
  have hb27 : ((12966) : ℝ) ≤ x27 := le_trans hb26 (le_of_lt hc2627)
  have hb28 : ((12966) : ℝ) ≤ x28 := le_trans hb27 (le_of_lt hc2728)
  have hb29 : ((12966) : ℝ) ≤ x29 := le_trans hb28 (le_of_lt hc2829)
  have hb30 : ((12966) : ℝ) ≤ x30 := le_trans hb29 (le_of_lt hc2930)
  have hb31 : ((12966) : ℝ) ≤ x31 := le_trans hb30 (le_of_lt hc3031)
  have hb32 : ((12966) : ℝ) ≤ x32 := le_trans hb31 (le_of_lt hc3132)
  have hb33 : ((12966) : ℝ) ≤ x33 := le_trans hb32 (le_of_lt hc3233)
  have hb34 : ((12966) : ℝ) ≤ x34 := le_trans hb33 (le_of_lt hc3334)
  have hb35 : ((12966) : ℝ) ≤ x35 := le_trans hb34 (le_of_lt hc3435)
  have hb36 : ((12966) : ℝ) ≤ x36 := le_trans hb35 (le_of_lt hc3536)
  have hb37 : ((12966) : ℝ) ≤ x37 := le_trans hb36 (le_of_lt hc3637)
  have hb38 : ((12966) : ℝ) ≤ x38 := le_trans hb37 (le_of_lt hc3738)
  have hb39 : ((12966) : ℝ) ≤ x39 := le_trans hb38 (le_of_lt hc3839)
  have hb40 : ((12966) : ℝ) ≤ x40 := le_trans hb39 (le_of_lt hc3940)
  have hb41 : ((12966) : ℝ) ≤ x41 := le_trans hb40 (le_of_lt hc4041)
  have hu41 : x41 ≤ ((13000) : ℝ) := hhi
  have hu40 : x40 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc4041) hu41
  have hu39 : x39 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3940) hu40
  have hu38 : x38 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3839) hu39
  have hu37 : x37 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3738) hu38
  have hu36 : x36 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3637) hu37
  have hu35 : x35 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3536) hu36
  have hu34 : x34 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3435) hu35
  have hu33 : x33 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3334) hu34
  have hu32 : x32 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3233) hu33
  have hu31 : x31 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3132) hu32
  have hu30 : x30 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc3031) hu31
  have hu29 : x29 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2930) hu30
  have hu28 : x28 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2829) hu29
  have hu27 : x27 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2728) hu28
  have hu26 : x26 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2627) hu27
  have hu25 : x25 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2526) hu26
  have hu24 : x24 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2425) hu25
  have hu23 : x23 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2324) hu24
  have hu22 : x22 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2223) hu23
  have hu21 : x21 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2122) hu22
  have hu20 : x20 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc2021) hu21
  have hu19 : x19 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1920) hu20
  have hu18 : x18 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1819) hu19
  have hu17 : x17 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1718) hu18
  have hu16 : x16 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1617) hu17
  have hu15 : x15 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1516) hu16
  have hu14 : x14 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1415) hu15
  have hu13 : x13 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1314) hu14
  have hu12 : x12 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1213) hu13
  have hu11 : x11 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1112) hu12
  have hu10 : x10 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc1011) hu11
  have hu9 : x9 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc910) hu10
  have hu8 : x8 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc89) hu9
  have hu7 : x7 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc78) hu8
  have hu6 : x6 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc67) hu7
  have hu5 : x5 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc56) hu6
  have hu4 : x4 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc45) hu5
  have hu3 : x3 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc34) hu4
  have hu2 : x2 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc23) hu3
  have hu1 : x1 ≤ ((13000) : ℝ) := le_trans (le_of_lt hc12) hu2
  have hre_lo : (((1 / 4000000)) : ℝ) ≤ 1 / 2 := by norm_num
  have hre_hi : (1 / 2 : ℝ) ≤ ((3999999 / 4000000)) := by norm_num
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    rw [hxsdef]
    simp only [List.forall_mem_cons]
    exact ⟨hzeta x1 hΛ1, hzeta x2 hΛ2, hzeta x3 hΛ3, hzeta x4 hΛ4, hzeta x5 hΛ5, hzeta x6 hΛ6, hzeta x7 hΛ7, hzeta x8 hΛ8, hzeta x9 hΛ9, hzeta x10 hΛ10, hzeta x11 hΛ11, hzeta x12 hΛ12, hzeta x13 hΛ13, hzeta x14 hΛ14, hzeta x15 hΛ15, hzeta x16 hΛ16, hzeta x17 hΛ17, hzeta x18 hΛ18, hzeta x19 hΛ19, hzeta x20 hΛ20, hzeta x21 hΛ21, hzeta x22 hΛ22, hzeta x23 hΛ23, hzeta x24 hΛ24, hzeta x25 hΛ25, hzeta x26 hΛ26, hzeta x27 hΛ27, hzeta x28 hΛ28, hzeta x29 hΛ29, hzeta x30 hΛ30, hzeta x31 hΛ31, hzeta x32 hΛ32, hzeta x33 hΛ33, hzeta x34 hΛ34, hzeta x35 hΛ35, hzeta x36 hΛ36, hzeta x37 hΛ37, hzeta x38 hΛ38, hzeta x39 hΛ39, hzeta x40 hΛ40, hzeta x41 hΛ41, List.forall_mem_nil _⟩
  have hTbox : ∀ z ∈ T, ((((1 / 4000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((3999999 / 4000000))) ∧ (((12966) : ℝ) ≤ z.im ∧ z.im ≤ (13000)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    rw [hxsdef]
    simp only [List.forall_mem_cons]
    exact ⟨⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb1, by rw [him_line]; exact hu1⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb2, by rw [him_line]; exact hu2⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb3, by rw [him_line]; exact hu3⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb4, by rw [him_line]; exact hu4⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb5, by rw [him_line]; exact hu5⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb6, by rw [him_line]; exact hu6⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb7, by rw [him_line]; exact hu7⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb8, by rw [him_line]; exact hu8⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb9, by rw [him_line]; exact hu9⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb10, by rw [him_line]; exact hu10⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb11, by rw [him_line]; exact hu11⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb12, by rw [him_line]; exact hu12⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb13, by rw [him_line]; exact hu13⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb14, by rw [him_line]; exact hu14⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb15, by rw [him_line]; exact hu15⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb16, by rw [him_line]; exact hu16⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb17, by rw [him_line]; exact hu17⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb18, by rw [him_line]; exact hu18⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb19, by rw [him_line]; exact hu19⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb20, by rw [him_line]; exact hu20⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb21, by rw [him_line]; exact hu21⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb22, by rw [him_line]; exact hu22⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb23, by rw [him_line]; exact hu23⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb24, by rw [him_line]; exact hu24⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb25, by rw [him_line]; exact hu25⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb26, by rw [him_line]; exact hu26⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb27, by rw [him_line]; exact hu27⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb28, by rw [him_line]; exact hu28⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb29, by rw [him_line]; exact hu29⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb30, by rw [him_line]; exact hu30⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb31, by rw [him_line]; exact hu31⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb32, by rw [him_line]; exact hu32⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb33, by rw [him_line]; exact hu33⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb34, by rw [him_line]; exact hu34⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb35, by rw [him_line]; exact hu35⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb36, by rw [him_line]; exact hu36⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb37, by rw [him_line]; exact hu37⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb38, by rw [him_line]; exact hu38⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb39, by rw [him_line]; exact hu39⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb40, by rw [him_line]; exact hu40⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb41, by rw [him_line]; exact hu41⟩, List.forall_mem_nil _⟩
  set s0f : Finset ℂ := RHInBoxAnalytic.zeroFinset cPB RPB hs1 with hs0def
  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ) with hd0def
  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (12966) (13000) cPB RPB hRpos hbox_ball hs1
  have hE0box : DifferentiableOn ℂ E0 (Set.Icc (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) ×ℂ Set.Icc ((12966) : ℝ) (13000)) := hE0holo
  have hker0' : ∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
      logDeriv riemannZeta z = (∑ ρ ∈ s0f, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by
    intro z hz hnz
    have := hker0 z hz hnz
    rw [hs0def, hd0def]; exact this
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hwindA⟩ := hArb E0 s0f d0 hE0box hker0'
  have hwind : (∫ x in (((1 / 4000000)) : ℝ)..((3999999 / 4000000)), logDeriv riemannZeta (↑x + (((12966) : ℝ) : ℂ) * I))
        - (∫ x in (((1 / 4000000)) : ℝ)..((3999999 / 4000000)), logDeriv riemannZeta (↑x + (((13000) : ℝ) : ℂ) * I))
        + I • (∫ y in ((12966) : ℝ)..(13000), logDeriv riemannZeta (((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((12966) : ℝ)..(13000), logDeriv riemannZeta (((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((41 : ℤ) : ℂ) := by
    rw [show (((41 : ℤ) : ℂ)) = (41 : ℂ) by norm_num]; exact hwindA
  have harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) ×ℂ Set.Icc ((12966) : ℝ) (13000)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 4000000)) : ℝ) ((3999999 / 4000000)), riemannZeta (↑x + (((12966) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 4000000)) : ℝ) ((3999999 / 4000000)), riemannZeta (↑x + (((13000) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((12966) : ℝ) (13000), riemannZeta (((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((12966) : ℝ) (13000), riemannZeta (((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 4000000)) : ℝ) < ρ.re ∧ ρ.re < ((3999999 / 4000000)) ∧ ((12966) : ℝ) < ρ.im ∧ ρ.im < (13000)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((12966) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((13000) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((12966) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((13000) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((12966) : ℝ) : ℂ) * I)) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((13000) : ℝ) : ℂ) * I)) volume (((1 / 4000000))) (((3999999 / 4000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((3999999 / 4000000)) : ℝ) : ℂ) + ↑y * I)) volume ((12966)) ((13000))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 4000000)) : ℝ) : ℂ) + ↑y * I)) volume ((12966)) ((13000))) := by
    intro E s d hEholo hkerE
    have hfull := hArb E s d hEholo hkerE
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1, hfull.2.2.2.2.2.1, hfull.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hcountN : (41 : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num
  exact RHInBox.rh_in_box_of_certificate (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (12966) (13000) cPB RPB 41
    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcountN

end RHInBox_1d4000000_3999999d4000000_12966_13000

/-  Per-box instantiation of `RHInBox.rh_in_box_of_certificate` on the box
    `[(1 / 1000000),(999999 / 1000000)] x [0,100]` with `N = 29` on-line zeros.

    Emitted by telperion `emit_per_box_instantiation` (Task 4 driver `--box`/`--height`).
    Geometry: ball center `c = ((1 / 2)) + (50)*I`, radius `R = Real.sqrt ((5000499999000001 / 2000000000000))`,
    chosen so the box is STRICTLY inside the ball and the pole `s = 1` is STRICTLY outside.
    The winding count `N` and on-line zeros are the documented Arb non-kernel inputs
    (supplied as the `hArb`/`hLine` hypotheses).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import RHInBoxAnalytic
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 8600000

namespace RHInBox_1d1000000_999999d1000000_0_100

/-- Chosen Blaschke ball center for the box `[(1 / 1000000),(999999 / 1000000)] x [0,100]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (50)⟩

/-- Chosen Blaschke ball radius (squared radius `(5000499999000001 / 2000000000000)`). -/
noncomputable def RPB : ℝ := Real.sqrt ((5000499999000001 / 2000000000000))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- **RH-in-a-box on `[(1 / 1000000),(999999 / 1000000)] x [0,100]` with `N = 29`.**  Instantiates the generic
    `RHInBox.rh_in_box_of_certificate` at this box's corners, chosen Blaschke ball
    `c = ((1 / 2)) + (50)*I`, `R = Real.sqrt ((5000499999000001 / 2000000000000))`, and count `N = 29`.  Takes the
    documented Arb inputs `hLine` (the 29 on-line zeros) and `hArb` (boundary bundle +
    winding `= 2*pi*I*29`).  conjecture1_proved = False. -/
theorem rh_in_box_1d1000000_999999d1000000_0_100
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
      DifferentiableOn ℂ E (Set.Icc (((1 / 1000000)) : ℝ) ((999999 / 1000000)) ×ℂ Set.Icc ((0) : ℝ) (100)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((0) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 1000000)) : ℝ) < ρ.re ∧ ρ.re < ((999999 / 1000000)) ∧ ((0) : ℝ) < ρ.im ∧ ρ.im < (100)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((0) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      ((∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
          + I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (29 : ℂ))) :
    (∀ ρ, ((((1 / 1000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999999 / 1000000))) → (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hsig : (((1 / 1000000)) : ℝ) ≤ ((999999 / 1000000)) := by norm_num
  have hTle : ((0) : ℝ) ≤ (100) := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((((1 / 1000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999999 / 1000000))) →
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
    have hle : Real.sqrt ((5000499999000001 / 2000000000000)) ≤
        Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (50)) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    linarith [hlt, hle]
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, ⟨hlo, hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hhi⟩, hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7, hΛ8, hΛ9, hΛ10, hΛ11, hΛ12, hΛ13, hΛ14, hΛ15, hΛ16, hΛ17, hΛ18, hΛ19, hΛ20, hΛ21, hΛ22, hΛ23, hΛ24, hΛ25, hΛ26, hΛ27, hΛ28, hΛ29⟩ := hLine
  set z1 : ℂ := 1 / 2 + (x1 : ℂ) * Complex.I with hz1def
  set z2 : ℂ := 1 / 2 + (x2 : ℂ) * Complex.I with hz2def
  set z3 : ℂ := 1 / 2 + (x3 : ℂ) * Complex.I with hz3def
  set z4 : ℂ := 1 / 2 + (x4 : ℂ) * Complex.I with hz4def
  set z5 : ℂ := 1 / 2 + (x5 : ℂ) * Complex.I with hz5def
  set z6 : ℂ := 1 / 2 + (x6 : ℂ) * Complex.I with hz6def
  set z7 : ℂ := 1 / 2 + (x7 : ℂ) * Complex.I with hz7def
  set z8 : ℂ := 1 / 2 + (x8 : ℂ) * Complex.I with hz8def
  set z9 : ℂ := 1 / 2 + (x9 : ℂ) * Complex.I with hz9def
  set z10 : ℂ := 1 / 2 + (x10 : ℂ) * Complex.I with hz10def
  set z11 : ℂ := 1 / 2 + (x11 : ℂ) * Complex.I with hz11def
  set z12 : ℂ := 1 / 2 + (x12 : ℂ) * Complex.I with hz12def
  set z13 : ℂ := 1 / 2 + (x13 : ℂ) * Complex.I with hz13def
  set z14 : ℂ := 1 / 2 + (x14 : ℂ) * Complex.I with hz14def
  set z15 : ℂ := 1 / 2 + (x15 : ℂ) * Complex.I with hz15def
  set z16 : ℂ := 1 / 2 + (x16 : ℂ) * Complex.I with hz16def
  set z17 : ℂ := 1 / 2 + (x17 : ℂ) * Complex.I with hz17def
  set z18 : ℂ := 1 / 2 + (x18 : ℂ) * Complex.I with hz18def
  set z19 : ℂ := 1 / 2 + (x19 : ℂ) * Complex.I with hz19def
  set z20 : ℂ := 1 / 2 + (x20 : ℂ) * Complex.I with hz20def
  set z21 : ℂ := 1 / 2 + (x21 : ℂ) * Complex.I with hz21def
  set z22 : ℂ := 1 / 2 + (x22 : ℂ) * Complex.I with hz22def
  set z23 : ℂ := 1 / 2 + (x23 : ℂ) * Complex.I with hz23def
  set z24 : ℂ := 1 / 2 + (x24 : ℂ) * Complex.I with hz24def
  set z25 : ℂ := 1 / 2 + (x25 : ℂ) * Complex.I with hz25def
  set z26 : ℂ := 1 / 2 + (x26 : ℂ) * Complex.I with hz26def
  set z27 : ℂ := 1 / 2 + (x27 : ℂ) * Complex.I with hz27def
  set z28 : ℂ := 1 / 2 + (x28 : ℂ) * Complex.I with hz28def
  set z29 : ℂ := 1 / 2 + (x29 : ℂ) * Complex.I with hz29def
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
  have n16 : z1 ≠ z6 := distinct x1 x6 (by linarith)
  have n17 : z1 ≠ z7 := distinct x1 x7 (by linarith)
  have n18 : z1 ≠ z8 := distinct x1 x8 (by linarith)
  have n19 : z1 ≠ z9 := distinct x1 x9 (by linarith)
  have n110 : z1 ≠ z10 := distinct x1 x10 (by linarith)
  have n111 : z1 ≠ z11 := distinct x1 x11 (by linarith)
  have n112 : z1 ≠ z12 := distinct x1 x12 (by linarith)
  have n113 : z1 ≠ z13 := distinct x1 x13 (by linarith)
  have n114 : z1 ≠ z14 := distinct x1 x14 (by linarith)
  have n115 : z1 ≠ z15 := distinct x1 x15 (by linarith)
  have n116 : z1 ≠ z16 := distinct x1 x16 (by linarith)
  have n117 : z1 ≠ z17 := distinct x1 x17 (by linarith)
  have n118 : z1 ≠ z18 := distinct x1 x18 (by linarith)
  have n119 : z1 ≠ z19 := distinct x1 x19 (by linarith)
  have n120 : z1 ≠ z20 := distinct x1 x20 (by linarith)
  have n121 : z1 ≠ z21 := distinct x1 x21 (by linarith)
  have n122 : z1 ≠ z22 := distinct x1 x22 (by linarith)
  have n123 : z1 ≠ z23 := distinct x1 x23 (by linarith)
  have n124 : z1 ≠ z24 := distinct x1 x24 (by linarith)
  have n125 : z1 ≠ z25 := distinct x1 x25 (by linarith)
  have n126 : z1 ≠ z26 := distinct x1 x26 (by linarith)
  have n127 : z1 ≠ z27 := distinct x1 x27 (by linarith)
  have n128 : z1 ≠ z28 := distinct x1 x28 (by linarith)
  have n129 : z1 ≠ z29 := distinct x1 x29 (by linarith)
  have n23 : z2 ≠ z3 := distinct x2 x3 (by linarith)
  have n24 : z2 ≠ z4 := distinct x2 x4 (by linarith)
  have n25 : z2 ≠ z5 := distinct x2 x5 (by linarith)
  have n26 : z2 ≠ z6 := distinct x2 x6 (by linarith)
  have n27 : z2 ≠ z7 := distinct x2 x7 (by linarith)
  have n28 : z2 ≠ z8 := distinct x2 x8 (by linarith)
  have n29 : z2 ≠ z9 := distinct x2 x9 (by linarith)
  have n210 : z2 ≠ z10 := distinct x2 x10 (by linarith)
  have n211 : z2 ≠ z11 := distinct x2 x11 (by linarith)
  have n212 : z2 ≠ z12 := distinct x2 x12 (by linarith)
  have n213 : z2 ≠ z13 := distinct x2 x13 (by linarith)
  have n214 : z2 ≠ z14 := distinct x2 x14 (by linarith)
  have n215 : z2 ≠ z15 := distinct x2 x15 (by linarith)
  have n216 : z2 ≠ z16 := distinct x2 x16 (by linarith)
  have n217 : z2 ≠ z17 := distinct x2 x17 (by linarith)
  have n218 : z2 ≠ z18 := distinct x2 x18 (by linarith)
  have n219 : z2 ≠ z19 := distinct x2 x19 (by linarith)
  have n220 : z2 ≠ z20 := distinct x2 x20 (by linarith)
  have n221 : z2 ≠ z21 := distinct x2 x21 (by linarith)
  have n222 : z2 ≠ z22 := distinct x2 x22 (by linarith)
  have n223 : z2 ≠ z23 := distinct x2 x23 (by linarith)
  have n224 : z2 ≠ z24 := distinct x2 x24 (by linarith)
  have n225 : z2 ≠ z25 := distinct x2 x25 (by linarith)
  have n226 : z2 ≠ z26 := distinct x2 x26 (by linarith)
  have n227 : z2 ≠ z27 := distinct x2 x27 (by linarith)
  have n228 : z2 ≠ z28 := distinct x2 x28 (by linarith)
  have n229 : z2 ≠ z29 := distinct x2 x29 (by linarith)
  have n34 : z3 ≠ z4 := distinct x3 x4 (by linarith)
  have n35 : z3 ≠ z5 := distinct x3 x5 (by linarith)
  have n36 : z3 ≠ z6 := distinct x3 x6 (by linarith)
  have n37 : z3 ≠ z7 := distinct x3 x7 (by linarith)
  have n38 : z3 ≠ z8 := distinct x3 x8 (by linarith)
  have n39 : z3 ≠ z9 := distinct x3 x9 (by linarith)
  have n310 : z3 ≠ z10 := distinct x3 x10 (by linarith)
  have n311 : z3 ≠ z11 := distinct x3 x11 (by linarith)
  have n312 : z3 ≠ z12 := distinct x3 x12 (by linarith)
  have n313 : z3 ≠ z13 := distinct x3 x13 (by linarith)
  have n314 : z3 ≠ z14 := distinct x3 x14 (by linarith)
  have n315 : z3 ≠ z15 := distinct x3 x15 (by linarith)
  have n316 : z3 ≠ z16 := distinct x3 x16 (by linarith)
  have n317 : z3 ≠ z17 := distinct x3 x17 (by linarith)
  have n318 : z3 ≠ z18 := distinct x3 x18 (by linarith)
  have n319 : z3 ≠ z19 := distinct x3 x19 (by linarith)
  have n320 : z3 ≠ z20 := distinct x3 x20 (by linarith)
  have n321 : z3 ≠ z21 := distinct x3 x21 (by linarith)
  have n322 : z3 ≠ z22 := distinct x3 x22 (by linarith)
  have n323 : z3 ≠ z23 := distinct x3 x23 (by linarith)
  have n324 : z3 ≠ z24 := distinct x3 x24 (by linarith)
  have n325 : z3 ≠ z25 := distinct x3 x25 (by linarith)
  have n326 : z3 ≠ z26 := distinct x3 x26 (by linarith)
  have n327 : z3 ≠ z27 := distinct x3 x27 (by linarith)
  have n328 : z3 ≠ z28 := distinct x3 x28 (by linarith)
  have n329 : z3 ≠ z29 := distinct x3 x29 (by linarith)
  have n45 : z4 ≠ z5 := distinct x4 x5 (by linarith)
  have n46 : z4 ≠ z6 := distinct x4 x6 (by linarith)
  have n47 : z4 ≠ z7 := distinct x4 x7 (by linarith)
  have n48 : z4 ≠ z8 := distinct x4 x8 (by linarith)
  have n49 : z4 ≠ z9 := distinct x4 x9 (by linarith)
  have n410 : z4 ≠ z10 := distinct x4 x10 (by linarith)
  have n411 : z4 ≠ z11 := distinct x4 x11 (by linarith)
  have n412 : z4 ≠ z12 := distinct x4 x12 (by linarith)
  have n413 : z4 ≠ z13 := distinct x4 x13 (by linarith)
  have n414 : z4 ≠ z14 := distinct x4 x14 (by linarith)
  have n415 : z4 ≠ z15 := distinct x4 x15 (by linarith)
  have n416 : z4 ≠ z16 := distinct x4 x16 (by linarith)
  have n417 : z4 ≠ z17 := distinct x4 x17 (by linarith)
  have n418 : z4 ≠ z18 := distinct x4 x18 (by linarith)
  have n419 : z4 ≠ z19 := distinct x4 x19 (by linarith)
  have n420 : z4 ≠ z20 := distinct x4 x20 (by linarith)
  have n421 : z4 ≠ z21 := distinct x4 x21 (by linarith)
  have n422 : z4 ≠ z22 := distinct x4 x22 (by linarith)
  have n423 : z4 ≠ z23 := distinct x4 x23 (by linarith)
  have n424 : z4 ≠ z24 := distinct x4 x24 (by linarith)
  have n425 : z4 ≠ z25 := distinct x4 x25 (by linarith)
  have n426 : z4 ≠ z26 := distinct x4 x26 (by linarith)
  have n427 : z4 ≠ z27 := distinct x4 x27 (by linarith)
  have n428 : z4 ≠ z28 := distinct x4 x28 (by linarith)
  have n429 : z4 ≠ z29 := distinct x4 x29 (by linarith)
  have n56 : z5 ≠ z6 := distinct x5 x6 (by linarith)
  have n57 : z5 ≠ z7 := distinct x5 x7 (by linarith)
  have n58 : z5 ≠ z8 := distinct x5 x8 (by linarith)
  have n59 : z5 ≠ z9 := distinct x5 x9 (by linarith)
  have n510 : z5 ≠ z10 := distinct x5 x10 (by linarith)
  have n511 : z5 ≠ z11 := distinct x5 x11 (by linarith)
  have n512 : z5 ≠ z12 := distinct x5 x12 (by linarith)
  have n513 : z5 ≠ z13 := distinct x5 x13 (by linarith)
  have n514 : z5 ≠ z14 := distinct x5 x14 (by linarith)
  have n515 : z5 ≠ z15 := distinct x5 x15 (by linarith)
  have n516 : z5 ≠ z16 := distinct x5 x16 (by linarith)
  have n517 : z5 ≠ z17 := distinct x5 x17 (by linarith)
  have n518 : z5 ≠ z18 := distinct x5 x18 (by linarith)
  have n519 : z5 ≠ z19 := distinct x5 x19 (by linarith)
  have n520 : z5 ≠ z20 := distinct x5 x20 (by linarith)
  have n521 : z5 ≠ z21 := distinct x5 x21 (by linarith)
  have n522 : z5 ≠ z22 := distinct x5 x22 (by linarith)
  have n523 : z5 ≠ z23 := distinct x5 x23 (by linarith)
  have n524 : z5 ≠ z24 := distinct x5 x24 (by linarith)
  have n525 : z5 ≠ z25 := distinct x5 x25 (by linarith)
  have n526 : z5 ≠ z26 := distinct x5 x26 (by linarith)
  have n527 : z5 ≠ z27 := distinct x5 x27 (by linarith)
  have n528 : z5 ≠ z28 := distinct x5 x28 (by linarith)
  have n529 : z5 ≠ z29 := distinct x5 x29 (by linarith)
  have n67 : z6 ≠ z7 := distinct x6 x7 (by linarith)
  have n68 : z6 ≠ z8 := distinct x6 x8 (by linarith)
  have n69 : z6 ≠ z9 := distinct x6 x9 (by linarith)
  have n610 : z6 ≠ z10 := distinct x6 x10 (by linarith)
  have n611 : z6 ≠ z11 := distinct x6 x11 (by linarith)
  have n612 : z6 ≠ z12 := distinct x6 x12 (by linarith)
  have n613 : z6 ≠ z13 := distinct x6 x13 (by linarith)
  have n614 : z6 ≠ z14 := distinct x6 x14 (by linarith)
  have n615 : z6 ≠ z15 := distinct x6 x15 (by linarith)
  have n616 : z6 ≠ z16 := distinct x6 x16 (by linarith)
  have n617 : z6 ≠ z17 := distinct x6 x17 (by linarith)
  have n618 : z6 ≠ z18 := distinct x6 x18 (by linarith)
  have n619 : z6 ≠ z19 := distinct x6 x19 (by linarith)
  have n620 : z6 ≠ z20 := distinct x6 x20 (by linarith)
  have n621 : z6 ≠ z21 := distinct x6 x21 (by linarith)
  have n622 : z6 ≠ z22 := distinct x6 x22 (by linarith)
  have n623 : z6 ≠ z23 := distinct x6 x23 (by linarith)
  have n624 : z6 ≠ z24 := distinct x6 x24 (by linarith)
  have n625 : z6 ≠ z25 := distinct x6 x25 (by linarith)
  have n626 : z6 ≠ z26 := distinct x6 x26 (by linarith)
  have n627 : z6 ≠ z27 := distinct x6 x27 (by linarith)
  have n628 : z6 ≠ z28 := distinct x6 x28 (by linarith)
  have n629 : z6 ≠ z29 := distinct x6 x29 (by linarith)
  have n78 : z7 ≠ z8 := distinct x7 x8 (by linarith)
  have n79 : z7 ≠ z9 := distinct x7 x9 (by linarith)
  have n710 : z7 ≠ z10 := distinct x7 x10 (by linarith)
  have n711 : z7 ≠ z11 := distinct x7 x11 (by linarith)
  have n712 : z7 ≠ z12 := distinct x7 x12 (by linarith)
  have n713 : z7 ≠ z13 := distinct x7 x13 (by linarith)
  have n714 : z7 ≠ z14 := distinct x7 x14 (by linarith)
  have n715 : z7 ≠ z15 := distinct x7 x15 (by linarith)
  have n716 : z7 ≠ z16 := distinct x7 x16 (by linarith)
  have n717 : z7 ≠ z17 := distinct x7 x17 (by linarith)
  have n718 : z7 ≠ z18 := distinct x7 x18 (by linarith)
  have n719 : z7 ≠ z19 := distinct x7 x19 (by linarith)
  have n720 : z7 ≠ z20 := distinct x7 x20 (by linarith)
  have n721 : z7 ≠ z21 := distinct x7 x21 (by linarith)
  have n722 : z7 ≠ z22 := distinct x7 x22 (by linarith)
  have n723 : z7 ≠ z23 := distinct x7 x23 (by linarith)
  have n724 : z7 ≠ z24 := distinct x7 x24 (by linarith)
  have n725 : z7 ≠ z25 := distinct x7 x25 (by linarith)
  have n726 : z7 ≠ z26 := distinct x7 x26 (by linarith)
  have n727 : z7 ≠ z27 := distinct x7 x27 (by linarith)
  have n728 : z7 ≠ z28 := distinct x7 x28 (by linarith)
  have n729 : z7 ≠ z29 := distinct x7 x29 (by linarith)
  have n89 : z8 ≠ z9 := distinct x8 x9 (by linarith)
  have n810 : z8 ≠ z10 := distinct x8 x10 (by linarith)
  have n811 : z8 ≠ z11 := distinct x8 x11 (by linarith)
  have n812 : z8 ≠ z12 := distinct x8 x12 (by linarith)
  have n813 : z8 ≠ z13 := distinct x8 x13 (by linarith)
  have n814 : z8 ≠ z14 := distinct x8 x14 (by linarith)
  have n815 : z8 ≠ z15 := distinct x8 x15 (by linarith)
  have n816 : z8 ≠ z16 := distinct x8 x16 (by linarith)
  have n817 : z8 ≠ z17 := distinct x8 x17 (by linarith)
  have n818 : z8 ≠ z18 := distinct x8 x18 (by linarith)
  have n819 : z8 ≠ z19 := distinct x8 x19 (by linarith)
  have n820 : z8 ≠ z20 := distinct x8 x20 (by linarith)
  have n821 : z8 ≠ z21 := distinct x8 x21 (by linarith)
  have n822 : z8 ≠ z22 := distinct x8 x22 (by linarith)
  have n823 : z8 ≠ z23 := distinct x8 x23 (by linarith)
  have n824 : z8 ≠ z24 := distinct x8 x24 (by linarith)
  have n825 : z8 ≠ z25 := distinct x8 x25 (by linarith)
  have n826 : z8 ≠ z26 := distinct x8 x26 (by linarith)
  have n827 : z8 ≠ z27 := distinct x8 x27 (by linarith)
  have n828 : z8 ≠ z28 := distinct x8 x28 (by linarith)
  have n829 : z8 ≠ z29 := distinct x8 x29 (by linarith)
  have n910 : z9 ≠ z10 := distinct x9 x10 (by linarith)
  have n911 : z9 ≠ z11 := distinct x9 x11 (by linarith)
  have n912 : z9 ≠ z12 := distinct x9 x12 (by linarith)
  have n913 : z9 ≠ z13 := distinct x9 x13 (by linarith)
  have n914 : z9 ≠ z14 := distinct x9 x14 (by linarith)
  have n915 : z9 ≠ z15 := distinct x9 x15 (by linarith)
  have n916 : z9 ≠ z16 := distinct x9 x16 (by linarith)
  have n917 : z9 ≠ z17 := distinct x9 x17 (by linarith)
  have n918 : z9 ≠ z18 := distinct x9 x18 (by linarith)
  have n919 : z9 ≠ z19 := distinct x9 x19 (by linarith)
  have n920 : z9 ≠ z20 := distinct x9 x20 (by linarith)
  have n921 : z9 ≠ z21 := distinct x9 x21 (by linarith)
  have n922 : z9 ≠ z22 := distinct x9 x22 (by linarith)
  have n923 : z9 ≠ z23 := distinct x9 x23 (by linarith)
  have n924 : z9 ≠ z24 := distinct x9 x24 (by linarith)
  have n925 : z9 ≠ z25 := distinct x9 x25 (by linarith)
  have n926 : z9 ≠ z26 := distinct x9 x26 (by linarith)
  have n927 : z9 ≠ z27 := distinct x9 x27 (by linarith)
  have n928 : z9 ≠ z28 := distinct x9 x28 (by linarith)
  have n929 : z9 ≠ z29 := distinct x9 x29 (by linarith)
  have n1011 : z10 ≠ z11 := distinct x10 x11 (by linarith)
  have n1012 : z10 ≠ z12 := distinct x10 x12 (by linarith)
  have n1013 : z10 ≠ z13 := distinct x10 x13 (by linarith)
  have n1014 : z10 ≠ z14 := distinct x10 x14 (by linarith)
  have n1015 : z10 ≠ z15 := distinct x10 x15 (by linarith)
  have n1016 : z10 ≠ z16 := distinct x10 x16 (by linarith)
  have n1017 : z10 ≠ z17 := distinct x10 x17 (by linarith)
  have n1018 : z10 ≠ z18 := distinct x10 x18 (by linarith)
  have n1019 : z10 ≠ z19 := distinct x10 x19 (by linarith)
  have n1020 : z10 ≠ z20 := distinct x10 x20 (by linarith)
  have n1021 : z10 ≠ z21 := distinct x10 x21 (by linarith)
  have n1022 : z10 ≠ z22 := distinct x10 x22 (by linarith)
  have n1023 : z10 ≠ z23 := distinct x10 x23 (by linarith)
  have n1024 : z10 ≠ z24 := distinct x10 x24 (by linarith)
  have n1025 : z10 ≠ z25 := distinct x10 x25 (by linarith)
  have n1026 : z10 ≠ z26 := distinct x10 x26 (by linarith)
  have n1027 : z10 ≠ z27 := distinct x10 x27 (by linarith)
  have n1028 : z10 ≠ z28 := distinct x10 x28 (by linarith)
  have n1029 : z10 ≠ z29 := distinct x10 x29 (by linarith)
  have n1112 : z11 ≠ z12 := distinct x11 x12 (by linarith)
  have n1113 : z11 ≠ z13 := distinct x11 x13 (by linarith)
  have n1114 : z11 ≠ z14 := distinct x11 x14 (by linarith)
  have n1115 : z11 ≠ z15 := distinct x11 x15 (by linarith)
  have n1116 : z11 ≠ z16 := distinct x11 x16 (by linarith)
  have n1117 : z11 ≠ z17 := distinct x11 x17 (by linarith)
  have n1118 : z11 ≠ z18 := distinct x11 x18 (by linarith)
  have n1119 : z11 ≠ z19 := distinct x11 x19 (by linarith)
  have n1120 : z11 ≠ z20 := distinct x11 x20 (by linarith)
  have n1121 : z11 ≠ z21 := distinct x11 x21 (by linarith)
  have n1122 : z11 ≠ z22 := distinct x11 x22 (by linarith)
  have n1123 : z11 ≠ z23 := distinct x11 x23 (by linarith)
  have n1124 : z11 ≠ z24 := distinct x11 x24 (by linarith)
  have n1125 : z11 ≠ z25 := distinct x11 x25 (by linarith)
  have n1126 : z11 ≠ z26 := distinct x11 x26 (by linarith)
  have n1127 : z11 ≠ z27 := distinct x11 x27 (by linarith)
  have n1128 : z11 ≠ z28 := distinct x11 x28 (by linarith)
  have n1129 : z11 ≠ z29 := distinct x11 x29 (by linarith)
  have n1213 : z12 ≠ z13 := distinct x12 x13 (by linarith)
  have n1214 : z12 ≠ z14 := distinct x12 x14 (by linarith)
  have n1215 : z12 ≠ z15 := distinct x12 x15 (by linarith)
  have n1216 : z12 ≠ z16 := distinct x12 x16 (by linarith)
  have n1217 : z12 ≠ z17 := distinct x12 x17 (by linarith)
  have n1218 : z12 ≠ z18 := distinct x12 x18 (by linarith)
  have n1219 : z12 ≠ z19 := distinct x12 x19 (by linarith)
  have n1220 : z12 ≠ z20 := distinct x12 x20 (by linarith)
  have n1221 : z12 ≠ z21 := distinct x12 x21 (by linarith)
  have n1222 : z12 ≠ z22 := distinct x12 x22 (by linarith)
  have n1223 : z12 ≠ z23 := distinct x12 x23 (by linarith)
  have n1224 : z12 ≠ z24 := distinct x12 x24 (by linarith)
  have n1225 : z12 ≠ z25 := distinct x12 x25 (by linarith)
  have n1226 : z12 ≠ z26 := distinct x12 x26 (by linarith)
  have n1227 : z12 ≠ z27 := distinct x12 x27 (by linarith)
  have n1228 : z12 ≠ z28 := distinct x12 x28 (by linarith)
  have n1229 : z12 ≠ z29 := distinct x12 x29 (by linarith)
  have n1314 : z13 ≠ z14 := distinct x13 x14 (by linarith)
  have n1315 : z13 ≠ z15 := distinct x13 x15 (by linarith)
  have n1316 : z13 ≠ z16 := distinct x13 x16 (by linarith)
  have n1317 : z13 ≠ z17 := distinct x13 x17 (by linarith)
  have n1318 : z13 ≠ z18 := distinct x13 x18 (by linarith)
  have n1319 : z13 ≠ z19 := distinct x13 x19 (by linarith)
  have n1320 : z13 ≠ z20 := distinct x13 x20 (by linarith)
  have n1321 : z13 ≠ z21 := distinct x13 x21 (by linarith)
  have n1322 : z13 ≠ z22 := distinct x13 x22 (by linarith)
  have n1323 : z13 ≠ z23 := distinct x13 x23 (by linarith)
  have n1324 : z13 ≠ z24 := distinct x13 x24 (by linarith)
  have n1325 : z13 ≠ z25 := distinct x13 x25 (by linarith)
  have n1326 : z13 ≠ z26 := distinct x13 x26 (by linarith)
  have n1327 : z13 ≠ z27 := distinct x13 x27 (by linarith)
  have n1328 : z13 ≠ z28 := distinct x13 x28 (by linarith)
  have n1329 : z13 ≠ z29 := distinct x13 x29 (by linarith)
  have n1415 : z14 ≠ z15 := distinct x14 x15 (by linarith)
  have n1416 : z14 ≠ z16 := distinct x14 x16 (by linarith)
  have n1417 : z14 ≠ z17 := distinct x14 x17 (by linarith)
  have n1418 : z14 ≠ z18 := distinct x14 x18 (by linarith)
  have n1419 : z14 ≠ z19 := distinct x14 x19 (by linarith)
  have n1420 : z14 ≠ z20 := distinct x14 x20 (by linarith)
  have n1421 : z14 ≠ z21 := distinct x14 x21 (by linarith)
  have n1422 : z14 ≠ z22 := distinct x14 x22 (by linarith)
  have n1423 : z14 ≠ z23 := distinct x14 x23 (by linarith)
  have n1424 : z14 ≠ z24 := distinct x14 x24 (by linarith)
  have n1425 : z14 ≠ z25 := distinct x14 x25 (by linarith)
  have n1426 : z14 ≠ z26 := distinct x14 x26 (by linarith)
  have n1427 : z14 ≠ z27 := distinct x14 x27 (by linarith)
  have n1428 : z14 ≠ z28 := distinct x14 x28 (by linarith)
  have n1429 : z14 ≠ z29 := distinct x14 x29 (by linarith)
  have n1516 : z15 ≠ z16 := distinct x15 x16 (by linarith)
  have n1517 : z15 ≠ z17 := distinct x15 x17 (by linarith)
  have n1518 : z15 ≠ z18 := distinct x15 x18 (by linarith)
  have n1519 : z15 ≠ z19 := distinct x15 x19 (by linarith)
  have n1520 : z15 ≠ z20 := distinct x15 x20 (by linarith)
  have n1521 : z15 ≠ z21 := distinct x15 x21 (by linarith)
  have n1522 : z15 ≠ z22 := distinct x15 x22 (by linarith)
  have n1523 : z15 ≠ z23 := distinct x15 x23 (by linarith)
  have n1524 : z15 ≠ z24 := distinct x15 x24 (by linarith)
  have n1525 : z15 ≠ z25 := distinct x15 x25 (by linarith)
  have n1526 : z15 ≠ z26 := distinct x15 x26 (by linarith)
  have n1527 : z15 ≠ z27 := distinct x15 x27 (by linarith)
  have n1528 : z15 ≠ z28 := distinct x15 x28 (by linarith)
  have n1529 : z15 ≠ z29 := distinct x15 x29 (by linarith)
  have n1617 : z16 ≠ z17 := distinct x16 x17 (by linarith)
  have n1618 : z16 ≠ z18 := distinct x16 x18 (by linarith)
  have n1619 : z16 ≠ z19 := distinct x16 x19 (by linarith)
  have n1620 : z16 ≠ z20 := distinct x16 x20 (by linarith)
  have n1621 : z16 ≠ z21 := distinct x16 x21 (by linarith)
  have n1622 : z16 ≠ z22 := distinct x16 x22 (by linarith)
  have n1623 : z16 ≠ z23 := distinct x16 x23 (by linarith)
  have n1624 : z16 ≠ z24 := distinct x16 x24 (by linarith)
  have n1625 : z16 ≠ z25 := distinct x16 x25 (by linarith)
  have n1626 : z16 ≠ z26 := distinct x16 x26 (by linarith)
  have n1627 : z16 ≠ z27 := distinct x16 x27 (by linarith)
  have n1628 : z16 ≠ z28 := distinct x16 x28 (by linarith)
  have n1629 : z16 ≠ z29 := distinct x16 x29 (by linarith)
  have n1718 : z17 ≠ z18 := distinct x17 x18 (by linarith)
  have n1719 : z17 ≠ z19 := distinct x17 x19 (by linarith)
  have n1720 : z17 ≠ z20 := distinct x17 x20 (by linarith)
  have n1721 : z17 ≠ z21 := distinct x17 x21 (by linarith)
  have n1722 : z17 ≠ z22 := distinct x17 x22 (by linarith)
  have n1723 : z17 ≠ z23 := distinct x17 x23 (by linarith)
  have n1724 : z17 ≠ z24 := distinct x17 x24 (by linarith)
  have n1725 : z17 ≠ z25 := distinct x17 x25 (by linarith)
  have n1726 : z17 ≠ z26 := distinct x17 x26 (by linarith)
  have n1727 : z17 ≠ z27 := distinct x17 x27 (by linarith)
  have n1728 : z17 ≠ z28 := distinct x17 x28 (by linarith)
  have n1729 : z17 ≠ z29 := distinct x17 x29 (by linarith)
  have n1819 : z18 ≠ z19 := distinct x18 x19 (by linarith)
  have n1820 : z18 ≠ z20 := distinct x18 x20 (by linarith)
  have n1821 : z18 ≠ z21 := distinct x18 x21 (by linarith)
  have n1822 : z18 ≠ z22 := distinct x18 x22 (by linarith)
  have n1823 : z18 ≠ z23 := distinct x18 x23 (by linarith)
  have n1824 : z18 ≠ z24 := distinct x18 x24 (by linarith)
  have n1825 : z18 ≠ z25 := distinct x18 x25 (by linarith)
  have n1826 : z18 ≠ z26 := distinct x18 x26 (by linarith)
  have n1827 : z18 ≠ z27 := distinct x18 x27 (by linarith)
  have n1828 : z18 ≠ z28 := distinct x18 x28 (by linarith)
  have n1829 : z18 ≠ z29 := distinct x18 x29 (by linarith)
  have n1920 : z19 ≠ z20 := distinct x19 x20 (by linarith)
  have n1921 : z19 ≠ z21 := distinct x19 x21 (by linarith)
  have n1922 : z19 ≠ z22 := distinct x19 x22 (by linarith)
  have n1923 : z19 ≠ z23 := distinct x19 x23 (by linarith)
  have n1924 : z19 ≠ z24 := distinct x19 x24 (by linarith)
  have n1925 : z19 ≠ z25 := distinct x19 x25 (by linarith)
  have n1926 : z19 ≠ z26 := distinct x19 x26 (by linarith)
  have n1927 : z19 ≠ z27 := distinct x19 x27 (by linarith)
  have n1928 : z19 ≠ z28 := distinct x19 x28 (by linarith)
  have n1929 : z19 ≠ z29 := distinct x19 x29 (by linarith)
  have n2021 : z20 ≠ z21 := distinct x20 x21 (by linarith)
  have n2022 : z20 ≠ z22 := distinct x20 x22 (by linarith)
  have n2023 : z20 ≠ z23 := distinct x20 x23 (by linarith)
  have n2024 : z20 ≠ z24 := distinct x20 x24 (by linarith)
  have n2025 : z20 ≠ z25 := distinct x20 x25 (by linarith)
  have n2026 : z20 ≠ z26 := distinct x20 x26 (by linarith)
  have n2027 : z20 ≠ z27 := distinct x20 x27 (by linarith)
  have n2028 : z20 ≠ z28 := distinct x20 x28 (by linarith)
  have n2029 : z20 ≠ z29 := distinct x20 x29 (by linarith)
  have n2122 : z21 ≠ z22 := distinct x21 x22 (by linarith)
  have n2123 : z21 ≠ z23 := distinct x21 x23 (by linarith)
  have n2124 : z21 ≠ z24 := distinct x21 x24 (by linarith)
  have n2125 : z21 ≠ z25 := distinct x21 x25 (by linarith)
  have n2126 : z21 ≠ z26 := distinct x21 x26 (by linarith)
  have n2127 : z21 ≠ z27 := distinct x21 x27 (by linarith)
  have n2128 : z21 ≠ z28 := distinct x21 x28 (by linarith)
  have n2129 : z21 ≠ z29 := distinct x21 x29 (by linarith)
  have n2223 : z22 ≠ z23 := distinct x22 x23 (by linarith)
  have n2224 : z22 ≠ z24 := distinct x22 x24 (by linarith)
  have n2225 : z22 ≠ z25 := distinct x22 x25 (by linarith)
  have n2226 : z22 ≠ z26 := distinct x22 x26 (by linarith)
  have n2227 : z22 ≠ z27 := distinct x22 x27 (by linarith)
  have n2228 : z22 ≠ z28 := distinct x22 x28 (by linarith)
  have n2229 : z22 ≠ z29 := distinct x22 x29 (by linarith)
  have n2324 : z23 ≠ z24 := distinct x23 x24 (by linarith)
  have n2325 : z23 ≠ z25 := distinct x23 x25 (by linarith)
  have n2326 : z23 ≠ z26 := distinct x23 x26 (by linarith)
  have n2327 : z23 ≠ z27 := distinct x23 x27 (by linarith)
  have n2328 : z23 ≠ z28 := distinct x23 x28 (by linarith)
  have n2329 : z23 ≠ z29 := distinct x23 x29 (by linarith)
  have n2425 : z24 ≠ z25 := distinct x24 x25 (by linarith)
  have n2426 : z24 ≠ z26 := distinct x24 x26 (by linarith)
  have n2427 : z24 ≠ z27 := distinct x24 x27 (by linarith)
  have n2428 : z24 ≠ z28 := distinct x24 x28 (by linarith)
  have n2429 : z24 ≠ z29 := distinct x24 x29 (by linarith)
  have n2526 : z25 ≠ z26 := distinct x25 x26 (by linarith)
  have n2527 : z25 ≠ z27 := distinct x25 x27 (by linarith)
  have n2528 : z25 ≠ z28 := distinct x25 x28 (by linarith)
  have n2529 : z25 ≠ z29 := distinct x25 x29 (by linarith)
  have n2627 : z26 ≠ z27 := distinct x26 x27 (by linarith)
  have n2628 : z26 ≠ z28 := distinct x26 x28 (by linarith)
  have n2629 : z26 ≠ z29 := distinct x26 x29 (by linarith)
  have n2728 : z27 ≠ z28 := distinct x27 x28 (by linarith)
  have n2729 : z27 ≠ z29 := distinct x27 x29 (by linarith)
  have n2829 : z28 ≠ z29 := distinct x28 x29 (by linarith)
  set T : Finset ℂ := {z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29} with hTdef
  have hTcard : T.card = 29 := by
    rw [hTdef]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n12, n13, n14, n15, n16, n17, n18, n19, n110, n111, n112, n113, n114, n115, n116, n117, n118, n119, n120, n121, n122, n123, n124, n125, n126, n127, n128, n129⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n23, n24, n25, n26, n27, n28, n29, n210, n211, n212, n213, n214, n215, n216, n217, n218, n219, n220, n221, n222, n223, n224, n225, n226, n227, n228, n229⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n34, n35, n36, n37, n38, n39, n310, n311, n312, n313, n314, n315, n316, n317, n318, n319, n320, n321, n322, n323, n324, n325, n326, n327, n328, n329⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n45, n46, n47, n48, n49, n410, n411, n412, n413, n414, n415, n416, n417, n418, n419, n420, n421, n422, n423, n424, n425, n426, n427, n428, n429⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n56, n57, n58, n59, n510, n511, n512, n513, n514, n515, n516, n517, n518, n519, n520, n521, n522, n523, n524, n525, n526, n527, n528, n529⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n67, n68, n69, n610, n611, n612, n613, n614, n615, n616, n617, n618, n619, n620, n621, n622, n623, n624, n625, n626, n627, n628, n629⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n78, n79, n710, n711, n712, n713, n714, n715, n716, n717, n718, n719, n720, n721, n722, n723, n724, n725, n726, n727, n728, n729⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n89, n810, n811, n812, n813, n814, n815, n816, n817, n818, n819, n820, n821, n822, n823, n824, n825, n826, n827, n828, n829⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n910, n911, n912, n913, n914, n915, n916, n917, n918, n919, n920, n921, n922, n923, n924, n925, n926, n927, n928, n929⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1011, n1012, n1013, n1014, n1015, n1016, n1017, n1018, n1019, n1020, n1021, n1022, n1023, n1024, n1025, n1026, n1027, n1028, n1029⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1112, n1113, n1114, n1115, n1116, n1117, n1118, n1119, n1120, n1121, n1122, n1123, n1124, n1125, n1126, n1127, n1128, n1129⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1213, n1214, n1215, n1216, n1217, n1218, n1219, n1220, n1221, n1222, n1223, n1224, n1225, n1226, n1227, n1228, n1229⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1314, n1315, n1316, n1317, n1318, n1319, n1320, n1321, n1322, n1323, n1324, n1325, n1326, n1327, n1328, n1329⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1415, n1416, n1417, n1418, n1419, n1420, n1421, n1422, n1423, n1424, n1425, n1426, n1427, n1428, n1429⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1516, n1517, n1518, n1519, n1520, n1521, n1522, n1523, n1524, n1525, n1526, n1527, n1528, n1529⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1617, n1618, n1619, n1620, n1621, n1622, n1623, n1624, n1625, n1626, n1627, n1628, n1629⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1718, n1719, n1720, n1721, n1722, n1723, n1724, n1725, n1726, n1727, n1728, n1729⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1819, n1820, n1821, n1822, n1823, n1824, n1825, n1826, n1827, n1828, n1829⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n1920, n1921, n1922, n1923, n1924, n1925, n1926, n1927, n1928, n1929⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2021, n2022, n2023, n2024, n2025, n2026, n2027, n2028, n2029⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2122, n2123, n2124, n2125, n2126, n2127, n2128, n2129⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2223, n2224, n2225, n2226, n2227, n2228, n2229⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2324, n2325, n2326, n2327, n2328, n2329⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2425, n2426, n2427, n2428, n2429⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2526, n2527, n2528, n2529⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2627, n2628, n2629⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨n2728, n2729⟩)]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]; exact n2829)]
    simp
  have hmem_iff : ∀ z ∈ T, z = z1 ∨ z = z2 ∨ z = z3 ∨ z = z4 ∨ z = z5 ∨ z = z6 ∨ z = z7 ∨ z = z8 ∨ z = z9 ∨ z = z10 ∨ z = z11 ∨ z = z12 ∨ z = z13 ∨ z = z14 ∨ z = z15 ∨ z = z16 ∨ z = z17 ∨ z = z18 ∨ z = z19 ∨ z = z20 ∨ z = z21 ∨ z = z22 ∨ z = z23 ∨ z = z24 ∨ z = z25 ∨ z = z26 ∨ z = z27 ∨ z = z28 ∨ z = z29 := by
    intro z hz
    rw [hTdef] at hz
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    intro z hz
    rcases hmem_iff z hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hz1def, hz2def, hz3def, hz4def, hz5def, hz6def, hz7def, hz8def, hz9def, hz10def, hz11def, hz12def, hz13def, hz14def, hz15def, hz16def, hz17def, hz18def, hz19def, hz20def, hz21def, hz22def, hz23def, hz24def, hz25def, hz26def, hz27def, hz28def, hz29def] <;> exact hre_line _
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    intro z hz
    rcases hmem_iff z hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hz1def, hz2def, hz3def, hz4def, hz5def, hz6def, hz7def, hz8def, hz9def, hz10def, hz11def, hz12def, hz13def, hz14def, hz15def, hz16def, hz17def, hz18def, hz19def, hz20def, hz21def, hz22def, hz23def, hz24def, hz25def, hz26def, hz27def, hz28def, hz29def]
    · exact hzeta x1 hΛ1
    · exact hzeta x2 hΛ2
    · exact hzeta x3 hΛ3
    · exact hzeta x4 hΛ4
    · exact hzeta x5 hΛ5
    · exact hzeta x6 hΛ6
    · exact hzeta x7 hΛ7
    · exact hzeta x8 hΛ8
    · exact hzeta x9 hΛ9
    · exact hzeta x10 hΛ10
    · exact hzeta x11 hΛ11
    · exact hzeta x12 hΛ12
    · exact hzeta x13 hΛ13
    · exact hzeta x14 hΛ14
    · exact hzeta x15 hΛ15
    · exact hzeta x16 hΛ16
    · exact hzeta x17 hΛ17
    · exact hzeta x18 hΛ18
    · exact hzeta x19 hΛ19
    · exact hzeta x20 hΛ20
    · exact hzeta x21 hΛ21
    · exact hzeta x22 hΛ22
    · exact hzeta x23 hΛ23
    · exact hzeta x24 hΛ24
    · exact hzeta x25 hΛ25
    · exact hzeta x26 hΛ26
    · exact hzeta x27 hΛ27
    · exact hzeta x28 hΛ28
    · exact hzeta x29 hΛ29
  have hTbox : ∀ z ∈ T, ((((1 / 1000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((999999 / 1000000))) ∧ (((0) : ℝ) ≤ z.im ∧ z.im ≤ (100)) := by
    intro z hz
    rcases hmem_iff z hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hz1def, hz2def, hz3def, hz4def, hz5def, hz6def, hz7def, hz8def, hz9def, hz10def, hz11def, hz12def, hz13def, hz14def, hz15def, hz16def, hz17def, hz18def, hz19def, hz20def, hz21def, hz22def, hz23def, hz24def, hz25def, hz26def, hz27def, hz28def, hz29def] <;>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      first
        | (rw [hre_line]; norm_num)
        | (rw [him_line]; linarith)
  set s0f : Finset ℂ := RHInBoxAnalytic.zeroFinset cPB RPB hs1 with hs0def
  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ) with hd0def
  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (((1 / 1000000)) : ℝ) ((999999 / 1000000)) (0) (100) cPB RPB hRpos hbox_ball hs1
  have hE0box : DifferentiableOn ℂ E0 (Set.Icc (((1 / 1000000)) : ℝ) ((999999 / 1000000)) ×ℂ Set.Icc ((0) : ℝ) (100)) := hE0holo
  have hker0' : ∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
      logDeriv riemannZeta z = (∑ ρ ∈ s0f, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by
    intro z hz hnz
    have := hker0 z hz hnz
    rw [hs0def, hd0def]; exact this
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hwindA⟩ := hArb E0 s0f d0 hE0box hker0'
  have hwind : (∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
        - (∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
        + I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((29 : ℤ) : ℂ) := by
    rw [show (((29 : ℤ) : ℂ)) = (29 : ℂ) by norm_num]; exact hwindA
  have harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc (((1 / 1000000)) : ℝ) ((999999 / 1000000)) ×ℂ Set.Icc ((0) : ℝ) (100)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((0) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 1000000)) : ℝ) < ρ.re ∧ ρ.re < ((999999 / 1000000)) ∧ ((0) : ℝ) < ρ.im ∧ ρ.im < (100)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((0) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) := by
    intro E s d hEholo hkerE
    have hfull := hArb E s d hEholo hkerE
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1, hfull.2.2.2.2.2.1, hfull.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hcountN : (29 : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num
  exact RHInBox.rh_in_box_of_certificate (((1 / 1000000)) : ℝ) ((999999 / 1000000)) (0) (100) cPB RPB 29
    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcountN

end RHInBox_1d1000000_999999d1000000_0_100

/-  Per-box instantiation of `RHInBox.rh_in_box_of_certificate` on the box
    `[(1 / 2000000),(1999999 / 2000000)] x [700,800]` with `N = 77` on-line zeros.

    Emitted by telperion `emit_per_box_instantiation` (Task 4 driver `--box`/`--height`).
    Geometry: ball center `c = ((1 / 2)) + (750)*I`, radius `R = Real.sqrt ((2260001999998000001 / 8000000000000))`,
    chosen so the box is STRICTLY inside the ball and the pole `s = 1` is STRICTLY outside.
    The winding count `N` and on-line zeros are the documented Arb non-kernel inputs
    (supplied as the `hArb`/`hLine` hypotheses).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import RHInBoxAnalytic
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 800000

namespace RHInBox_1d2000000_1999999d2000000_700_800

/-- Chosen Blaschke ball center for the box `[(1 / 2000000),(1999999 / 2000000)] x [700,800]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (750)⟩

/-- Chosen Blaschke ball radius (squared radius `(2260001999998000001 / 8000000000000)`). -/
noncomputable def RPB : ℝ := Real.sqrt ((2260001999998000001 / 8000000000000))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- **RH-in-a-box on `[(1 / 2000000),(1999999 / 2000000)] x [700,800]` with `N = 77`.**  Instantiates the generic
    `RHInBox.rh_in_box_of_certificate` at this box's corners, chosen Blaschke ball
    `c = ((1 / 2)) + (750)*I`, `R = Real.sqrt ((2260001999998000001 / 8000000000000))`, and count `N = 77`.  Takes the
    documented Arb inputs `hLine` (the 77 on-line zeros) and `hArb` (boundary bundle +
    winding `= 2*pi*I*77`).  conjecture1_proved = False. -/
theorem rh_in_box_1d2000000_1999999d2000000_700_800
    (hLine : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 : ℝ,
      (700 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 < x68 ∧ x68 < x69 ∧ x69 < x70 ∧ x70 < x71 ∧ x71 < x72 ∧ x72 < x73 ∧ x73 < x74 ∧ x74 < x75 ∧ x75 < x76 ∧ x76 < x77 ∧ x77 ≤ 800) ∧
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
       completedRiemannZeta (1 / 2 + (x41 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x42 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x43 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x44 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x45 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x46 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x47 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x48 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x49 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x65 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x66 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x67 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x68 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x69 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x70 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x71 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x72 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x73 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x74 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x75 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x76 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x77 : ℂ) * Complex.I) = 0))
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((700) : ℝ) (800)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((700) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((800) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((700) : ℝ) (800), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((700) : ℝ) (800), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((700) : ℝ) < ρ.im ∧ ρ.im < (800)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((700) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((800) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((700)) ((800))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((700)) ((800))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((700) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((800) : ℝ) : ℂ) * I))
          + I • (∫ y in ((700) : ℝ)..(800), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((700) : ℝ)..(800), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (77 : ℂ))) :
    (∀ ρ, ((((1 / 2000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1999999 / 2000000))) → (((700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hsig : (((1 / 2000000)) : ℝ) ≤ ((1999999 / 2000000)) := by norm_num
  have hTle : ((700) : ℝ) ≤ (800) := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((((1 / 2000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1999999 / 2000000))) →
      (((700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (750))]
  have hs1 : (1 : ℂ) ∉ Metric.ball cPB RPB := by
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    intro hlt
    simp only [Complex.one_re, Complex.one_im] at hlt
    have hle : Real.sqrt ((2260001999998000001 / 8000000000000)) ≤
        Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (750)) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    linarith [hlt, hle]
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63, x64, x65, x66, x67, x68, x69, x70, x71, x72, x73, x74, x75, x76, x77, ⟨hlo, hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, hc3334, hc3435, hc3536, hc3637, hc3738, hc3839, hc3940, hc4041, hc4142, hc4243, hc4344, hc4445, hc4546, hc4647, hc4748, hc4849, hc4950, hc5051, hc5152, hc5253, hc5354, hc5455, hc5556, hc5657, hc5758, hc5859, hc5960, hc6061, hc6162, hc6263, hc6364, hc6465, hc6566, hc6667, hc6768, hc6869, hc6970, hc7071, hc7172, hc7273, hc7374, hc7475, hc7576, hc7677, hhi⟩, hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7, hΛ8, hΛ9, hΛ10, hΛ11, hΛ12, hΛ13, hΛ14, hΛ15, hΛ16, hΛ17, hΛ18, hΛ19, hΛ20, hΛ21, hΛ22, hΛ23, hΛ24, hΛ25, hΛ26, hΛ27, hΛ28, hΛ29, hΛ30, hΛ31, hΛ32, hΛ33, hΛ34, hΛ35, hΛ36, hΛ37, hΛ38, hΛ39, hΛ40, hΛ41, hΛ42, hΛ43, hΛ44, hΛ45, hΛ46, hΛ47, hΛ48, hΛ49, hΛ50, hΛ51, hΛ52, hΛ53, hΛ54, hΛ55, hΛ56, hΛ57, hΛ58, hΛ59, hΛ60, hΛ61, hΛ62, hΛ63, hΛ64, hΛ65, hΛ66, hΛ67, hΛ68, hΛ69, hΛ70, hΛ71, hΛ72, hΛ73, hΛ74, hΛ75, hΛ76, hΛ77⟩ := hLine
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
  set xsL : List ℝ := [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63, x64, x65, x66, x67, x68, x69, x70, x71, x72, x73, x74, x75, x76, x77] with hxsdef
  have hchain : xsL.IsChain (· < ·) := by
    rw [hxsdef]
    simp only [List.isChain_cons_cons]
    exact ⟨hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, hc3334, hc3435, hc3536, hc3637, hc3738, hc3839, hc3940, hc4041, hc4142, hc4243, hc4344, hc4445, hc4546, hc4647, hc4748, hc4849, hc4950, hc5051, hc5152, hc5253, hc5354, hc5455, hc5556, hc5657, hc5758, hc5859, hc5960, hc6061, hc6162, hc6263, hc6364, hc6465, hc6566, hc6667, hc6768, hc6869, hc6970, hc7071, hc7172, hc7273, hc7374, hc7475, hc7576, hc7677, List.IsChain.singleton _⟩
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = 77 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hxsdef]
    rfl
  have hmem_list : ∀ t ∈ xsL, t = x1 ∨ t = x2 ∨ t = x3 ∨ t = x4 ∨ t = x5 ∨ t = x6 ∨ t = x7 ∨ t = x8 ∨ t = x9 ∨ t = x10 ∨ t = x11 ∨ t = x12 ∨ t = x13 ∨ t = x14 ∨ t = x15 ∨ t = x16 ∨ t = x17 ∨ t = x18 ∨ t = x19 ∨ t = x20 ∨ t = x21 ∨ t = x22 ∨ t = x23 ∨ t = x24 ∨ t = x25 ∨ t = x26 ∨ t = x27 ∨ t = x28 ∨ t = x29 ∨ t = x30 ∨ t = x31 ∨ t = x32 ∨ t = x33 ∨ t = x34 ∨ t = x35 ∨ t = x36 ∨ t = x37 ∨ t = x38 ∨ t = x39 ∨ t = x40 ∨ t = x41 ∨ t = x42 ∨ t = x43 ∨ t = x44 ∨ t = x45 ∨ t = x46 ∨ t = x47 ∨ t = x48 ∨ t = x49 ∨ t = x50 ∨ t = x51 ∨ t = x52 ∨ t = x53 ∨ t = x54 ∨ t = x55 ∨ t = x56 ∨ t = x57 ∨ t = x58 ∨ t = x59 ∨ t = x60 ∨ t = x61 ∨ t = x62 ∨ t = x63 ∨ t = x64 ∨ t = x65 ∨ t = x66 ∨ t = x67 ∨ t = x68 ∨ t = x69 ∨ t = x70 ∨ t = x71 ∨ t = x72 ∨ t = x73 ∨ t = x74 ∨ t = x75 ∨ t = x76 ∨ t = x77 := by
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
    rcases hmem_list t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact hzeta _ hΛ30
    · exact hzeta _ hΛ31
    · exact hzeta _ hΛ32
    · exact hzeta _ hΛ33
    · exact hzeta _ hΛ34
    · exact hzeta _ hΛ35
    · exact hzeta _ hΛ36
    · exact hzeta _ hΛ37
    · exact hzeta _ hΛ38
    · exact hzeta _ hΛ39
    · exact hzeta _ hΛ40
    · exact hzeta _ hΛ41
    · exact hzeta _ hΛ42
    · exact hzeta _ hΛ43
    · exact hzeta _ hΛ44
    · exact hzeta _ hΛ45
    · exact hzeta _ hΛ46
    · exact hzeta _ hΛ47
    · exact hzeta _ hΛ48
    · exact hzeta _ hΛ49
    · exact hzeta _ hΛ50
    · exact hzeta _ hΛ51
    · exact hzeta _ hΛ52
    · exact hzeta _ hΛ53
    · exact hzeta _ hΛ54
    · exact hzeta _ hΛ55
    · exact hzeta _ hΛ56
    · exact hzeta _ hΛ57
    · exact hzeta _ hΛ58
    · exact hzeta _ hΛ59
    · exact hzeta _ hΛ60
    · exact hzeta _ hΛ61
    · exact hzeta _ hΛ62
    · exact hzeta _ hΛ63
    · exact hzeta _ hΛ64
    · exact hzeta _ hΛ65
    · exact hzeta _ hΛ66
    · exact hzeta _ hΛ67
    · exact hzeta _ hΛ68
    · exact hzeta _ hΛ69
    · exact hzeta _ hΛ70
    · exact hzeta _ hΛ71
    · exact hzeta _ hΛ72
    · exact hzeta _ hΛ73
    · exact hzeta _ hΛ74
    · exact hzeta _ hΛ75
    · exact hzeta _ hΛ76
    · exact hzeta _ hΛ77
  have hTbox : ∀ z ∈ T, ((((1 / 2000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((1999999 / 2000000))) ∧ (((700) : ℝ) ≤ z.im ∧ z.im ≤ (800)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    intro t ht
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hre_line]; norm_num
    · rw [hre_line]; norm_num
    · rw [him_line]
      rcases hmem_list t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
    · rw [him_line]
      rcases hmem_list t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
  set s0f : Finset ℂ := RHInBoxAnalytic.zeroFinset cPB RPB hs1 with hs0def
  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ) with hd0def
  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) (700) (800) cPB RPB hRpos hbox_ball hs1
  have hE0box : DifferentiableOn ℂ E0 (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((700) : ℝ) (800)) := hE0holo
  have hker0' : ∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
      logDeriv riemannZeta z = (∑ ρ ∈ s0f, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by
    intro z hz hnz
    have := hker0 z hz hnz
    rw [hs0def, hd0def]; exact this
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hwindA⟩ := hArb E0 s0f d0 hE0box hker0'
  have hwind : (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((700) : ℝ) : ℂ) * I))
        - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((800) : ℝ) : ℂ) * I))
        + I • (∫ y in ((700) : ℝ)..(800), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((700) : ℝ)..(800), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((77 : ℤ) : ℂ) := by
    rw [show (((77 : ℤ) : ℂ)) = (77 : ℂ) by norm_num]; exact hwindA
  have harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((700) : ℝ) (800)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((700) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((800) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((700) : ℝ) (800), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((700) : ℝ) (800), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((700) : ℝ) < ρ.im ∧ ρ.im < (800)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((700) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((800) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((700)) ((800))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((700)) ((800))) := by
    intro E s d hEholo hkerE
    have hfull := hArb E s d hEholo hkerE
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1, hfull.2.2.2.2.2.1, hfull.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hcountN : (77 : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num
  exact RHInBox.rh_in_box_of_certificate (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) (700) (800) cPB RPB 77
    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcountN

end RHInBox_1d2000000_1999999d2000000_700_800

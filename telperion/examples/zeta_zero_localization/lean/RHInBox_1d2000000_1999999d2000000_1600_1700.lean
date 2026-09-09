/-  Per-box instantiation of `RHInBox.rh_in_box_of_certificate` on the box
    `[(1 / 2000000),(1999999 / 2000000)] x [1600,1700]` with `N = 89` on-line zeros.

    Emitted by telperion `emit_per_box_instantiation` (Task 4 driver `--box`/`--height`).
    Geometry: ball center `c = ((1 / 2)) + (1650)*I`, radius `R = Real.sqrt ((10900001999998000001 / 8000000000000))`,
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

namespace RHInBox_1d2000000_1999999d2000000_1600_1700

/-- Chosen Blaschke ball center for the box `[(1 / 2000000),(1999999 / 2000000)] x [1600,1700]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (1650)⟩

/-- Chosen Blaschke ball radius (squared radius `(10900001999998000001 / 8000000000000)`). -/
noncomputable def RPB : ℝ := Real.sqrt ((10900001999998000001 / 8000000000000))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- **RH-in-a-box on `[(1 / 2000000),(1999999 / 2000000)] x [1600,1700]` with `N = 89`.**  Instantiates the generic
    `RHInBox.rh_in_box_of_certificate` at this box's corners, chosen Blaschke ball
    `c = ((1 / 2)) + (1650)*I`, `R = Real.sqrt ((10900001999998000001 / 8000000000000))`, and count `N = 89`.  Takes the
    documented Arb inputs `hLine` (the 89 on-line zeros) and `hArb` (boundary bundle +
    winding `= 2*pi*I*89`).  conjecture1_proved = False. -/
theorem rh_in_box_1d2000000_1999999d2000000_1600_1700
    (hLine : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 : ℝ,
      (1600 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 < x68 ∧ x68 < x69 ∧ x69 < x70 ∧ x70 < x71 ∧ x71 < x72 ∧ x72 < x73 ∧ x73 < x74 ∧ x74 < x75 ∧ x75 < x76 ∧ x76 < x77 ∧ x77 < x78 ∧ x78 < x79 ∧ x79 < x80 ∧ x80 < x81 ∧ x81 < x82 ∧ x82 < x83 ∧ x83 < x84 ∧ x84 < x85 ∧ x85 < x86 ∧ x86 < x87 ∧ x87 < x88 ∧ x88 < x89 ∧ x89 ≤ 1700) ∧
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
       completedRiemannZeta (1 / 2 + (x77 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x78 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x79 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x80 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x81 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x82 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x83 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x84 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x85 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x86 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x87 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x88 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x89 : ℂ) * Complex.I) = 0))
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((1600) : ℝ) (1700)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((1600) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((1700) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((1600) : ℝ) (1700), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((1600) : ℝ) (1700), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((1600) : ℝ) < ρ.im ∧ ρ.im < (1700)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((1600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((1700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((1600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((1700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((1600) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((1700) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((1600)) ((1700))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((1600) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((1700) : ℝ) : ℂ) * I))
          + I • (∫ y in ((1600) : ℝ)..(1700), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((1600) : ℝ)..(1700), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (89 : ℂ))) :
    (∀ ρ, ((((1 / 2000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1999999 / 2000000))) → (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1700)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hsig : (((1 / 2000000)) : ℝ) ≤ ((1999999 / 2000000)) := by norm_num
  have hTle : ((1600) : ℝ) ≤ (1700) := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((((1 / 2000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1999999 / 2000000))) →
      (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1700)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (1650))]
  have hs1 : (1 : ℂ) ∉ Metric.ball cPB RPB := by
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    intro hlt
    simp only [Complex.one_re, Complex.one_im] at hlt
    have hle : Real.sqrt ((10900001999998000001 / 8000000000000)) ≤
        Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (1650)) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    linarith [hlt, hle]
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63, x64, x65, x66, x67, x68, x69, x70, x71, x72, x73, x74, x75, x76, x77, x78, x79, x80, x81, x82, x83, x84, x85, x86, x87, x88, x89, ⟨hlo, hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, hc3334, hc3435, hc3536, hc3637, hc3738, hc3839, hc3940, hc4041, hc4142, hc4243, hc4344, hc4445, hc4546, hc4647, hc4748, hc4849, hc4950, hc5051, hc5152, hc5253, hc5354, hc5455, hc5556, hc5657, hc5758, hc5859, hc5960, hc6061, hc6162, hc6263, hc6364, hc6465, hc6566, hc6667, hc6768, hc6869, hc6970, hc7071, hc7172, hc7273, hc7374, hc7475, hc7576, hc7677, hc7778, hc7879, hc7980, hc8081, hc8182, hc8283, hc8384, hc8485, hc8586, hc8687, hc8788, hc8889, hhi⟩, hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7, hΛ8, hΛ9, hΛ10, hΛ11, hΛ12, hΛ13, hΛ14, hΛ15, hΛ16, hΛ17, hΛ18, hΛ19, hΛ20, hΛ21, hΛ22, hΛ23, hΛ24, hΛ25, hΛ26, hΛ27, hΛ28, hΛ29, hΛ30, hΛ31, hΛ32, hΛ33, hΛ34, hΛ35, hΛ36, hΛ37, hΛ38, hΛ39, hΛ40, hΛ41, hΛ42, hΛ43, hΛ44, hΛ45, hΛ46, hΛ47, hΛ48, hΛ49, hΛ50, hΛ51, hΛ52, hΛ53, hΛ54, hΛ55, hΛ56, hΛ57, hΛ58, hΛ59, hΛ60, hΛ61, hΛ62, hΛ63, hΛ64, hΛ65, hΛ66, hΛ67, hΛ68, hΛ69, hΛ70, hΛ71, hΛ72, hΛ73, hΛ74, hΛ75, hΛ76, hΛ77, hΛ78, hΛ79, hΛ80, hΛ81, hΛ82, hΛ83, hΛ84, hΛ85, hΛ86, hΛ87, hΛ88, hΛ89⟩ := hLine
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
  set xsL : List ℝ := [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63, x64, x65, x66, x67, x68, x69, x70, x71, x72, x73, x74, x75, x76, x77, x78, x79, x80, x81, x82, x83, x84, x85, x86, x87, x88, x89] with hxsdef
  have hchain : xsL.IsChain (· < ·) := by
    rw [hxsdef]
    simp only [List.isChain_cons_cons]
    exact ⟨hc12, hc23, hc34, hc45, hc56, hc67, hc78, hc89, hc910, hc1011, hc1112, hc1213, hc1314, hc1415, hc1516, hc1617, hc1718, hc1819, hc1920, hc2021, hc2122, hc2223, hc2324, hc2425, hc2526, hc2627, hc2728, hc2829, hc2930, hc3031, hc3132, hc3233, hc3334, hc3435, hc3536, hc3637, hc3738, hc3839, hc3940, hc4041, hc4142, hc4243, hc4344, hc4445, hc4546, hc4647, hc4748, hc4849, hc4950, hc5051, hc5152, hc5253, hc5354, hc5455, hc5556, hc5657, hc5758, hc5859, hc5960, hc6061, hc6162, hc6263, hc6364, hc6465, hc6566, hc6667, hc6768, hc6869, hc6970, hc7071, hc7172, hc7273, hc7374, hc7475, hc7576, hc7677, hc7778, hc7879, hc7980, hc8081, hc8182, hc8283, hc8384, hc8485, hc8586, hc8687, hc8788, hc8889, List.IsChain.singleton _⟩
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = 89 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hxsdef]
    rfl
  have hb1 : ((1600) : ℝ) ≤ x1 := hlo
  have hb2 : ((1600) : ℝ) ≤ x2 := le_trans hb1 (le_of_lt hc12)
  have hb3 : ((1600) : ℝ) ≤ x3 := le_trans hb2 (le_of_lt hc23)
  have hb4 : ((1600) : ℝ) ≤ x4 := le_trans hb3 (le_of_lt hc34)
  have hb5 : ((1600) : ℝ) ≤ x5 := le_trans hb4 (le_of_lt hc45)
  have hb6 : ((1600) : ℝ) ≤ x6 := le_trans hb5 (le_of_lt hc56)
  have hb7 : ((1600) : ℝ) ≤ x7 := le_trans hb6 (le_of_lt hc67)
  have hb8 : ((1600) : ℝ) ≤ x8 := le_trans hb7 (le_of_lt hc78)
  have hb9 : ((1600) : ℝ) ≤ x9 := le_trans hb8 (le_of_lt hc89)
  have hb10 : ((1600) : ℝ) ≤ x10 := le_trans hb9 (le_of_lt hc910)
  have hb11 : ((1600) : ℝ) ≤ x11 := le_trans hb10 (le_of_lt hc1011)
  have hb12 : ((1600) : ℝ) ≤ x12 := le_trans hb11 (le_of_lt hc1112)
  have hb13 : ((1600) : ℝ) ≤ x13 := le_trans hb12 (le_of_lt hc1213)
  have hb14 : ((1600) : ℝ) ≤ x14 := le_trans hb13 (le_of_lt hc1314)
  have hb15 : ((1600) : ℝ) ≤ x15 := le_trans hb14 (le_of_lt hc1415)
  have hb16 : ((1600) : ℝ) ≤ x16 := le_trans hb15 (le_of_lt hc1516)
  have hb17 : ((1600) : ℝ) ≤ x17 := le_trans hb16 (le_of_lt hc1617)
  have hb18 : ((1600) : ℝ) ≤ x18 := le_trans hb17 (le_of_lt hc1718)
  have hb19 : ((1600) : ℝ) ≤ x19 := le_trans hb18 (le_of_lt hc1819)
  have hb20 : ((1600) : ℝ) ≤ x20 := le_trans hb19 (le_of_lt hc1920)
  have hb21 : ((1600) : ℝ) ≤ x21 := le_trans hb20 (le_of_lt hc2021)
  have hb22 : ((1600) : ℝ) ≤ x22 := le_trans hb21 (le_of_lt hc2122)
  have hb23 : ((1600) : ℝ) ≤ x23 := le_trans hb22 (le_of_lt hc2223)
  have hb24 : ((1600) : ℝ) ≤ x24 := le_trans hb23 (le_of_lt hc2324)
  have hb25 : ((1600) : ℝ) ≤ x25 := le_trans hb24 (le_of_lt hc2425)
  have hb26 : ((1600) : ℝ) ≤ x26 := le_trans hb25 (le_of_lt hc2526)
  have hb27 : ((1600) : ℝ) ≤ x27 := le_trans hb26 (le_of_lt hc2627)
  have hb28 : ((1600) : ℝ) ≤ x28 := le_trans hb27 (le_of_lt hc2728)
  have hb29 : ((1600) : ℝ) ≤ x29 := le_trans hb28 (le_of_lt hc2829)
  have hb30 : ((1600) : ℝ) ≤ x30 := le_trans hb29 (le_of_lt hc2930)
  have hb31 : ((1600) : ℝ) ≤ x31 := le_trans hb30 (le_of_lt hc3031)
  have hb32 : ((1600) : ℝ) ≤ x32 := le_trans hb31 (le_of_lt hc3132)
  have hb33 : ((1600) : ℝ) ≤ x33 := le_trans hb32 (le_of_lt hc3233)
  have hb34 : ((1600) : ℝ) ≤ x34 := le_trans hb33 (le_of_lt hc3334)
  have hb35 : ((1600) : ℝ) ≤ x35 := le_trans hb34 (le_of_lt hc3435)
  have hb36 : ((1600) : ℝ) ≤ x36 := le_trans hb35 (le_of_lt hc3536)
  have hb37 : ((1600) : ℝ) ≤ x37 := le_trans hb36 (le_of_lt hc3637)
  have hb38 : ((1600) : ℝ) ≤ x38 := le_trans hb37 (le_of_lt hc3738)
  have hb39 : ((1600) : ℝ) ≤ x39 := le_trans hb38 (le_of_lt hc3839)
  have hb40 : ((1600) : ℝ) ≤ x40 := le_trans hb39 (le_of_lt hc3940)
  have hb41 : ((1600) : ℝ) ≤ x41 := le_trans hb40 (le_of_lt hc4041)
  have hb42 : ((1600) : ℝ) ≤ x42 := le_trans hb41 (le_of_lt hc4142)
  have hb43 : ((1600) : ℝ) ≤ x43 := le_trans hb42 (le_of_lt hc4243)
  have hb44 : ((1600) : ℝ) ≤ x44 := le_trans hb43 (le_of_lt hc4344)
  have hb45 : ((1600) : ℝ) ≤ x45 := le_trans hb44 (le_of_lt hc4445)
  have hb46 : ((1600) : ℝ) ≤ x46 := le_trans hb45 (le_of_lt hc4546)
  have hb47 : ((1600) : ℝ) ≤ x47 := le_trans hb46 (le_of_lt hc4647)
  have hb48 : ((1600) : ℝ) ≤ x48 := le_trans hb47 (le_of_lt hc4748)
  have hb49 : ((1600) : ℝ) ≤ x49 := le_trans hb48 (le_of_lt hc4849)
  have hb50 : ((1600) : ℝ) ≤ x50 := le_trans hb49 (le_of_lt hc4950)
  have hb51 : ((1600) : ℝ) ≤ x51 := le_trans hb50 (le_of_lt hc5051)
  have hb52 : ((1600) : ℝ) ≤ x52 := le_trans hb51 (le_of_lt hc5152)
  have hb53 : ((1600) : ℝ) ≤ x53 := le_trans hb52 (le_of_lt hc5253)
  have hb54 : ((1600) : ℝ) ≤ x54 := le_trans hb53 (le_of_lt hc5354)
  have hb55 : ((1600) : ℝ) ≤ x55 := le_trans hb54 (le_of_lt hc5455)
  have hb56 : ((1600) : ℝ) ≤ x56 := le_trans hb55 (le_of_lt hc5556)
  have hb57 : ((1600) : ℝ) ≤ x57 := le_trans hb56 (le_of_lt hc5657)
  have hb58 : ((1600) : ℝ) ≤ x58 := le_trans hb57 (le_of_lt hc5758)
  have hb59 : ((1600) : ℝ) ≤ x59 := le_trans hb58 (le_of_lt hc5859)
  have hb60 : ((1600) : ℝ) ≤ x60 := le_trans hb59 (le_of_lt hc5960)
  have hb61 : ((1600) : ℝ) ≤ x61 := le_trans hb60 (le_of_lt hc6061)
  have hb62 : ((1600) : ℝ) ≤ x62 := le_trans hb61 (le_of_lt hc6162)
  have hb63 : ((1600) : ℝ) ≤ x63 := le_trans hb62 (le_of_lt hc6263)
  have hb64 : ((1600) : ℝ) ≤ x64 := le_trans hb63 (le_of_lt hc6364)
  have hb65 : ((1600) : ℝ) ≤ x65 := le_trans hb64 (le_of_lt hc6465)
  have hb66 : ((1600) : ℝ) ≤ x66 := le_trans hb65 (le_of_lt hc6566)
  have hb67 : ((1600) : ℝ) ≤ x67 := le_trans hb66 (le_of_lt hc6667)
  have hb68 : ((1600) : ℝ) ≤ x68 := le_trans hb67 (le_of_lt hc6768)
  have hb69 : ((1600) : ℝ) ≤ x69 := le_trans hb68 (le_of_lt hc6869)
  have hb70 : ((1600) : ℝ) ≤ x70 := le_trans hb69 (le_of_lt hc6970)
  have hb71 : ((1600) : ℝ) ≤ x71 := le_trans hb70 (le_of_lt hc7071)
  have hb72 : ((1600) : ℝ) ≤ x72 := le_trans hb71 (le_of_lt hc7172)
  have hb73 : ((1600) : ℝ) ≤ x73 := le_trans hb72 (le_of_lt hc7273)
  have hb74 : ((1600) : ℝ) ≤ x74 := le_trans hb73 (le_of_lt hc7374)
  have hb75 : ((1600) : ℝ) ≤ x75 := le_trans hb74 (le_of_lt hc7475)
  have hb76 : ((1600) : ℝ) ≤ x76 := le_trans hb75 (le_of_lt hc7576)
  have hb77 : ((1600) : ℝ) ≤ x77 := le_trans hb76 (le_of_lt hc7677)
  have hb78 : ((1600) : ℝ) ≤ x78 := le_trans hb77 (le_of_lt hc7778)
  have hb79 : ((1600) : ℝ) ≤ x79 := le_trans hb78 (le_of_lt hc7879)
  have hb80 : ((1600) : ℝ) ≤ x80 := le_trans hb79 (le_of_lt hc7980)
  have hb81 : ((1600) : ℝ) ≤ x81 := le_trans hb80 (le_of_lt hc8081)
  have hb82 : ((1600) : ℝ) ≤ x82 := le_trans hb81 (le_of_lt hc8182)
  have hb83 : ((1600) : ℝ) ≤ x83 := le_trans hb82 (le_of_lt hc8283)
  have hb84 : ((1600) : ℝ) ≤ x84 := le_trans hb83 (le_of_lt hc8384)
  have hb85 : ((1600) : ℝ) ≤ x85 := le_trans hb84 (le_of_lt hc8485)
  have hb86 : ((1600) : ℝ) ≤ x86 := le_trans hb85 (le_of_lt hc8586)
  have hb87 : ((1600) : ℝ) ≤ x87 := le_trans hb86 (le_of_lt hc8687)
  have hb88 : ((1600) : ℝ) ≤ x88 := le_trans hb87 (le_of_lt hc8788)
  have hb89 : ((1600) : ℝ) ≤ x89 := le_trans hb88 (le_of_lt hc8889)
  have hu89 : x89 ≤ ((1700) : ℝ) := hhi
  have hu88 : x88 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8889) hu89
  have hu87 : x87 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8788) hu88
  have hu86 : x86 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8687) hu87
  have hu85 : x85 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8586) hu86
  have hu84 : x84 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8485) hu85
  have hu83 : x83 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8384) hu84
  have hu82 : x82 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8283) hu83
  have hu81 : x81 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8182) hu82
  have hu80 : x80 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc8081) hu81
  have hu79 : x79 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7980) hu80
  have hu78 : x78 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7879) hu79
  have hu77 : x77 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7778) hu78
  have hu76 : x76 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7677) hu77
  have hu75 : x75 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7576) hu76
  have hu74 : x74 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7475) hu75
  have hu73 : x73 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7374) hu74
  have hu72 : x72 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7273) hu73
  have hu71 : x71 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7172) hu72
  have hu70 : x70 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc7071) hu71
  have hu69 : x69 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6970) hu70
  have hu68 : x68 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6869) hu69
  have hu67 : x67 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6768) hu68
  have hu66 : x66 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6667) hu67
  have hu65 : x65 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6566) hu66
  have hu64 : x64 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6465) hu65
  have hu63 : x63 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6364) hu64
  have hu62 : x62 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6263) hu63
  have hu61 : x61 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6162) hu62
  have hu60 : x60 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc6061) hu61
  have hu59 : x59 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5960) hu60
  have hu58 : x58 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5859) hu59
  have hu57 : x57 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5758) hu58
  have hu56 : x56 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5657) hu57
  have hu55 : x55 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5556) hu56
  have hu54 : x54 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5455) hu55
  have hu53 : x53 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5354) hu54
  have hu52 : x52 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5253) hu53
  have hu51 : x51 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5152) hu52
  have hu50 : x50 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc5051) hu51
  have hu49 : x49 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4950) hu50
  have hu48 : x48 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4849) hu49
  have hu47 : x47 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4748) hu48
  have hu46 : x46 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4647) hu47
  have hu45 : x45 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4546) hu46
  have hu44 : x44 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4445) hu45
  have hu43 : x43 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4344) hu44
  have hu42 : x42 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4243) hu43
  have hu41 : x41 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4142) hu42
  have hu40 : x40 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc4041) hu41
  have hu39 : x39 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3940) hu40
  have hu38 : x38 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3839) hu39
  have hu37 : x37 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3738) hu38
  have hu36 : x36 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3637) hu37
  have hu35 : x35 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3536) hu36
  have hu34 : x34 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3435) hu35
  have hu33 : x33 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3334) hu34
  have hu32 : x32 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3233) hu33
  have hu31 : x31 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3132) hu32
  have hu30 : x30 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc3031) hu31
  have hu29 : x29 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2930) hu30
  have hu28 : x28 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2829) hu29
  have hu27 : x27 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2728) hu28
  have hu26 : x26 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2627) hu27
  have hu25 : x25 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2526) hu26
  have hu24 : x24 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2425) hu25
  have hu23 : x23 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2324) hu24
  have hu22 : x22 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2223) hu23
  have hu21 : x21 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2122) hu22
  have hu20 : x20 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc2021) hu21
  have hu19 : x19 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1920) hu20
  have hu18 : x18 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1819) hu19
  have hu17 : x17 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1718) hu18
  have hu16 : x16 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1617) hu17
  have hu15 : x15 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1516) hu16
  have hu14 : x14 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1415) hu15
  have hu13 : x13 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1314) hu14
  have hu12 : x12 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1213) hu13
  have hu11 : x11 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1112) hu12
  have hu10 : x10 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc1011) hu11
  have hu9 : x9 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc910) hu10
  have hu8 : x8 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc89) hu9
  have hu7 : x7 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc78) hu8
  have hu6 : x6 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc67) hu7
  have hu5 : x5 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc56) hu6
  have hu4 : x4 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc45) hu5
  have hu3 : x3 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc34) hu4
  have hu2 : x2 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc23) hu3
  have hu1 : x1 ≤ ((1700) : ℝ) := le_trans (le_of_lt hc12) hu2
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
    exact ⟨hzeta x1 hΛ1, hzeta x2 hΛ2, hzeta x3 hΛ3, hzeta x4 hΛ4, hzeta x5 hΛ5, hzeta x6 hΛ6, hzeta x7 hΛ7, hzeta x8 hΛ8, hzeta x9 hΛ9, hzeta x10 hΛ10, hzeta x11 hΛ11, hzeta x12 hΛ12, hzeta x13 hΛ13, hzeta x14 hΛ14, hzeta x15 hΛ15, hzeta x16 hΛ16, hzeta x17 hΛ17, hzeta x18 hΛ18, hzeta x19 hΛ19, hzeta x20 hΛ20, hzeta x21 hΛ21, hzeta x22 hΛ22, hzeta x23 hΛ23, hzeta x24 hΛ24, hzeta x25 hΛ25, hzeta x26 hΛ26, hzeta x27 hΛ27, hzeta x28 hΛ28, hzeta x29 hΛ29, hzeta x30 hΛ30, hzeta x31 hΛ31, hzeta x32 hΛ32, hzeta x33 hΛ33, hzeta x34 hΛ34, hzeta x35 hΛ35, hzeta x36 hΛ36, hzeta x37 hΛ37, hzeta x38 hΛ38, hzeta x39 hΛ39, hzeta x40 hΛ40, hzeta x41 hΛ41, hzeta x42 hΛ42, hzeta x43 hΛ43, hzeta x44 hΛ44, hzeta x45 hΛ45, hzeta x46 hΛ46, hzeta x47 hΛ47, hzeta x48 hΛ48, hzeta x49 hΛ49, hzeta x50 hΛ50, hzeta x51 hΛ51, hzeta x52 hΛ52, hzeta x53 hΛ53, hzeta x54 hΛ54, hzeta x55 hΛ55, hzeta x56 hΛ56, hzeta x57 hΛ57, hzeta x58 hΛ58, hzeta x59 hΛ59, hzeta x60 hΛ60, hzeta x61 hΛ61, hzeta x62 hΛ62, hzeta x63 hΛ63, hzeta x64 hΛ64, hzeta x65 hΛ65, hzeta x66 hΛ66, hzeta x67 hΛ67, hzeta x68 hΛ68, hzeta x69 hΛ69, hzeta x70 hΛ70, hzeta x71 hΛ71, hzeta x72 hΛ72, hzeta x73 hΛ73, hzeta x74 hΛ74, hzeta x75 hΛ75, hzeta x76 hΛ76, hzeta x77 hΛ77, hzeta x78 hΛ78, hzeta x79 hΛ79, hzeta x80 hΛ80, hzeta x81 hΛ81, hzeta x82 hΛ82, hzeta x83 hΛ83, hzeta x84 hΛ84, hzeta x85 hΛ85, hzeta x86 hΛ86, hzeta x87 hΛ87, hzeta x88 hΛ88, hzeta x89 hΛ89, List.forall_mem_nil _⟩
  have hTbox : ∀ z ∈ T, ((((1 / 2000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((1999999 / 2000000))) ∧ (((1600) : ℝ) ≤ z.im ∧ z.im ≤ (1700)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL ?_
    rw [hxsdef]
    simp only [List.forall_mem_cons]
    exact ⟨⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb1, by rw [him_line]; exact hu1⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb2, by rw [him_line]; exact hu2⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb3, by rw [him_line]; exact hu3⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb4, by rw [him_line]; exact hu4⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb5, by rw [him_line]; exact hu5⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb6, by rw [him_line]; exact hu6⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb7, by rw [him_line]; exact hu7⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb8, by rw [him_line]; exact hu8⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb9, by rw [him_line]; exact hu9⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb10, by rw [him_line]; exact hu10⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb11, by rw [him_line]; exact hu11⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb12, by rw [him_line]; exact hu12⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb13, by rw [him_line]; exact hu13⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb14, by rw [him_line]; exact hu14⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb15, by rw [him_line]; exact hu15⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb16, by rw [him_line]; exact hu16⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb17, by rw [him_line]; exact hu17⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb18, by rw [him_line]; exact hu18⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb19, by rw [him_line]; exact hu19⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb20, by rw [him_line]; exact hu20⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb21, by rw [him_line]; exact hu21⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb22, by rw [him_line]; exact hu22⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb23, by rw [him_line]; exact hu23⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb24, by rw [him_line]; exact hu24⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb25, by rw [him_line]; exact hu25⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb26, by rw [him_line]; exact hu26⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb27, by rw [him_line]; exact hu27⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb28, by rw [him_line]; exact hu28⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb29, by rw [him_line]; exact hu29⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb30, by rw [him_line]; exact hu30⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb31, by rw [him_line]; exact hu31⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb32, by rw [him_line]; exact hu32⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb33, by rw [him_line]; exact hu33⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb34, by rw [him_line]; exact hu34⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb35, by rw [him_line]; exact hu35⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb36, by rw [him_line]; exact hu36⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb37, by rw [him_line]; exact hu37⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb38, by rw [him_line]; exact hu38⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb39, by rw [him_line]; exact hu39⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb40, by rw [him_line]; exact hu40⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb41, by rw [him_line]; exact hu41⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb42, by rw [him_line]; exact hu42⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb43, by rw [him_line]; exact hu43⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb44, by rw [him_line]; exact hu44⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb45, by rw [him_line]; exact hu45⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb46, by rw [him_line]; exact hu46⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb47, by rw [him_line]; exact hu47⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb48, by rw [him_line]; exact hu48⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb49, by rw [him_line]; exact hu49⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb50, by rw [him_line]; exact hu50⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb51, by rw [him_line]; exact hu51⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb52, by rw [him_line]; exact hu52⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb53, by rw [him_line]; exact hu53⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb54, by rw [him_line]; exact hu54⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb55, by rw [him_line]; exact hu55⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb56, by rw [him_line]; exact hu56⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb57, by rw [him_line]; exact hu57⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb58, by rw [him_line]; exact hu58⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb59, by rw [him_line]; exact hu59⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb60, by rw [him_line]; exact hu60⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb61, by rw [him_line]; exact hu61⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb62, by rw [him_line]; exact hu62⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb63, by rw [him_line]; exact hu63⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb64, by rw [him_line]; exact hu64⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb65, by rw [him_line]; exact hu65⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb66, by rw [him_line]; exact hu66⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb67, by rw [him_line]; exact hu67⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb68, by rw [him_line]; exact hu68⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb69, by rw [him_line]; exact hu69⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb70, by rw [him_line]; exact hu70⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb71, by rw [him_line]; exact hu71⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb72, by rw [him_line]; exact hu72⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb73, by rw [him_line]; exact hu73⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb74, by rw [him_line]; exact hu74⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb75, by rw [him_line]; exact hu75⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb76, by rw [him_line]; exact hu76⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb77, by rw [him_line]; exact hu77⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb78, by rw [him_line]; exact hu78⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb79, by rw [him_line]; exact hu79⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb80, by rw [him_line]; exact hu80⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb81, by rw [him_line]; exact hu81⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb82, by rw [him_line]; exact hu82⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb83, by rw [him_line]; exact hu83⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb84, by rw [him_line]; exact hu84⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb85, by rw [him_line]; exact hu85⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb86, by rw [him_line]; exact hu86⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb87, by rw [him_line]; exact hu87⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb88, by rw [him_line]; exact hu88⟩, ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩, by rw [him_line]; exact hb89, by rw [him_line]; exact hu89⟩, List.forall_mem_nil _⟩
  set s0f : Finset ℂ := RHInBoxAnalytic.zeroFinset cPB RPB hs1 with hs0def
  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ) with hd0def
  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) (1600) (1700) cPB RPB hRpos hbox_ball hs1
  have hE0box : DifferentiableOn ℂ E0 (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((1600) : ℝ) (1700)) := hE0holo
  have hker0' : ∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
      logDeriv riemannZeta z = (∑ ρ ∈ s0f, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by
    intro z hz hnz
    have := hker0 z hz hnz
    rw [hs0def, hd0def]; exact this
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hwindA⟩ := hArb E0 s0f d0 hE0box hker0'
  have hwind : (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((1600) : ℝ) : ℂ) * I))
        - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((1700) : ℝ) : ℂ) * I))
        + I • (∫ y in ((1600) : ℝ)..(1700), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((1600) : ℝ)..(1700), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((89 : ℤ) : ℂ) := by
    rw [show (((89 : ℤ) : ℂ)) = (89 : ℂ) by norm_num]; exact hwindA
  have harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((1600) : ℝ) (1700)) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((1600) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((1700) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((1600) : ℝ) (1700), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((1600) : ℝ) (1700), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((1600) : ℝ) < ρ.im ∧ ρ.im < (1700)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((1600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((1700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((1600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((1700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((1600) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((1700) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((1600)) ((1700))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((1600)) ((1700))) := by
    intro E s d hEholo hkerE
    have hfull := hArb E s d hEholo hkerE
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1, hfull.2.2.2.2.2.1, hfull.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfull.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hcountN : (89 : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num
  exact RHInBox.rh_in_box_of_certificate (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) (1600) (1700) cPB RPB 89
    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcountN

end RHInBox_1d2000000_1999999d2000000_1600_1700

/-  Empty-band (zero-free) certificate for the box `[(1 / 1000),(999 / 1000)] x [0,(55 / 16)]`.

    Emitted by telperion `emit_empty_band_instantiation`.  Boundary winding `N = 0`
    (Arb non-kernel input `hwind`) + the routine boundary bundle `hArb` feed
    `RHInBoxAnalytic.zeta_count_eq_winding_generic` at `N = 0`; the resulting divisor
    support has `∑ d = 0` with `d ≥ 1`, forcing it EMPTY, so the box holds no zeta zero.
    Ball center `c = ((1 / 2)) + ((55 / 32))*I`, radius `R = Real.sqrt ((51257633 / 16000000))` (box strictly
    inside, pole `s = 1` strictly outside).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import RvMRHInBox
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

namespace NoZerosInBox_1d1000_999d1000_0_55d16

/-- Chosen Blaschke ball center for `[(1 / 1000),(999 / 1000)] x [0,(55 / 16)]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), ((55 / 32))⟩

/-- Chosen Blaschke ball radius (squared radius `(51257633 / 16000000)`). -/
noncomputable def RPB : ℝ := Real.sqrt ((51257633 / 16000000))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- The pole `s = 1` is strictly outside the chosen ball. -/
theorem hs1_PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((51257633 / 16000000)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - ((55 / 32))) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-- **Zero-free box `[(1 / 1000),(999 / 1000)] x [0,(55 / 16)]` via winding `N = 0`.**  Instantiates
    `RHInBoxAnalytic.zeta_count_eq_winding_generic` at `N = 0`; the empty divisor support
    means no zeta zero lies in the box.  Documented Arb inputs: `hwind` (winding `= 0`) and
    `hArb` (boundary bundle).  conjecture1_proved = False. -/
theorem no_zeros_in_box_1d1000_999d1000_0_55d16
    (hwind : (∫ x in (((1 / 1000)) : ℝ)..((999 / 1000)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
        - (∫ x in (((1 / 1000)) : ℝ)..((999 / 1000)), logDeriv riemannZeta (↑x + ((((55 / 16)) : ℝ) : ℂ) * I))
        + I • (∫ y in ((0) : ℝ)..((55 / 16)), logDeriv riemannZeta (((((999 / 1000)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((0) : ℝ)..((55 / 16)), logDeriv riemannZeta (((((1 / 1000)) : ℝ) : ℂ) + ↑y * I))
      = 0)
    (hArb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1_PB
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc (((1 / 1000)) : ℝ) ((999 / 1000)) ×ℂ Set.Icc ((0) : ℝ) ((55 / 16))) →
      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 1000)) : ℝ) ((999 / 1000)), riemannZeta (↑x + (((0) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 1000)) : ℝ) ((999 / 1000)), riemannZeta (↑x + ((((55 / 16)) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) ((55 / 16)), riemannZeta (((((999 / 1000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) ((55 / 16)), riemannZeta (((((1 / 1000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 1000)) : ℝ) < ρ.re ∧ ρ.re < ((999 / 1000)) ∧ ((0) : ℝ) < ρ.im ∧ ρ.im < ((55 / 16))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000))) (((999 / 1000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((((55 / 16)) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000))) (((999 / 1000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((999 / 1000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) (((55 / 16)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 1000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) (((55 / 16)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000))) (((999 / 1000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((((55 / 16)) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000))) (((999 / 1000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((999 / 1000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) (((55 / 16)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 1000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) (((55 / 16)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((0) : ℝ) : ℂ) * I)) volume (((1 / 1000))) (((999 / 1000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((((55 / 16)) : ℝ) : ℂ) * I)) volume (((1 / 1000))) (((999 / 1000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((999 / 1000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) (((55 / 16)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 1000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) (((55 / 16))))) :
    (∀ ρ : ℂ, ((((1 / 1000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999 / 1000))) → (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) →
      riemannZeta ρ ≠ 0) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hsig : (((1 / 1000)) : ℝ) ≤ ((999 / 1000)) := by norm_num
  have hTle : ((0) : ℝ) ≤ ((55 / 16)) := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((((1 / 1000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999 / 1000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - ((55 / 32)))]
  have hwind0 : (∫ x in (((1 / 1000)) : ℝ)..((999 / 1000)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
        - (∫ x in (((1 / 1000)) : ℝ)..((999 / 1000)), logDeriv riemannZeta (↑x + ((((55 / 16)) : ℝ) : ℂ) * I))
        + I • (∫ y in ((0) : ℝ)..((55 / 16)), logDeriv riemannZeta (((((999 / 1000)) : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in ((0) : ℝ)..((55 / 16)), logDeriv riemannZeta (((((1 / 1000)) : ℝ) : ℂ) + ↑y * I))
      = 2 * π * I * ((0 : ℤ) : ℂ) := by rw [hwind]; simp
  obtain ⟨s, d, hd1, hcap, hsum⟩ :=
    RHInBoxAnalytic.zeta_count_eq_winding_generic (((1 / 1000)) : ℝ) ((999 / 1000)) (0) ((55 / 16))
      cPB RPB 0 hRpos hsig hTle hbox_ball hs1_PB hwind0 hArb
  intro ρ hre him hzero
  have hin : ρ ∈ s := hcap ρ hre him hzero
  have hnonneg : ∀ ρ' ∈ s, (0 : ℤ) ≤ d ρ' := fun ρ' hρ' => le_trans (by norm_num) (hd1 ρ' hρ')
  have hle : d ρ ≤ ∑ ρ' ∈ s, d ρ' := Finset.single_le_sum hnonneg hin
  rw [hsum] at hle
  have h1 := hd1 ρ hin
  omega

end NoZerosInBox_1d1000_999d1000_0_55d16

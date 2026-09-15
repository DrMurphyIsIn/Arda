/- STRIP CLEARING (kernel glue): discharge the `55/16` height-floor hypothesis `hγ` of
   `AllZeros_h100.all_nontrivial_zeros_up_to_height_100` from the two winding-0 empty-band
   certificates (#329 band + #332 left sliver) and the critical-line reflection (#320).

   The strip decomposition (interface doc §6.1-6.2, corrected route of #332):
     * `Re ∈ (0, 1/1000]`        — left-sliver box cert  `NoZerosInBox_0_1d1000_0_55d16`;
     * `Re ∈ [1/1000, 999/1000]` — band box cert         `NoZerosInBox_1d1000_999d1000_0_55d16`;
     * `Re ∈ (999/1000, 1)`      — reflect `ρ ↦ 1 − conj ρ` (Im-preserving,
       `ZeroFreeBridge.riemannZeta_reflect_line_eq_zero`) into the left sliver.
   Then `ZetaZeroConfinement.no_low_zeros_of_strip_clear` yields the height floor, and the
   headline wrapper re-exports `all_nontrivial_zeros_up_to_height_100` with `hγ` REPLACED by the
   two boxes' zero-freeness — every remaining hypothesis is a uniform Arb winding/edge input.

   conjecture1_proved = False — a finite Turing verification up to height 100, NOT a proof of RH. -/
import Mathlib
import DlvpZetaSymmetry
import ZetaZeroConfinement
import AllZeros_h100
import NoZerosInBox_0_1d1000_0_55d16
import NoZerosInBox_1d1000_999d1000_0_55d16

open Complex MeasureTheory Real
open scoped Topology

namespace StripClear

/-- The full open strip below height `55/16` is zero-free, given the two empty-band box
    certificates (their conclusions, not their Arb bundles): left sliver + band cover
    `Re ∈ (0, 999/1000]` directly, and the critical-line reflection `ρ ↦ 1 − conj ρ`
    (Im-preserving) carries `Re ∈ (999/1000, 1)` into the left sliver. -/
theorem hclear_low_of_box_certs
    (hleft : ∀ ρ : ℂ, (((0) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1 / 1000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) → riemannZeta ρ ≠ 0)
    (hband : ∀ ρ : ℂ, (((1 / 1000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999 / 1000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) → riemannZeta ρ ≠ 0) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      0 < ρ.im → ρ.im ≤ 55 / 16 → False := by
  intro ρ hz h0 h1 him0 himT
  by_cases hsm : ρ.re ≤ 1 / 1000
  · exact hleft ρ ⟨h0.le, hsm⟩ ⟨him0.le, himT⟩ hz
  · replace hsm : 1 / 1000 < ρ.re := not_le.mp hsm
    by_cases hmid : ρ.re ≤ 999 / 1000
    · exact hband ρ ⟨hsm.le, hmid⟩ ⟨him0.le, himT⟩ hz
    · replace hmid : 999 / 1000 < ρ.re := not_le.mp hmid
      -- right sliver `Re ∈ (999/1000, 1)`: reflect across the critical line into the left sliver.
      have hz' : riemannZeta (1 - (starRingEnd ℂ) ρ) = 0 :=
        ZeroFreeBridge.riemannZeta_reflect_line_eq_zero h0 h1 hz
      have hre' : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
      have him' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
      exact hleft (1 - (starRingEnd ℂ) ρ)
        ⟨by rw [hre']; linarith, by rw [hre']; linarith⟩
        ⟨by rw [him']; exact him0.le, by rw [him']; exact himT⟩ hz'

/-- The `55/16` height floor for nontrivial zeros up to any height `T`, from the two box
    certificates via `no_low_zeros_of_strip_clear`. This is exactly the shape of the `hγ`
    hypothesis of `all_nontrivial_zeros_up_to_height_100`. -/
theorem height_floor_of_box_certs (T : ℝ)
    (hleft : ∀ ρ : ℂ, (((0) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1 / 1000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) → riemannZeta ρ ≠ 0)
    (hband : ∀ ρ : ℂ, (((1 / 1000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999 / 1000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) → riemannZeta ρ ≠ 0) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → 55 / 16 ≤ |ρ.im| :=
  ZetaZeroConfinement.no_low_zeros_of_strip_clear T (hclear_low_of_box_certs hleft hband)

/-- **All nontrivial zeros up to height 100 on the line — no bare height-floor hypothesis.**
    Same conclusion as `AllZeros_h100.all_nontrivial_zeros_up_to_height_100`, with `hγ`
    REPLACED by the conclusions of the two winding-0 empty-band certificates. Every
    hypothesis is now a uniform Arb winding/edge input (big box + two empty bands);
    no classical fact is assumed bare. conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_100_strip_cleared
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
      (∀ z ∈ Metric.ball RHInBox_1d1000000_999999d1000000_0_100.cPB RHInBox_1d1000000_999999d1000000_0_100.RPB, riemannZeta z ≠ 0 →
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
        = 2 * π * I * (29 : ℂ)))
    (hleft : ∀ ρ : ℂ, (((0) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((1 / 1000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) → riemannZeta ρ ≠ 0)
    (hband : ∀ ρ : ℂ, (((1 / 1000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999 / 1000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((55 / 16))) → riemannZeta ρ ≠ 0) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100 → ρ.re = 1 / 2 :=
  AllZeros_h100.all_nontrivial_zeros_up_to_height_100 hLine hArb
    (height_floor_of_box_certs 100 hleft hband)

end StripClear

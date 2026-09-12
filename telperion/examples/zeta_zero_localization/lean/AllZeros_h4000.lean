/-  Height-chain step: all nontrivial zeta zeros up to height 4000 on Re = 1/2 --
    `AllZeros_h3000` + a `[3000, 4000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h3000
import RHInBoxT_1d4000000_3999999d4000000_3000_3040
import RHInBoxT_1d4000000_3999999d4000000_3040_3080
import RHInBoxT_1d4000000_3999999d4000000_3080_3120
import RHInBoxT_1d4000000_3999999d4000000_12479d4_3160
import RHInBoxT_1d4000000_3999999d4000000_3160_3200
import RHInBoxT_1d4000000_3999999d4000000_3200_3240
import RHInBoxT_1d4000000_3999999d4000000_3240_3280
import RHInBoxT_1d4000000_3999999d4000000_3280_3320
import RHInBoxT_1d4000000_3999999d4000000_3320_3360
import RHInBoxT_1d4000000_3999999d4000000_3360_3400
import RHInBoxT_1d4000000_3999999d4000000_3400_3440
import RHInBoxT_1d4000000_3999999d4000000_3440_3480
import RHInBoxT_1d4000000_3999999d4000000_3480_3520
import RHInBoxT_1d4000000_3999999d4000000_3520_14241d4
import RHInBoxT_1d4000000_3999999d4000000_3560_3600
import RHInBoxT_1d4000000_3999999d4000000_3600_3640
import RHInBoxT_1d4000000_3999999d4000000_3640_3680
import RHInBoxT_1d4000000_3999999d4000000_3680_3720
import RHInBoxT_1d4000000_3999999d4000000_3720_3760
import RHInBoxT_1d4000000_3999999d4000000_3760_3800
import RHInBoxT_1d4000000_3999999d4000000_3800_3840
import RHInBoxT_1d4000000_3999999d4000000_15359d4_3880
import RHInBoxT_1d4000000_3999999d4000000_3880_3920
import RHInBoxT_1d4000000_3999999d4000000_3920_15841d4
import RHInBoxT_1d4000000_3999999d4000000_3960_16001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h4000

/-- The 25-band NOMINAL partition of `[3000, 4000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 3000
  | 1 => 3040
  | 2 => 3080
  | 3 => 3120
  | 4 => 3160
  | 5 => 3200
  | 6 => 3240
  | 7 => 3280
  | 8 => 3320
  | 9 => 3360
  | 10 => 3400
  | 11 => 3440
  | 12 => 3480
  | 13 => 3520
  | 14 => 3560
  | 15 => 3600
  | 16 => 3640
  | 17 => 3680
  | 18 => 3720
  | 19 => 3760
  | 20 => 3800
  | 21 => 3840
  | 22 => 3880
  | 23 => 3920
  | 24 => 3960
  | 25 => 4000
  | _ => 4000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((3000:ℝ)) ≤ (3040); norm_num
  · show ((3040:ℝ)) ≤ (3080); norm_num
  · show ((3080:ℝ)) ≤ (3120); norm_num
  · show ((3120:ℝ)) ≤ (3160); norm_num
  · show ((3160:ℝ)) ≤ (3200); norm_num
  · show ((3200:ℝ)) ≤ (3240); norm_num
  · show ((3240:ℝ)) ≤ (3280); norm_num
  · show ((3280:ℝ)) ≤ (3320); norm_num
  · show ((3320:ℝ)) ≤ (3360); norm_num
  · show ((3360:ℝ)) ≤ (3400); norm_num
  · show ((3400:ℝ)) ≤ (3440); norm_num
  · show ((3440:ℝ)) ≤ (3480); norm_num
  · show ((3480:ℝ)) ≤ (3520); norm_num
  · show ((3520:ℝ)) ≤ (3560); norm_num
  · show ((3560:ℝ)) ≤ (3600); norm_num
  · show ((3600:ℝ)) ≤ (3640); norm_num
  · show ((3640:ℝ)) ≤ (3680); norm_num
  · show ((3680:ℝ)) ≤ (3720); norm_num
  · show ((3720:ℝ)) ≤ (3760); norm_num
  · show ((3760:ℝ)) ≤ (3800); norm_num
  · show ((3800:ℝ)) ≤ (3840); norm_num
  · show ((3840:ℝ)) ≤ (3880); norm_num
  · show ((3880:ℝ)) ≤ (3920); norm_num
  · show ((3920:ℝ)) ≤ (3960); norm_num
  · show ((3960:ℝ)) ≤ (4000); norm_num
  · show ((4000:ℝ)) ≤ (4000); norm_num
  · exact le_refl _

/-- The lower edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 3000
  | 1 => 3040
  | 2 => 3080
  | 3 => 12479 / 4
  | 4 => 3160
  | 5 => 3200
  | 6 => 3240
  | 7 => 3280
  | 8 => 3320
  | 9 => 3360
  | 10 => 3400
  | 11 => 3440
  | 12 => 3480
  | 13 => 3520
  | 14 => 3560
  | 15 => 3600
  | 16 => 3640
  | 17 => 3680
  | 18 => 3720
  | 19 => 3760
  | 20 => 3800
  | 21 => 15359 / 4
  | 22 => 3880
  | 23 => 3920
  | 24 => 3960
  | _ => 3960

/-- The upper edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 3040
  | 1 => 3080
  | 2 => 3120
  | 3 => 3160
  | 4 => 3200
  | 5 => 3240
  | 6 => 3280
  | 7 => 3320
  | 8 => 3360
  | 9 => 3400
  | 10 => 3440
  | 11 => 3480
  | 12 => 3520
  | 13 => 14241 / 4
  | 14 => 3600
  | 15 => 3640
  | 16 => 3680
  | 17 => 3720
  | 18 => 3760
  | 19 => 3800
  | 20 => 3840
  | 21 => 3880
  | 22 => 3920
  | 23 => 15841 / 4
  | 24 => 16001 / 4
  | _ => 16001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 25 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 4000` (`log 4000 ≤ 9`, `2.7^9 ≥ 4000`). -/
theorem haC_4000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 4000 := by
  have hlog : Real.log 4000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h9 : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 := pow_le_pow_left₀ (by norm_num) he1 9
    rw [h9]; nlinarith [hpow]
  have hpos : 0 < Real.log 4000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 4000
      ≤ (1 / 4000000) * 9 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[3000, 4000]` segment's band hypothesis: every band `i < 25` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 25 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 25 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[3000, 4000]` SEGMENT: every zero with `3000 ≤ Im ≤ 4000` is on the line. -/
theorem segment_3000_4000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (3000:ℝ) ≤ ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 3000 4000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_4000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 4000 via the HEIGHT CHAIN**: `[0,3000]` ∘ `[3000,4000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_4000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2 := by
  have hγ3000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 3000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 3000 4000
    (AllZeros_h3000.all_nontrivial_zeros_up_to_height_3000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hγ3000)
    (segment_3000_4000 hbands hγ)

end AllZeros_h4000

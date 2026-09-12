/-  Height-chain step: all nontrivial zeta zeros up to height 14000 on Re = 1/2 --
    `AllZeros_h13000` + a `[13000, 14000]` SEGMENT certificate (29 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h13000
import RHInBoxT_1d4000000_3999999d4000000_13000_13034
import RHInBoxT_1d4000000_3999999d4000000_13034_13069
import RHInBoxT_1d4000000_3999999d4000000_13069_13103
import RHInBoxT_1d4000000_3999999d4000000_13103_13138
import RHInBoxT_1d4000000_3999999d4000000_13138_13172
import RHInBoxT_1d4000000_3999999d4000000_13172_13207
import RHInBoxT_1d4000000_3999999d4000000_13207_13241
import RHInBoxT_1d4000000_3999999d4000000_13241_13276
import RHInBoxT_1d4000000_3999999d4000000_26551d2_13310
import RHInBoxT_1d4000000_3999999d4000000_13310_13345
import RHInBoxT_1d4000000_3999999d4000000_13345_13379
import RHInBoxT_1d4000000_3999999d4000000_13379_13414
import RHInBoxT_1d4000000_3999999d4000000_13414_13448
import RHInBoxT_1d4000000_3999999d4000000_13448_13483
import RHInBoxT_1d4000000_3999999d4000000_13483_13517
import RHInBoxT_1d4000000_3999999d4000000_13517_13552
import RHInBoxT_1d4000000_3999999d4000000_13552_13586
import RHInBoxT_1d4000000_3999999d4000000_13586_13621
import RHInBoxT_1d4000000_3999999d4000000_13621_13655
import RHInBoxT_1d4000000_3999999d4000000_13655_13690
import RHInBoxT_1d4000000_3999999d4000000_13690_13724
import RHInBoxT_1d4000000_3999999d4000000_13724_13759
import RHInBoxT_1d4000000_3999999d4000000_13759_13793
import RHInBoxT_1d4000000_3999999d4000000_13793_13828
import RHInBoxT_1d4000000_3999999d4000000_13828_13862
import RHInBoxT_1d4000000_3999999d4000000_13862_13897
import RHInBoxT_1d4000000_3999999d4000000_13897_55725d4
import RHInBoxT_1d4000000_3999999d4000000_13931_13966
import RHInBoxT_1d4000000_3999999d4000000_13966_14000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h14000

/-- The 29-band NOMINAL partition of `[13000, 14000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 13000
  | 1 => 13034
  | 2 => 13069
  | 3 => 13103
  | 4 => 13138
  | 5 => 13172
  | 6 => 13207
  | 7 => 13241
  | 8 => 13276
  | 9 => 13310
  | 10 => 13345
  | 11 => 13379
  | 12 => 13414
  | 13 => 13448
  | 14 => 13483
  | 15 => 13517
  | 16 => 13552
  | 17 => 13586
  | 18 => 13621
  | 19 => 13655
  | 20 => 13690
  | 21 => 13724
  | 22 => 13759
  | 23 => 13793
  | 24 => 13828
  | 25 => 13862
  | 26 => 13897
  | 27 => 13931
  | 28 => 13966
  | 29 => 14000
  | _ => 14000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((13000:ℝ)) ≤ (13034); norm_num
  · show ((13034:ℝ)) ≤ (13069); norm_num
  · show ((13069:ℝ)) ≤ (13103); norm_num
  · show ((13103:ℝ)) ≤ (13138); norm_num
  · show ((13138:ℝ)) ≤ (13172); norm_num
  · show ((13172:ℝ)) ≤ (13207); norm_num
  · show ((13207:ℝ)) ≤ (13241); norm_num
  · show ((13241:ℝ)) ≤ (13276); norm_num
  · show ((13276:ℝ)) ≤ (13310); norm_num
  · show ((13310:ℝ)) ≤ (13345); norm_num
  · show ((13345:ℝ)) ≤ (13379); norm_num
  · show ((13379:ℝ)) ≤ (13414); norm_num
  · show ((13414:ℝ)) ≤ (13448); norm_num
  · show ((13448:ℝ)) ≤ (13483); norm_num
  · show ((13483:ℝ)) ≤ (13517); norm_num
  · show ((13517:ℝ)) ≤ (13552); norm_num
  · show ((13552:ℝ)) ≤ (13586); norm_num
  · show ((13586:ℝ)) ≤ (13621); norm_num
  · show ((13621:ℝ)) ≤ (13655); norm_num
  · show ((13655:ℝ)) ≤ (13690); norm_num
  · show ((13690:ℝ)) ≤ (13724); norm_num
  · show ((13724:ℝ)) ≤ (13759); norm_num
  · show ((13759:ℝ)) ≤ (13793); norm_num
  · show ((13793:ℝ)) ≤ (13828); norm_num
  · show ((13828:ℝ)) ≤ (13862); norm_num
  · show ((13862:ℝ)) ≤ (13897); norm_num
  · show ((13897:ℝ)) ≤ (13931); norm_num
  · show ((13931:ℝ)) ≤ (13966); norm_num
  · show ((13966:ℝ)) ≤ (14000); norm_num
  · show ((14000:ℝ)) ≤ (14000); norm_num
  · exact le_refl _

/-- The lower edges of the 29 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 13000
  | 1 => 13034
  | 2 => 13069
  | 3 => 13103
  | 4 => 13138
  | 5 => 13172
  | 6 => 13207
  | 7 => 13241
  | 8 => 26551 / 2
  | 9 => 13310
  | 10 => 13345
  | 11 => 13379
  | 12 => 13414
  | 13 => 13448
  | 14 => 13483
  | 15 => 13517
  | 16 => 13552
  | 17 => 13586
  | 18 => 13621
  | 19 => 13655
  | 20 => 13690
  | 21 => 13724
  | 22 => 13759
  | 23 => 13793
  | 24 => 13828
  | 25 => 13862
  | 26 => 13897
  | 27 => 13931
  | 28 => 13966
  | _ => 13966

/-- The upper edges of the 29 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 13034
  | 1 => 13069
  | 2 => 13103
  | 3 => 13138
  | 4 => 13172
  | 5 => 13207
  | 6 => 13241
  | 7 => 13276
  | 8 => 13310
  | 9 => 13345
  | 10 => 13379
  | 11 => 13414
  | 12 => 13448
  | 13 => 13483
  | 14 => 13517
  | 15 => 13552
  | 16 => 13586
  | 17 => 13621
  | 18 => 13655
  | 19 => 13690
  | 20 => 13724
  | 21 => 13759
  | 22 => 13793
  | 23 => 13828
  | 24 => 13862
  | 25 => 13897
  | 26 => 55725 / 4
  | 27 => 13966
  | 28 => 14000
  | _ => 14000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 29 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 14000` (`log 14000 ≤ 10`, `2.7^10 ≥ 14000`). -/
theorem haC_14000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 14000 := by
  have hlog : Real.log 14000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 14000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 14000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[13000, 14000]` segment's band hypothesis: every band `i < 29` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 29 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 29 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[13000, 14000]` SEGMENT: every zero with `13000 ≤ Im ≤ 14000` is on the line. -/
theorem segment_13000_14000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 14000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (13000:ℝ) ≤ ρ.im → ρ.im ≤ 14000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 13000 14000 bndSeg 29 (by norm_num) bndSeg_mono rfl rfl haC_14000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 14000 via the HEIGHT CHAIN**: `[0,13000]` ∘ `[13000,14000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_14000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands_6000 : AllZeros_h6000.BandHyp)
    (hbands_7000 : AllZeros_h7000.BandHyp)
    (hbands_8000 : AllZeros_h8000.BandHyp)
    (hbands_9000 : AllZeros_h9000.BandHyp)
    (hbands_10000 : AllZeros_h10000.BandHyp)
    (hbands_11000 : AllZeros_h11000.BandHyp)
    (hbands_12000 : AllZeros_h12000.BandHyp)
    (hbands_13000 : AllZeros_h13000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 14000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 14000 → ρ.re = 1 / 2 := by
  have hγ13000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 13000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 13000 14000
    (AllZeros_h13000.all_nontrivial_zeros_up_to_height_13000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hbands_6000
      hbands_7000
      hbands_8000
      hbands_9000
      hbands_10000
      hbands_11000
      hbands_12000
      hbands_13000
      hγ13000)
    (segment_13000_14000 hbands hγ)

end AllZeros_h14000

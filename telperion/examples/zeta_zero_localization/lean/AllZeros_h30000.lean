/-  Height-chain step: all nontrivial zeta zeros up to height 30000 on Re = 1/2 --
    `AllZeros_h29000` + a `[29000, 30000]` SEGMENT certificate (32 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h29000
import RHInBoxT_1d4000000_3999999d4000000_29000_29031
import RHInBoxT_1d4000000_3999999d4000000_29031_29062
import RHInBoxT_1d4000000_3999999d4000000_29062_29094
import RHInBoxT_1d4000000_3999999d4000000_29094_29125
import RHInBoxT_1d4000000_3999999d4000000_29125_29156
import RHInBoxT_1d4000000_3999999d4000000_29156_29188
import RHInBoxT_1d4000000_3999999d4000000_29188_29219
import RHInBoxT_1d4000000_3999999d4000000_29219_29250
import RHInBoxT_1d4000000_3999999d4000000_29250_29281
import RHInBoxT_1d4000000_3999999d4000000_29281_29312
import RHInBoxT_1d4000000_3999999d4000000_29312_117377d4
import RHInBoxT_1d4000000_3999999d4000000_29344_29375
import RHInBoxT_1d4000000_3999999d4000000_29375_29406
import RHInBoxT_1d4000000_3999999d4000000_29406_29438
import RHInBoxT_1d4000000_3999999d4000000_29438_29469
import RHInBoxT_1d4000000_3999999d4000000_29469_29500
import RHInBoxT_1d4000000_3999999d4000000_29500_29531
import RHInBoxT_1d4000000_3999999d4000000_29531_29562
import RHInBoxT_1d4000000_3999999d4000000_29562_29594
import RHInBoxT_1d4000000_3999999d4000000_29594_118501d4
import RHInBoxT_1d4000000_3999999d4000000_29625_29656
import RHInBoxT_1d4000000_3999999d4000000_29656_29688
import RHInBoxT_1d4000000_3999999d4000000_29688_29719
import RHInBoxT_1d4000000_3999999d4000000_29719_29750
import RHInBoxT_1d4000000_3999999d4000000_29750_29781
import RHInBoxT_1d4000000_3999999d4000000_29781_29812
import RHInBoxT_1d4000000_3999999d4000000_29812_29844
import RHInBoxT_1d4000000_3999999d4000000_29844_119501d4
import RHInBoxT_1d4000000_3999999d4000000_29875_29906
import RHInBoxT_1d4000000_3999999d4000000_29906_119753d4
import RHInBoxT_1d4000000_3999999d4000000_29938_29969
import RHInBoxT_1d4000000_3999999d4000000_29969_30000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h30000

/-- The 32-band NOMINAL partition of `[29000, 30000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 29000
  | 1 => 29031
  | 2 => 29062
  | 3 => 29094
  | 4 => 29125
  | 5 => 29156
  | 6 => 29188
  | 7 => 29219
  | 8 => 29250
  | 9 => 29281
  | 10 => 29312
  | 11 => 29344
  | 12 => 29375
  | 13 => 29406
  | 14 => 29438
  | 15 => 29469
  | 16 => 29500
  | 17 => 29531
  | 18 => 29562
  | 19 => 29594
  | 20 => 29625
  | 21 => 29656
  | 22 => 29688
  | 23 => 29719
  | 24 => 29750
  | 25 => 29781
  | 26 => 29812
  | 27 => 29844
  | 28 => 29875
  | 29 => 29906
  | 30 => 29938
  | 31 => 29969
  | 32 => 30000
  | _ => 30000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((29000:ℝ)) ≤ (29031); norm_num
  · show ((29031:ℝ)) ≤ (29062); norm_num
  · show ((29062:ℝ)) ≤ (29094); norm_num
  · show ((29094:ℝ)) ≤ (29125); norm_num
  · show ((29125:ℝ)) ≤ (29156); norm_num
  · show ((29156:ℝ)) ≤ (29188); norm_num
  · show ((29188:ℝ)) ≤ (29219); norm_num
  · show ((29219:ℝ)) ≤ (29250); norm_num
  · show ((29250:ℝ)) ≤ (29281); norm_num
  · show ((29281:ℝ)) ≤ (29312); norm_num
  · show ((29312:ℝ)) ≤ (29344); norm_num
  · show ((29344:ℝ)) ≤ (29375); norm_num
  · show ((29375:ℝ)) ≤ (29406); norm_num
  · show ((29406:ℝ)) ≤ (29438); norm_num
  · show ((29438:ℝ)) ≤ (29469); norm_num
  · show ((29469:ℝ)) ≤ (29500); norm_num
  · show ((29500:ℝ)) ≤ (29531); norm_num
  · show ((29531:ℝ)) ≤ (29562); norm_num
  · show ((29562:ℝ)) ≤ (29594); norm_num
  · show ((29594:ℝ)) ≤ (29625); norm_num
  · show ((29625:ℝ)) ≤ (29656); norm_num
  · show ((29656:ℝ)) ≤ (29688); norm_num
  · show ((29688:ℝ)) ≤ (29719); norm_num
  · show ((29719:ℝ)) ≤ (29750); norm_num
  · show ((29750:ℝ)) ≤ (29781); norm_num
  · show ((29781:ℝ)) ≤ (29812); norm_num
  · show ((29812:ℝ)) ≤ (29844); norm_num
  · show ((29844:ℝ)) ≤ (29875); norm_num
  · show ((29875:ℝ)) ≤ (29906); norm_num
  · show ((29906:ℝ)) ≤ (29938); norm_num
  · show ((29938:ℝ)) ≤ (29969); norm_num
  · show ((29969:ℝ)) ≤ (30000); norm_num
  · show ((30000:ℝ)) ≤ (30000); norm_num
  · exact le_refl _

/-- The lower edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 29000
  | 1 => 29031
  | 2 => 29062
  | 3 => 29094
  | 4 => 29125
  | 5 => 29156
  | 6 => 29188
  | 7 => 29219
  | 8 => 29250
  | 9 => 29281
  | 10 => 29312
  | 11 => 29344
  | 12 => 29375
  | 13 => 29406
  | 14 => 29438
  | 15 => 29469
  | 16 => 29500
  | 17 => 29531
  | 18 => 29562
  | 19 => 29594
  | 20 => 29625
  | 21 => 29656
  | 22 => 29688
  | 23 => 29719
  | 24 => 29750
  | 25 => 29781
  | 26 => 29812
  | 27 => 29844
  | 28 => 29875
  | 29 => 29906
  | 30 => 29938
  | 31 => 29969
  | _ => 29969

/-- The upper edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 29031
  | 1 => 29062
  | 2 => 29094
  | 3 => 29125
  | 4 => 29156
  | 5 => 29188
  | 6 => 29219
  | 7 => 29250
  | 8 => 29281
  | 9 => 29312
  | 10 => 117377 / 4
  | 11 => 29375
  | 12 => 29406
  | 13 => 29438
  | 14 => 29469
  | 15 => 29500
  | 16 => 29531
  | 17 => 29562
  | 18 => 29594
  | 19 => 118501 / 4
  | 20 => 29656
  | 21 => 29688
  | 22 => 29719
  | 23 => 29750
  | 24 => 29781
  | 25 => 29812
  | 26 => 29844
  | 27 => 119501 / 4
  | 28 => 29906
  | 29 => 119753 / 4
  | 30 => 29969
  | 31 => 30000
  | _ => 30000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 32 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 30000` (`log 30000 ≤ 11`, `2.7^11 ≥ 30000`). -/
theorem haC_30000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 30000 := by
  have hlog : Real.log 30000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 30000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 30000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[29000, 30000]` segment's band hypothesis: every band `i < 32` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 32 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 32 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[29000, 30000]` SEGMENT: every zero with `29000 ≤ Im ≤ 30000` is on the line. -/
theorem segment_29000_30000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 30000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (29000:ℝ) ≤ ρ.im → ρ.im ≤ 30000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 29000 30000 bndSeg 32 (by norm_num) bndSeg_mono rfl rfl haC_30000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 30000 via the HEIGHT CHAIN**: `[0,29000]` ∘ `[29000,30000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_30000_of_bands
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
    (hbands_14000 : AllZeros_h14000.BandHyp)
    (hbands_15000 : AllZeros_h15000.BandHyp)
    (hbands_16000 : AllZeros_h16000.BandHyp)
    (hbands_17000 : AllZeros_h17000.BandHyp)
    (hbands_18000 : AllZeros_h18000.BandHyp)
    (hbands_19000 : AllZeros_h19000.BandHyp)
    (hbands_20000 : AllZeros_h20000.BandHyp)
    (hbands_21000 : AllZeros_h21000.BandHyp)
    (hbands_22000 : AllZeros_h22000.BandHyp)
    (hbands_23000 : AllZeros_h23000.BandHyp)
    (hbands_24000 : AllZeros_h24000.BandHyp)
    (hbands_25000 : AllZeros_h25000.BandHyp)
    (hbands_26000 : AllZeros_h26000.BandHyp)
    (hbands_27000 : AllZeros_h27000.BandHyp)
    (hbands_28000 : AllZeros_h28000.BandHyp)
    (hbands_29000 : AllZeros_h29000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 30000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 30000 → ρ.re = 1 / 2 := by
  have hγ29000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 29000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 29000 30000
    (AllZeros_h29000.all_nontrivial_zeros_up_to_height_29000_of_bands
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
      hbands_14000
      hbands_15000
      hbands_16000
      hbands_17000
      hbands_18000
      hbands_19000
      hbands_20000
      hbands_21000
      hbands_22000
      hbands_23000
      hbands_24000
      hbands_25000
      hbands_26000
      hbands_27000
      hbands_28000
      hbands_29000
      hγ29000)
    (segment_29000_30000 hbands hγ)

end AllZeros_h30000

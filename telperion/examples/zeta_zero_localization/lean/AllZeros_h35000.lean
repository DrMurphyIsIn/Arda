/-  Height-chain step: all nontrivial zeta zeros up to height 35000 on Re = 1/2 --
    `AllZeros_h34000` + a `[34000, 35000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h34000
import RHInBoxT_1d4000000_3999999d4000000_135999d4_34030
import RHInBoxT_1d4000000_3999999d4000000_34030_34061
import RHInBoxT_1d4000000_3999999d4000000_34061_34091
import RHInBoxT_1d4000000_3999999d4000000_34091_34121
import RHInBoxT_1d4000000_3999999d4000000_34121_34152
import RHInBoxT_1d4000000_3999999d4000000_34152_34182
import RHInBoxT_1d4000000_3999999d4000000_34182_34212
import RHInBoxT_1d4000000_3999999d4000000_34212_34242
import RHInBoxT_1d4000000_3999999d4000000_34242_34273
import RHInBoxT_1d4000000_3999999d4000000_34273_34303
import RHInBoxT_1d4000000_3999999d4000000_34303_34333
import RHInBoxT_1d4000000_3999999d4000000_34333_137457d4
import RHInBoxT_1d4000000_3999999d4000000_34364_34394
import RHInBoxT_1d4000000_3999999d4000000_34394_34424
import RHInBoxT_1d4000000_3999999d4000000_34424_34455
import RHInBoxT_1d4000000_3999999d4000000_34455_34485
import RHInBoxT_1d4000000_3999999d4000000_34485_34515
import RHInBoxT_1d4000000_3999999d4000000_138059d4_34545
import RHInBoxT_1d4000000_3999999d4000000_34545_34576
import RHInBoxT_1d4000000_3999999d4000000_34576_138425d4
import RHInBoxT_1d4000000_3999999d4000000_34606_34636
import RHInBoxT_1d4000000_3999999d4000000_34636_34667
import RHInBoxT_1d4000000_3999999d4000000_34667_138789d4
import RHInBoxT_1d4000000_3999999d4000000_34697_34727
import RHInBoxT_1d4000000_3999999d4000000_34727_34758
import RHInBoxT_1d4000000_3999999d4000000_34758_34788
import RHInBoxT_1d4000000_3999999d4000000_34788_34818
import RHInBoxT_1d4000000_3999999d4000000_34818_34848
import RHInBoxT_1d4000000_3999999d4000000_34848_34879
import RHInBoxT_1d4000000_3999999d4000000_34879_34909
import RHInBoxT_1d4000000_3999999d4000000_34909_34939
import RHInBoxT_1d4000000_3999999d4000000_34939_69941d2
import RHInBoxT_1d4000000_3999999d4000000_34970_35000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h35000

/-- The 33-band NOMINAL partition of `[34000, 35000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 34000
  | 1 => 34030
  | 2 => 34061
  | 3 => 34091
  | 4 => 34121
  | 5 => 34152
  | 6 => 34182
  | 7 => 34212
  | 8 => 34242
  | 9 => 34273
  | 10 => 34303
  | 11 => 34333
  | 12 => 34364
  | 13 => 34394
  | 14 => 34424
  | 15 => 34455
  | 16 => 34485
  | 17 => 34515
  | 18 => 34545
  | 19 => 34576
  | 20 => 34606
  | 21 => 34636
  | 22 => 34667
  | 23 => 34697
  | 24 => 34727
  | 25 => 34758
  | 26 => 34788
  | 27 => 34818
  | 28 => 34848
  | 29 => 34879
  | 30 => 34909
  | 31 => 34939
  | 32 => 34970
  | 33 => 35000
  | _ => 35000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((34000:ℝ)) ≤ (34030); norm_num
  · show ((34030:ℝ)) ≤ (34061); norm_num
  · show ((34061:ℝ)) ≤ (34091); norm_num
  · show ((34091:ℝ)) ≤ (34121); norm_num
  · show ((34121:ℝ)) ≤ (34152); norm_num
  · show ((34152:ℝ)) ≤ (34182); norm_num
  · show ((34182:ℝ)) ≤ (34212); norm_num
  · show ((34212:ℝ)) ≤ (34242); norm_num
  · show ((34242:ℝ)) ≤ (34273); norm_num
  · show ((34273:ℝ)) ≤ (34303); norm_num
  · show ((34303:ℝ)) ≤ (34333); norm_num
  · show ((34333:ℝ)) ≤ (34364); norm_num
  · show ((34364:ℝ)) ≤ (34394); norm_num
  · show ((34394:ℝ)) ≤ (34424); norm_num
  · show ((34424:ℝ)) ≤ (34455); norm_num
  · show ((34455:ℝ)) ≤ (34485); norm_num
  · show ((34485:ℝ)) ≤ (34515); norm_num
  · show ((34515:ℝ)) ≤ (34545); norm_num
  · show ((34545:ℝ)) ≤ (34576); norm_num
  · show ((34576:ℝ)) ≤ (34606); norm_num
  · show ((34606:ℝ)) ≤ (34636); norm_num
  · show ((34636:ℝ)) ≤ (34667); norm_num
  · show ((34667:ℝ)) ≤ (34697); norm_num
  · show ((34697:ℝ)) ≤ (34727); norm_num
  · show ((34727:ℝ)) ≤ (34758); norm_num
  · show ((34758:ℝ)) ≤ (34788); norm_num
  · show ((34788:ℝ)) ≤ (34818); norm_num
  · show ((34818:ℝ)) ≤ (34848); norm_num
  · show ((34848:ℝ)) ≤ (34879); norm_num
  · show ((34879:ℝ)) ≤ (34909); norm_num
  · show ((34909:ℝ)) ≤ (34939); norm_num
  · show ((34939:ℝ)) ≤ (34970); norm_num
  · show ((34970:ℝ)) ≤ (35000); norm_num
  · show ((35000:ℝ)) ≤ (35000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 135999 / 4
  | 1 => 34030
  | 2 => 34061
  | 3 => 34091
  | 4 => 34121
  | 5 => 34152
  | 6 => 34182
  | 7 => 34212
  | 8 => 34242
  | 9 => 34273
  | 10 => 34303
  | 11 => 34333
  | 12 => 34364
  | 13 => 34394
  | 14 => 34424
  | 15 => 34455
  | 16 => 34485
  | 17 => 138059 / 4
  | 18 => 34545
  | 19 => 34576
  | 20 => 34606
  | 21 => 34636
  | 22 => 34667
  | 23 => 34697
  | 24 => 34727
  | 25 => 34758
  | 26 => 34788
  | 27 => 34818
  | 28 => 34848
  | 29 => 34879
  | 30 => 34909
  | 31 => 34939
  | 32 => 34970
  | _ => 34970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 34030
  | 1 => 34061
  | 2 => 34091
  | 3 => 34121
  | 4 => 34152
  | 5 => 34182
  | 6 => 34212
  | 7 => 34242
  | 8 => 34273
  | 9 => 34303
  | 10 => 34333
  | 11 => 137457 / 4
  | 12 => 34394
  | 13 => 34424
  | 14 => 34455
  | 15 => 34485
  | 16 => 34515
  | 17 => 34545
  | 18 => 34576
  | 19 => 138425 / 4
  | 20 => 34636
  | 21 => 34667
  | 22 => 138789 / 4
  | 23 => 34727
  | 24 => 34758
  | 25 => 34788
  | 26 => 34818
  | 27 => 34848
  | 28 => 34879
  | 29 => 34909
  | 30 => 34939
  | 31 => 69941 / 2
  | 32 => 35000
  | _ => 35000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 35000` (`log 35000 ≤ 11`, `2.7^11 ≥ 35000`). -/
theorem haC_35000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 35000 := by
  have hlog : Real.log 35000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 35000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 35000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[34000, 35000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[34000, 35000]` SEGMENT: every zero with `34000 ≤ Im ≤ 35000` is on the line. -/
theorem segment_34000_35000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 35000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (34000:ℝ) ≤ ρ.im → ρ.im ≤ 35000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 34000 35000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_35000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 35000 via the HEIGHT CHAIN**: `[0,34000]` ∘ `[34000,35000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_35000_of_bands
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
    (hbands_30000 : AllZeros_h30000.BandHyp)
    (hbands_31000 : AllZeros_h31000.BandHyp)
    (hbands_32000 : AllZeros_h32000.BandHyp)
    (hbands_33000 : AllZeros_h33000.BandHyp)
    (hbands_34000 : AllZeros_h34000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 35000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 35000 → ρ.re = 1 / 2 := by
  have hγ34000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 34000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 34000 35000
    (AllZeros_h34000.all_nontrivial_zeros_up_to_height_34000_of_bands
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
      hbands_30000
      hbands_31000
      hbands_32000
      hbands_33000
      hbands_34000
      hγ34000)
    (segment_34000_35000 hbands hγ)

end AllZeros_h35000

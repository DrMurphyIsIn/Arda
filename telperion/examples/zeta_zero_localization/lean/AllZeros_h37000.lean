/-  Height-chain step: all nontrivial zeta zeros up to height 37000 on Re = 1/2 --
    `AllZeros_h36000` + a `[36000, 37000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h36000
import RHInBoxT_1d4000000_3999999d4000000_36000_36030
import RHInBoxT_1d4000000_3999999d4000000_36030_36061
import RHInBoxT_1d4000000_3999999d4000000_36061_36091
import RHInBoxT_1d4000000_3999999d4000000_36091_144485d4
import RHInBoxT_1d4000000_3999999d4000000_36121_36152
import RHInBoxT_1d4000000_3999999d4000000_36152_36182
import RHInBoxT_1d4000000_3999999d4000000_144727d4_144849d4
import RHInBoxT_1d4000000_3999999d4000000_36212_36242
import RHInBoxT_1d4000000_3999999d4000000_36242_145093d4
import RHInBoxT_1d4000000_3999999d4000000_36273_145213d4
import RHInBoxT_1d4000000_3999999d4000000_36303_36333
import RHInBoxT_1d4000000_3999999d4000000_36333_36364
import RHInBoxT_1d4000000_3999999d4000000_36364_36394
import RHInBoxT_1d4000000_3999999d4000000_145575d4_36424
import RHInBoxT_1d4000000_3999999d4000000_36424_36455
import RHInBoxT_1d4000000_3999999d4000000_36455_36485
import RHInBoxT_1d4000000_3999999d4000000_36485_36515
import RHInBoxT_1d4000000_3999999d4000000_36515_36545
import RHInBoxT_1d4000000_3999999d4000000_36545_36576
import RHInBoxT_1d4000000_3999999d4000000_36576_36606
import RHInBoxT_1d4000000_3999999d4000000_36606_36636
import RHInBoxT_1d4000000_3999999d4000000_36636_36667
import RHInBoxT_1d4000000_3999999d4000000_36667_36697
import RHInBoxT_1d4000000_3999999d4000000_146787d4_146909d4
import RHInBoxT_1d4000000_3999999d4000000_36727_36758
import RHInBoxT_1d4000000_3999999d4000000_36758_36788
import RHInBoxT_1d4000000_3999999d4000000_36788_36818
import RHInBoxT_1d4000000_3999999d4000000_36818_36848
import RHInBoxT_1d4000000_3999999d4000000_147391d4_36879
import RHInBoxT_1d4000000_3999999d4000000_147515d4_36909
import RHInBoxT_1d4000000_3999999d4000000_36909_36939
import RHInBoxT_1d4000000_3999999d4000000_36939_147881d4
import RHInBoxT_1d4000000_3999999d4000000_36970_37000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h37000

/-- The 33-band NOMINAL partition of `[36000, 37000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 36000
  | 1 => 36030
  | 2 => 36061
  | 3 => 36091
  | 4 => 36121
  | 5 => 36152
  | 6 => 36182
  | 7 => 36212
  | 8 => 36242
  | 9 => 36273
  | 10 => 36303
  | 11 => 36333
  | 12 => 36364
  | 13 => 36394
  | 14 => 36424
  | 15 => 36455
  | 16 => 36485
  | 17 => 36515
  | 18 => 36545
  | 19 => 36576
  | 20 => 36606
  | 21 => 36636
  | 22 => 36667
  | 23 => 36697
  | 24 => 36727
  | 25 => 36758
  | 26 => 36788
  | 27 => 36818
  | 28 => 36848
  | 29 => 36879
  | 30 => 36909
  | 31 => 36939
  | 32 => 36970
  | 33 => 37000
  | _ => 37000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((36000:ℝ)) ≤ (36030); norm_num
  · show ((36030:ℝ)) ≤ (36061); norm_num
  · show ((36061:ℝ)) ≤ (36091); norm_num
  · show ((36091:ℝ)) ≤ (36121); norm_num
  · show ((36121:ℝ)) ≤ (36152); norm_num
  · show ((36152:ℝ)) ≤ (36182); norm_num
  · show ((36182:ℝ)) ≤ (36212); norm_num
  · show ((36212:ℝ)) ≤ (36242); norm_num
  · show ((36242:ℝ)) ≤ (36273); norm_num
  · show ((36273:ℝ)) ≤ (36303); norm_num
  · show ((36303:ℝ)) ≤ (36333); norm_num
  · show ((36333:ℝ)) ≤ (36364); norm_num
  · show ((36364:ℝ)) ≤ (36394); norm_num
  · show ((36394:ℝ)) ≤ (36424); norm_num
  · show ((36424:ℝ)) ≤ (36455); norm_num
  · show ((36455:ℝ)) ≤ (36485); norm_num
  · show ((36485:ℝ)) ≤ (36515); norm_num
  · show ((36515:ℝ)) ≤ (36545); norm_num
  · show ((36545:ℝ)) ≤ (36576); norm_num
  · show ((36576:ℝ)) ≤ (36606); norm_num
  · show ((36606:ℝ)) ≤ (36636); norm_num
  · show ((36636:ℝ)) ≤ (36667); norm_num
  · show ((36667:ℝ)) ≤ (36697); norm_num
  · show ((36697:ℝ)) ≤ (36727); norm_num
  · show ((36727:ℝ)) ≤ (36758); norm_num
  · show ((36758:ℝ)) ≤ (36788); norm_num
  · show ((36788:ℝ)) ≤ (36818); norm_num
  · show ((36818:ℝ)) ≤ (36848); norm_num
  · show ((36848:ℝ)) ≤ (36879); norm_num
  · show ((36879:ℝ)) ≤ (36909); norm_num
  · show ((36909:ℝ)) ≤ (36939); norm_num
  · show ((36939:ℝ)) ≤ (36970); norm_num
  · show ((36970:ℝ)) ≤ (37000); norm_num
  · show ((37000:ℝ)) ≤ (37000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 36000
  | 1 => 36030
  | 2 => 36061
  | 3 => 36091
  | 4 => 36121
  | 5 => 36152
  | 6 => 144727 / 4
  | 7 => 36212
  | 8 => 36242
  | 9 => 36273
  | 10 => 36303
  | 11 => 36333
  | 12 => 36364
  | 13 => 145575 / 4
  | 14 => 36424
  | 15 => 36455
  | 16 => 36485
  | 17 => 36515
  | 18 => 36545
  | 19 => 36576
  | 20 => 36606
  | 21 => 36636
  | 22 => 36667
  | 23 => 146787 / 4
  | 24 => 36727
  | 25 => 36758
  | 26 => 36788
  | 27 => 36818
  | 28 => 147391 / 4
  | 29 => 147515 / 4
  | 30 => 36909
  | 31 => 36939
  | 32 => 36970
  | _ => 36970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 36030
  | 1 => 36061
  | 2 => 36091
  | 3 => 144485 / 4
  | 4 => 36152
  | 5 => 36182
  | 6 => 144849 / 4
  | 7 => 36242
  | 8 => 145093 / 4
  | 9 => 145213 / 4
  | 10 => 36333
  | 11 => 36364
  | 12 => 36394
  | 13 => 36424
  | 14 => 36455
  | 15 => 36485
  | 16 => 36515
  | 17 => 36545
  | 18 => 36576
  | 19 => 36606
  | 20 => 36636
  | 21 => 36667
  | 22 => 36697
  | 23 => 146909 / 4
  | 24 => 36758
  | 25 => 36788
  | 26 => 36818
  | 27 => 36848
  | 28 => 36879
  | 29 => 36909
  | 30 => 36939
  | 31 => 147881 / 4
  | 32 => 37000
  | _ => 37000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 37000` (`log 37000 ≤ 11`, `2.7^11 ≥ 37000`). -/
theorem haC_37000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 37000 := by
  have hlog : Real.log 37000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 37000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 37000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[36000, 37000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[36000, 37000]` SEGMENT: every zero with `36000 ≤ Im ≤ 37000` is on the line. -/
theorem segment_36000_37000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 37000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (36000:ℝ) ≤ ρ.im → ρ.im ≤ 37000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 36000 37000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_37000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 37000 via the HEIGHT CHAIN**: `[0,36000]` ∘ `[36000,37000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_37000_of_bands
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
    (hbands_35000 : AllZeros_h35000.BandHyp)
    (hbands_36000 : AllZeros_h36000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 37000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 37000 → ρ.re = 1 / 2 := by
  have hγ36000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 36000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 36000 37000
    (AllZeros_h36000.all_nontrivial_zeros_up_to_height_36000_of_bands
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
      hbands_35000
      hbands_36000
      hγ36000)
    (segment_36000_37000 hbands hγ)

end AllZeros_h37000

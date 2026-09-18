/-  Height-chain step: all nontrivial zeta zeros up to height 159000 on Re = 1/2 --
    `AllZeros_h158000` + a `[158000, 159000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h158000
import RHInBoxT_1d4000000_3999999d4000000_158000_158026
import RHInBoxT_1d4000000_3999999d4000000_158026_158051
import RHInBoxT_1d4000000_3999999d4000000_158051_158077
import RHInBoxT_1d4000000_3999999d4000000_158077_158103
import RHInBoxT_1d4000000_3999999d4000000_158103_158128
import RHInBoxT_1d4000000_3999999d4000000_632511d4_158154
import RHInBoxT_1d4000000_3999999d4000000_158154_158179
import RHInBoxT_1d4000000_3999999d4000000_158179_158205
import RHInBoxT_1d4000000_3999999d4000000_158205_158231
import RHInBoxT_1d4000000_3999999d4000000_632923d4_158256
import RHInBoxT_1d4000000_3999999d4000000_158256_158282
import RHInBoxT_1d4000000_3999999d4000000_158282_158308
import RHInBoxT_1d4000000_3999999d4000000_158308_158333
import RHInBoxT_1d4000000_3999999d4000000_158333_158359
import RHInBoxT_1d4000000_3999999d4000000_158359_158385
import RHInBoxT_1d4000000_3999999d4000000_633539d4_158410
import RHInBoxT_1d4000000_3999999d4000000_158410_633745d4
import RHInBoxT_1d4000000_3999999d4000000_158436_158462
import RHInBoxT_1d4000000_3999999d4000000_158462_158487
import RHInBoxT_1d4000000_3999999d4000000_158487_158513
import RHInBoxT_1d4000000_3999999d4000000_158513_158538
import RHInBoxT_1d4000000_3999999d4000000_158538_158564
import RHInBoxT_1d4000000_3999999d4000000_158564_158590
import RHInBoxT_1d4000000_3999999d4000000_158590_634461d4
import RHInBoxT_1d4000000_3999999d4000000_158615_158641
import RHInBoxT_1d4000000_3999999d4000000_158641_158667
import RHInBoxT_1d4000000_3999999d4000000_158667_158692
import RHInBoxT_1d4000000_3999999d4000000_158692_158718
import RHInBoxT_1d4000000_3999999d4000000_158718_158744
import RHInBoxT_1d4000000_3999999d4000000_158744_158769
import RHInBoxT_1d4000000_3999999d4000000_158769_158795
import RHInBoxT_1d4000000_3999999d4000000_158795_158821
import RHInBoxT_1d4000000_3999999d4000000_158821_158846
import RHInBoxT_1d4000000_3999999d4000000_158846_158872
import RHInBoxT_1d4000000_3999999d4000000_158872_158897
import RHInBoxT_1d4000000_3999999d4000000_158897_158923
import RHInBoxT_1d4000000_3999999d4000000_158923_635797d4
import RHInBoxT_1d4000000_3999999d4000000_158949_158974
import RHInBoxT_1d4000000_3999999d4000000_158974_159000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h159000

/-- The 39-band NOMINAL partition of `[158000, 159000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 158000
  | 1 => 158026
  | 2 => 158051
  | 3 => 158077
  | 4 => 158103
  | 5 => 158128
  | 6 => 158154
  | 7 => 158179
  | 8 => 158205
  | 9 => 158231
  | 10 => 158256
  | 11 => 158282
  | 12 => 158308
  | 13 => 158333
  | 14 => 158359
  | 15 => 158385
  | 16 => 158410
  | 17 => 158436
  | 18 => 158462
  | 19 => 158487
  | 20 => 158513
  | 21 => 158538
  | 22 => 158564
  | 23 => 158590
  | 24 => 158615
  | 25 => 158641
  | 26 => 158667
  | 27 => 158692
  | 28 => 158718
  | 29 => 158744
  | 30 => 158769
  | 31 => 158795
  | 32 => 158821
  | 33 => 158846
  | 34 => 158872
  | 35 => 158897
  | 36 => 158923
  | 37 => 158949
  | 38 => 158974
  | 39 => 159000
  | _ => 159000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((158000:ℝ)) ≤ (158026); norm_num
  · show ((158026:ℝ)) ≤ (158051); norm_num
  · show ((158051:ℝ)) ≤ (158077); norm_num
  · show ((158077:ℝ)) ≤ (158103); norm_num
  · show ((158103:ℝ)) ≤ (158128); norm_num
  · show ((158128:ℝ)) ≤ (158154); norm_num
  · show ((158154:ℝ)) ≤ (158179); norm_num
  · show ((158179:ℝ)) ≤ (158205); norm_num
  · show ((158205:ℝ)) ≤ (158231); norm_num
  · show ((158231:ℝ)) ≤ (158256); norm_num
  · show ((158256:ℝ)) ≤ (158282); norm_num
  · show ((158282:ℝ)) ≤ (158308); norm_num
  · show ((158308:ℝ)) ≤ (158333); norm_num
  · show ((158333:ℝ)) ≤ (158359); norm_num
  · show ((158359:ℝ)) ≤ (158385); norm_num
  · show ((158385:ℝ)) ≤ (158410); norm_num
  · show ((158410:ℝ)) ≤ (158436); norm_num
  · show ((158436:ℝ)) ≤ (158462); norm_num
  · show ((158462:ℝ)) ≤ (158487); norm_num
  · show ((158487:ℝ)) ≤ (158513); norm_num
  · show ((158513:ℝ)) ≤ (158538); norm_num
  · show ((158538:ℝ)) ≤ (158564); norm_num
  · show ((158564:ℝ)) ≤ (158590); norm_num
  · show ((158590:ℝ)) ≤ (158615); norm_num
  · show ((158615:ℝ)) ≤ (158641); norm_num
  · show ((158641:ℝ)) ≤ (158667); norm_num
  · show ((158667:ℝ)) ≤ (158692); norm_num
  · show ((158692:ℝ)) ≤ (158718); norm_num
  · show ((158718:ℝ)) ≤ (158744); norm_num
  · show ((158744:ℝ)) ≤ (158769); norm_num
  · show ((158769:ℝ)) ≤ (158795); norm_num
  · show ((158795:ℝ)) ≤ (158821); norm_num
  · show ((158821:ℝ)) ≤ (158846); norm_num
  · show ((158846:ℝ)) ≤ (158872); norm_num
  · show ((158872:ℝ)) ≤ (158897); norm_num
  · show ((158897:ℝ)) ≤ (158923); norm_num
  · show ((158923:ℝ)) ≤ (158949); norm_num
  · show ((158949:ℝ)) ≤ (158974); norm_num
  · show ((158974:ℝ)) ≤ (159000); norm_num
  · show ((159000:ℝ)) ≤ (159000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 158000
  | 1 => 158026
  | 2 => 158051
  | 3 => 158077
  | 4 => 158103
  | 5 => 632511 / 4
  | 6 => 158154
  | 7 => 158179
  | 8 => 158205
  | 9 => 632923 / 4
  | 10 => 158256
  | 11 => 158282
  | 12 => 158308
  | 13 => 158333
  | 14 => 158359
  | 15 => 633539 / 4
  | 16 => 158410
  | 17 => 158436
  | 18 => 158462
  | 19 => 158487
  | 20 => 158513
  | 21 => 158538
  | 22 => 158564
  | 23 => 158590
  | 24 => 158615
  | 25 => 158641
  | 26 => 158667
  | 27 => 158692
  | 28 => 158718
  | 29 => 158744
  | 30 => 158769
  | 31 => 158795
  | 32 => 158821
  | 33 => 158846
  | 34 => 158872
  | 35 => 158897
  | 36 => 158923
  | 37 => 158949
  | 38 => 158974
  | _ => 158974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 158026
  | 1 => 158051
  | 2 => 158077
  | 3 => 158103
  | 4 => 158128
  | 5 => 158154
  | 6 => 158179
  | 7 => 158205
  | 8 => 158231
  | 9 => 158256
  | 10 => 158282
  | 11 => 158308
  | 12 => 158333
  | 13 => 158359
  | 14 => 158385
  | 15 => 158410
  | 16 => 633745 / 4
  | 17 => 158462
  | 18 => 158487
  | 19 => 158513
  | 20 => 158538
  | 21 => 158564
  | 22 => 158590
  | 23 => 634461 / 4
  | 24 => 158641
  | 25 => 158667
  | 26 => 158692
  | 27 => 158718
  | 28 => 158744
  | 29 => 158769
  | 30 => 158795
  | 31 => 158821
  | 32 => 158846
  | 33 => 158872
  | 34 => 158897
  | 35 => 158923
  | 36 => 635797 / 4
  | 37 => 158974
  | 38 => 159000
  | _ => 159000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 159000` (`log 159000 ≤ 13`, `2.7^13 ≥ 159000`). -/
theorem haC_159000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 159000 := by
  have hlog : Real.log 159000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 159000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 159000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[158000, 159000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[158000, 159000]` SEGMENT: every zero with `158000 ≤ Im ≤ 159000` is on the line. -/
theorem segment_158000_159000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 159000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (158000:ℝ) ≤ ρ.im → ρ.im ≤ 159000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 158000 159000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_159000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 159000 via the HEIGHT CHAIN**: `[0,158000]` ∘ `[158000,159000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_159000_of_bands
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
    (hbands_37000 : AllZeros_h37000.BandHyp)
    (hbands_38000 : AllZeros_h38000.BandHyp)
    (hbands_39000 : AllZeros_h39000.BandHyp)
    (hbands_40000 : AllZeros_h40000.BandHyp)
    (hbands_41000 : AllZeros_h41000.BandHyp)
    (hbands_42000 : AllZeros_h42000.BandHyp)
    (hbands_43000 : AllZeros_h43000.BandHyp)
    (hbands_44000 : AllZeros_h44000.BandHyp)
    (hbands_45000 : AllZeros_h45000.BandHyp)
    (hbands_46000 : AllZeros_h46000.BandHyp)
    (hbands_47000 : AllZeros_h47000.BandHyp)
    (hbands_48000 : AllZeros_h48000.BandHyp)
    (hbands_49000 : AllZeros_h49000.BandHyp)
    (hbands_50000 : AllZeros_h50000.BandHyp)
    (hbands_51000 : AllZeros_h51000.BandHyp)
    (hbands_52000 : AllZeros_h52000.BandHyp)
    (hbands_53000 : AllZeros_h53000.BandHyp)
    (hbands_54000 : AllZeros_h54000.BandHyp)
    (hbands_55000 : AllZeros_h55000.BandHyp)
    (hbands_56000 : AllZeros_h56000.BandHyp)
    (hbands_57000 : AllZeros_h57000.BandHyp)
    (hbands_58000 : AllZeros_h58000.BandHyp)
    (hbands_59000 : AllZeros_h59000.BandHyp)
    (hbands_60000 : AllZeros_h60000.BandHyp)
    (hbands_61000 : AllZeros_h61000.BandHyp)
    (hbands_62000 : AllZeros_h62000.BandHyp)
    (hbands_63000 : AllZeros_h63000.BandHyp)
    (hbands_64000 : AllZeros_h64000.BandHyp)
    (hbands_65000 : AllZeros_h65000.BandHyp)
    (hbands_66000 : AllZeros_h66000.BandHyp)
    (hbands_67000 : AllZeros_h67000.BandHyp)
    (hbands_68000 : AllZeros_h68000.BandHyp)
    (hbands_69000 : AllZeros_h69000.BandHyp)
    (hbands_70000 : AllZeros_h70000.BandHyp)
    (hbands_71000 : AllZeros_h71000.BandHyp)
    (hbands_72000 : AllZeros_h72000.BandHyp)
    (hbands_73000 : AllZeros_h73000.BandHyp)
    (hbands_74000 : AllZeros_h74000.BandHyp)
    (hbands_75000 : AllZeros_h75000.BandHyp)
    (hbands_76000 : AllZeros_h76000.BandHyp)
    (hbands_77000 : AllZeros_h77000.BandHyp)
    (hbands_78000 : AllZeros_h78000.BandHyp)
    (hbands_79000 : AllZeros_h79000.BandHyp)
    (hbands_80000 : AllZeros_h80000.BandHyp)
    (hbands_81000 : AllZeros_h81000.BandHyp)
    (hbands_82000 : AllZeros_h82000.BandHyp)
    (hbands_83000 : AllZeros_h83000.BandHyp)
    (hbands_84000 : AllZeros_h84000.BandHyp)
    (hbands_85000 : AllZeros_h85000.BandHyp)
    (hbands_86000 : AllZeros_h86000.BandHyp)
    (hbands_87000 : AllZeros_h87000.BandHyp)
    (hbands_88000 : AllZeros_h88000.BandHyp)
    (hbands_89000 : AllZeros_h89000.BandHyp)
    (hbands_90000 : AllZeros_h90000.BandHyp)
    (hbands_91000 : AllZeros_h91000.BandHyp)
    (hbands_92000 : AllZeros_h92000.BandHyp)
    (hbands_93000 : AllZeros_h93000.BandHyp)
    (hbands_94000 : AllZeros_h94000.BandHyp)
    (hbands_95000 : AllZeros_h95000.BandHyp)
    (hbands_96000 : AllZeros_h96000.BandHyp)
    (hbands_97000 : AllZeros_h97000.BandHyp)
    (hbands_98000 : AllZeros_h98000.BandHyp)
    (hbands_99000 : AllZeros_h99000.BandHyp)
    (hbands_100000 : AllZeros_h100000.BandHyp)
    (hbands_101000 : AllZeros_h101000.BandHyp)
    (hbands_102000 : AllZeros_h102000.BandHyp)
    (hbands_103000 : AllZeros_h103000.BandHyp)
    (hbands_104000 : AllZeros_h104000.BandHyp)
    (hbands_105000 : AllZeros_h105000.BandHyp)
    (hbands_106000 : AllZeros_h106000.BandHyp)
    (hbands_107000 : AllZeros_h107000.BandHyp)
    (hbands_108000 : AllZeros_h108000.BandHyp)
    (hbands_109000 : AllZeros_h109000.BandHyp)
    (hbands_110000 : AllZeros_h110000.BandHyp)
    (hbands_111000 : AllZeros_h111000.BandHyp)
    (hbands_112000 : AllZeros_h112000.BandHyp)
    (hbands_113000 : AllZeros_h113000.BandHyp)
    (hbands_114000 : AllZeros_h114000.BandHyp)
    (hbands_115000 : AllZeros_h115000.BandHyp)
    (hbands_116000 : AllZeros_h116000.BandHyp)
    (hbands_117000 : AllZeros_h117000.BandHyp)
    (hbands_118000 : AllZeros_h118000.BandHyp)
    (hbands_119000 : AllZeros_h119000.BandHyp)
    (hbands_120000 : AllZeros_h120000.BandHyp)
    (hbands_121000 : AllZeros_h121000.BandHyp)
    (hbands_122000 : AllZeros_h122000.BandHyp)
    (hbands_123000 : AllZeros_h123000.BandHyp)
    (hbands_124000 : AllZeros_h124000.BandHyp)
    (hbands_125000 : AllZeros_h125000.BandHyp)
    (hbands_126000 : AllZeros_h126000.BandHyp)
    (hbands_127000 : AllZeros_h127000.BandHyp)
    (hbands_128000 : AllZeros_h128000.BandHyp)
    (hbands_129000 : AllZeros_h129000.BandHyp)
    (hbands_130000 : AllZeros_h130000.BandHyp)
    (hbands_131000 : AllZeros_h131000.BandHyp)
    (hbands_132000 : AllZeros_h132000.BandHyp)
    (hbands_133000 : AllZeros_h133000.BandHyp)
    (hbands_134000 : AllZeros_h134000.BandHyp)
    (hbands_135000 : AllZeros_h135000.BandHyp)
    (hbands_136000 : AllZeros_h136000.BandHyp)
    (hbands_137000 : AllZeros_h137000.BandHyp)
    (hbands_138000 : AllZeros_h138000.BandHyp)
    (hbands_139000 : AllZeros_h139000.BandHyp)
    (hbands_140000 : AllZeros_h140000.BandHyp)
    (hbands_141000 : AllZeros_h141000.BandHyp)
    (hbands_142000 : AllZeros_h142000.BandHyp)
    (hbands_143000 : AllZeros_h143000.BandHyp)
    (hbands_144000 : AllZeros_h144000.BandHyp)
    (hbands_145000 : AllZeros_h145000.BandHyp)
    (hbands_146000 : AllZeros_h146000.BandHyp)
    (hbands_147000 : AllZeros_h147000.BandHyp)
    (hbands_148000 : AllZeros_h148000.BandHyp)
    (hbands_149000 : AllZeros_h149000.BandHyp)
    (hbands_150000 : AllZeros_h150000.BandHyp)
    (hbands_151000 : AllZeros_h151000.BandHyp)
    (hbands_152000 : AllZeros_h152000.BandHyp)
    (hbands_153000 : AllZeros_h153000.BandHyp)
    (hbands_154000 : AllZeros_h154000.BandHyp)
    (hbands_155000 : AllZeros_h155000.BandHyp)
    (hbands_156000 : AllZeros_h156000.BandHyp)
    (hbands_157000 : AllZeros_h157000.BandHyp)
    (hbands_158000 : AllZeros_h158000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 159000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 159000 → ρ.re = 1 / 2 := by
  have hγ158000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 158000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 158000 159000
    (AllZeros_h158000.all_nontrivial_zeros_up_to_height_158000_of_bands
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
      hbands_37000
      hbands_38000
      hbands_39000
      hbands_40000
      hbands_41000
      hbands_42000
      hbands_43000
      hbands_44000
      hbands_45000
      hbands_46000
      hbands_47000
      hbands_48000
      hbands_49000
      hbands_50000
      hbands_51000
      hbands_52000
      hbands_53000
      hbands_54000
      hbands_55000
      hbands_56000
      hbands_57000
      hbands_58000
      hbands_59000
      hbands_60000
      hbands_61000
      hbands_62000
      hbands_63000
      hbands_64000
      hbands_65000
      hbands_66000
      hbands_67000
      hbands_68000
      hbands_69000
      hbands_70000
      hbands_71000
      hbands_72000
      hbands_73000
      hbands_74000
      hbands_75000
      hbands_76000
      hbands_77000
      hbands_78000
      hbands_79000
      hbands_80000
      hbands_81000
      hbands_82000
      hbands_83000
      hbands_84000
      hbands_85000
      hbands_86000
      hbands_87000
      hbands_88000
      hbands_89000
      hbands_90000
      hbands_91000
      hbands_92000
      hbands_93000
      hbands_94000
      hbands_95000
      hbands_96000
      hbands_97000
      hbands_98000
      hbands_99000
      hbands_100000
      hbands_101000
      hbands_102000
      hbands_103000
      hbands_104000
      hbands_105000
      hbands_106000
      hbands_107000
      hbands_108000
      hbands_109000
      hbands_110000
      hbands_111000
      hbands_112000
      hbands_113000
      hbands_114000
      hbands_115000
      hbands_116000
      hbands_117000
      hbands_118000
      hbands_119000
      hbands_120000
      hbands_121000
      hbands_122000
      hbands_123000
      hbands_124000
      hbands_125000
      hbands_126000
      hbands_127000
      hbands_128000
      hbands_129000
      hbands_130000
      hbands_131000
      hbands_132000
      hbands_133000
      hbands_134000
      hbands_135000
      hbands_136000
      hbands_137000
      hbands_138000
      hbands_139000
      hbands_140000
      hbands_141000
      hbands_142000
      hbands_143000
      hbands_144000
      hbands_145000
      hbands_146000
      hbands_147000
      hbands_148000
      hbands_149000
      hbands_150000
      hbands_151000
      hbands_152000
      hbands_153000
      hbands_154000
      hbands_155000
      hbands_156000
      hbands_157000
      hbands_158000
      hγ158000)
    (segment_158000_159000 hbands hγ)

end AllZeros_h159000

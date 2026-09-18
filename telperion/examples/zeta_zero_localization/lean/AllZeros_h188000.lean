/-  Height-chain step: all nontrivial zeta zeros up to height 188000 on Re = 1/2 --
    `AllZeros_h187000` + a `[187000, 188000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h187000
import RHInBoxT_1d4000000_3999999d4000000_187000_187026
import RHInBoxT_1d4000000_3999999d4000000_187026_187051
import RHInBoxT_1d4000000_3999999d4000000_187051_187077
import RHInBoxT_1d4000000_3999999d4000000_187077_187103
import RHInBoxT_1d4000000_3999999d4000000_187103_187128
import RHInBoxT_1d4000000_3999999d4000000_748511d4_748617d4
import RHInBoxT_1d4000000_3999999d4000000_187154_187179
import RHInBoxT_1d4000000_3999999d4000000_187179_187205
import RHInBoxT_1d4000000_3999999d4000000_748819d4_748925d4
import RHInBoxT_1d4000000_3999999d4000000_187231_187256
import RHInBoxT_1d4000000_3999999d4000000_749023d4_374565d2
import RHInBoxT_1d4000000_3999999d4000000_187282_187308
import RHInBoxT_1d4000000_3999999d4000000_187308_187333
import RHInBoxT_1d4000000_3999999d4000000_187333_187359
import RHInBoxT_1d4000000_3999999d4000000_187359_187385
import RHInBoxT_1d4000000_3999999d4000000_187385_187410
import RHInBoxT_1d4000000_3999999d4000000_187410_749745d4
import RHInBoxT_1d4000000_3999999d4000000_187436_187462
import RHInBoxT_1d4000000_3999999d4000000_187462_187487
import RHInBoxT_1d4000000_3999999d4000000_187487_187513
import RHInBoxT_1d4000000_3999999d4000000_187513_750153d4
import RHInBoxT_1d4000000_3999999d4000000_187538_187564
import RHInBoxT_1d4000000_3999999d4000000_750255d4_187590
import RHInBoxT_1d4000000_3999999d4000000_187590_187615
import RHInBoxT_1d4000000_3999999d4000000_187615_187641
import RHInBoxT_1d4000000_3999999d4000000_187641_187667
import RHInBoxT_1d4000000_3999999d4000000_750667d4_187692
import RHInBoxT_1d4000000_3999999d4000000_187692_187718
import RHInBoxT_1d4000000_3999999d4000000_187718_187744
import RHInBoxT_1d4000000_3999999d4000000_187744_751077d4
import RHInBoxT_1d4000000_3999999d4000000_187769_187795
import RHInBoxT_1d4000000_3999999d4000000_187795_187821
import RHInBoxT_1d4000000_3999999d4000000_187821_751385d4
import RHInBoxT_1d4000000_3999999d4000000_187846_187872
import RHInBoxT_1d4000000_3999999d4000000_751487d4_187897
import RHInBoxT_1d4000000_3999999d4000000_751587d4_187923
import RHInBoxT_1d4000000_3999999d4000000_187923_751797d4
import RHInBoxT_1d4000000_3999999d4000000_187949_187974
import RHInBoxT_1d4000000_3999999d4000000_187974_188000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h188000

/-- The 39-band NOMINAL partition of `[187000, 188000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 187000
  | 1 => 187026
  | 2 => 187051
  | 3 => 187077
  | 4 => 187103
  | 5 => 187128
  | 6 => 187154
  | 7 => 187179
  | 8 => 187205
  | 9 => 187231
  | 10 => 187256
  | 11 => 187282
  | 12 => 187308
  | 13 => 187333
  | 14 => 187359
  | 15 => 187385
  | 16 => 187410
  | 17 => 187436
  | 18 => 187462
  | 19 => 187487
  | 20 => 187513
  | 21 => 187538
  | 22 => 187564
  | 23 => 187590
  | 24 => 187615
  | 25 => 187641
  | 26 => 187667
  | 27 => 187692
  | 28 => 187718
  | 29 => 187744
  | 30 => 187769
  | 31 => 187795
  | 32 => 187821
  | 33 => 187846
  | 34 => 187872
  | 35 => 187897
  | 36 => 187923
  | 37 => 187949
  | 38 => 187974
  | 39 => 188000
  | _ => 188000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((187000:ℝ)) ≤ (187026); norm_num
  · show ((187026:ℝ)) ≤ (187051); norm_num
  · show ((187051:ℝ)) ≤ (187077); norm_num
  · show ((187077:ℝ)) ≤ (187103); norm_num
  · show ((187103:ℝ)) ≤ (187128); norm_num
  · show ((187128:ℝ)) ≤ (187154); norm_num
  · show ((187154:ℝ)) ≤ (187179); norm_num
  · show ((187179:ℝ)) ≤ (187205); norm_num
  · show ((187205:ℝ)) ≤ (187231); norm_num
  · show ((187231:ℝ)) ≤ (187256); norm_num
  · show ((187256:ℝ)) ≤ (187282); norm_num
  · show ((187282:ℝ)) ≤ (187308); norm_num
  · show ((187308:ℝ)) ≤ (187333); norm_num
  · show ((187333:ℝ)) ≤ (187359); norm_num
  · show ((187359:ℝ)) ≤ (187385); norm_num
  · show ((187385:ℝ)) ≤ (187410); norm_num
  · show ((187410:ℝ)) ≤ (187436); norm_num
  · show ((187436:ℝ)) ≤ (187462); norm_num
  · show ((187462:ℝ)) ≤ (187487); norm_num
  · show ((187487:ℝ)) ≤ (187513); norm_num
  · show ((187513:ℝ)) ≤ (187538); norm_num
  · show ((187538:ℝ)) ≤ (187564); norm_num
  · show ((187564:ℝ)) ≤ (187590); norm_num
  · show ((187590:ℝ)) ≤ (187615); norm_num
  · show ((187615:ℝ)) ≤ (187641); norm_num
  · show ((187641:ℝ)) ≤ (187667); norm_num
  · show ((187667:ℝ)) ≤ (187692); norm_num
  · show ((187692:ℝ)) ≤ (187718); norm_num
  · show ((187718:ℝ)) ≤ (187744); norm_num
  · show ((187744:ℝ)) ≤ (187769); norm_num
  · show ((187769:ℝ)) ≤ (187795); norm_num
  · show ((187795:ℝ)) ≤ (187821); norm_num
  · show ((187821:ℝ)) ≤ (187846); norm_num
  · show ((187846:ℝ)) ≤ (187872); norm_num
  · show ((187872:ℝ)) ≤ (187897); norm_num
  · show ((187897:ℝ)) ≤ (187923); norm_num
  · show ((187923:ℝ)) ≤ (187949); norm_num
  · show ((187949:ℝ)) ≤ (187974); norm_num
  · show ((187974:ℝ)) ≤ (188000); norm_num
  · show ((188000:ℝ)) ≤ (188000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 187000
  | 1 => 187026
  | 2 => 187051
  | 3 => 187077
  | 4 => 187103
  | 5 => 748511 / 4
  | 6 => 187154
  | 7 => 187179
  | 8 => 748819 / 4
  | 9 => 187231
  | 10 => 749023 / 4
  | 11 => 187282
  | 12 => 187308
  | 13 => 187333
  | 14 => 187359
  | 15 => 187385
  | 16 => 187410
  | 17 => 187436
  | 18 => 187462
  | 19 => 187487
  | 20 => 187513
  | 21 => 187538
  | 22 => 750255 / 4
  | 23 => 187590
  | 24 => 187615
  | 25 => 187641
  | 26 => 750667 / 4
  | 27 => 187692
  | 28 => 187718
  | 29 => 187744
  | 30 => 187769
  | 31 => 187795
  | 32 => 187821
  | 33 => 187846
  | 34 => 751487 / 4
  | 35 => 751587 / 4
  | 36 => 187923
  | 37 => 187949
  | 38 => 187974
  | _ => 187974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 187026
  | 1 => 187051
  | 2 => 187077
  | 3 => 187103
  | 4 => 187128
  | 5 => 748617 / 4
  | 6 => 187179
  | 7 => 187205
  | 8 => 748925 / 4
  | 9 => 187256
  | 10 => 374565 / 2
  | 11 => 187308
  | 12 => 187333
  | 13 => 187359
  | 14 => 187385
  | 15 => 187410
  | 16 => 749745 / 4
  | 17 => 187462
  | 18 => 187487
  | 19 => 187513
  | 20 => 750153 / 4
  | 21 => 187564
  | 22 => 187590
  | 23 => 187615
  | 24 => 187641
  | 25 => 187667
  | 26 => 187692
  | 27 => 187718
  | 28 => 187744
  | 29 => 751077 / 4
  | 30 => 187795
  | 31 => 187821
  | 32 => 751385 / 4
  | 33 => 187872
  | 34 => 187897
  | 35 => 187923
  | 36 => 751797 / 4
  | 37 => 187974
  | 38 => 188000
  | _ => 188000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 188000` (`log 188000 ≤ 13`, `2.7^13 ≥ 188000`). -/
theorem haC_188000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 188000 := by
  have hlog : Real.log 188000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 188000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 188000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[187000, 188000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[187000, 188000]` SEGMENT: every zero with `187000 ≤ Im ≤ 188000` is on the line. -/
theorem segment_187000_188000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 188000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (187000:ℝ) ≤ ρ.im → ρ.im ≤ 188000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 187000 188000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_188000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 188000 via the HEIGHT CHAIN**: `[0,187000]` ∘ `[187000,188000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_188000_of_bands
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
    (hbands_159000 : AllZeros_h159000.BandHyp)
    (hbands_160000 : AllZeros_h160000.BandHyp)
    (hbands_161000 : AllZeros_h161000.BandHyp)
    (hbands_162000 : AllZeros_h162000.BandHyp)
    (hbands_163000 : AllZeros_h163000.BandHyp)
    (hbands_164000 : AllZeros_h164000.BandHyp)
    (hbands_165000 : AllZeros_h165000.BandHyp)
    (hbands_166000 : AllZeros_h166000.BandHyp)
    (hbands_167000 : AllZeros_h167000.BandHyp)
    (hbands_168000 : AllZeros_h168000.BandHyp)
    (hbands_169000 : AllZeros_h169000.BandHyp)
    (hbands_170000 : AllZeros_h170000.BandHyp)
    (hbands_171000 : AllZeros_h171000.BandHyp)
    (hbands_172000 : AllZeros_h172000.BandHyp)
    (hbands_173000 : AllZeros_h173000.BandHyp)
    (hbands_174000 : AllZeros_h174000.BandHyp)
    (hbands_175000 : AllZeros_h175000.BandHyp)
    (hbands_176000 : AllZeros_h176000.BandHyp)
    (hbands_177000 : AllZeros_h177000.BandHyp)
    (hbands_178000 : AllZeros_h178000.BandHyp)
    (hbands_179000 : AllZeros_h179000.BandHyp)
    (hbands_180000 : AllZeros_h180000.BandHyp)
    (hbands_181000 : AllZeros_h181000.BandHyp)
    (hbands_182000 : AllZeros_h182000.BandHyp)
    (hbands_183000 : AllZeros_h183000.BandHyp)
    (hbands_184000 : AllZeros_h184000.BandHyp)
    (hbands_185000 : AllZeros_h185000.BandHyp)
    (hbands_186000 : AllZeros_h186000.BandHyp)
    (hbands_187000 : AllZeros_h187000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 188000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 188000 → ρ.re = 1 / 2 := by
  have hγ187000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 187000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 187000 188000
    (AllZeros_h187000.all_nontrivial_zeros_up_to_height_187000_of_bands
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
      hbands_159000
      hbands_160000
      hbands_161000
      hbands_162000
      hbands_163000
      hbands_164000
      hbands_165000
      hbands_166000
      hbands_167000
      hbands_168000
      hbands_169000
      hbands_170000
      hbands_171000
      hbands_172000
      hbands_173000
      hbands_174000
      hbands_175000
      hbands_176000
      hbands_177000
      hbands_178000
      hbands_179000
      hbands_180000
      hbands_181000
      hbands_182000
      hbands_183000
      hbands_184000
      hbands_185000
      hbands_186000
      hbands_187000
      hγ187000)
    (segment_187000_188000 hbands hγ)

end AllZeros_h188000

/-  Height-chain step: all nontrivial zeta zeros up to height 153000 on Re = 1/2 --
    `AllZeros_h152000` + a `[152000, 153000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h152000
import RHInBoxT_1d4000000_3999999d4000000_152000_608105d4
import RHInBoxT_1d4000000_3999999d4000000_608103d4_152051
import RHInBoxT_1d4000000_3999999d4000000_152051_152077
import RHInBoxT_1d4000000_3999999d4000000_152077_152103
import RHInBoxT_1d4000000_3999999d4000000_152103_152128
import RHInBoxT_1d4000000_3999999d4000000_304255d2_152154
import RHInBoxT_1d4000000_3999999d4000000_152154_152179
import RHInBoxT_1d4000000_3999999d4000000_152179_152205
import RHInBoxT_1d4000000_3999999d4000000_608819d4_152231
import RHInBoxT_1d4000000_3999999d4000000_152231_609025d4
import RHInBoxT_1d4000000_3999999d4000000_152256_152282
import RHInBoxT_1d4000000_3999999d4000000_152282_152308
import RHInBoxT_1d4000000_3999999d4000000_152308_152333
import RHInBoxT_1d4000000_3999999d4000000_152333_152359
import RHInBoxT_1d4000000_3999999d4000000_152359_152385
import RHInBoxT_1d4000000_3999999d4000000_152385_152410
import RHInBoxT_1d4000000_3999999d4000000_152410_609745d4
import RHInBoxT_1d4000000_3999999d4000000_152436_152462
import RHInBoxT_1d4000000_3999999d4000000_152462_609949d4
import RHInBoxT_1d4000000_3999999d4000000_152487_152513
import RHInBoxT_1d4000000_3999999d4000000_610051d4_152538
import RHInBoxT_1d4000000_3999999d4000000_152538_152564
import RHInBoxT_1d4000000_3999999d4000000_152564_152590
import RHInBoxT_1d4000000_3999999d4000000_152590_152615
import RHInBoxT_1d4000000_3999999d4000000_152615_152641
import RHInBoxT_1d4000000_3999999d4000000_152641_152667
import RHInBoxT_1d4000000_3999999d4000000_152667_152692
import RHInBoxT_1d4000000_3999999d4000000_152692_152718
import RHInBoxT_1d4000000_3999999d4000000_152718_152744
import RHInBoxT_1d4000000_3999999d4000000_152744_152769
import RHInBoxT_1d4000000_3999999d4000000_611075d4_152795
import RHInBoxT_1d4000000_3999999d4000000_152795_152821
import RHInBoxT_1d4000000_3999999d4000000_152821_611385d4
import RHInBoxT_1d4000000_3999999d4000000_152846_152872
import RHInBoxT_1d4000000_3999999d4000000_152872_152897
import RHInBoxT_1d4000000_3999999d4000000_152897_152923
import RHInBoxT_1d4000000_3999999d4000000_152923_152949
import RHInBoxT_1d4000000_3999999d4000000_152949_611897d4
import RHInBoxT_1d4000000_3999999d4000000_152974_153000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h153000

/-- The 39-band NOMINAL partition of `[152000, 153000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 152000
  | 1 => 152026
  | 2 => 152051
  | 3 => 152077
  | 4 => 152103
  | 5 => 152128
  | 6 => 152154
  | 7 => 152179
  | 8 => 152205
  | 9 => 152231
  | 10 => 152256
  | 11 => 152282
  | 12 => 152308
  | 13 => 152333
  | 14 => 152359
  | 15 => 152385
  | 16 => 152410
  | 17 => 152436
  | 18 => 152462
  | 19 => 152487
  | 20 => 152513
  | 21 => 152538
  | 22 => 152564
  | 23 => 152590
  | 24 => 152615
  | 25 => 152641
  | 26 => 152667
  | 27 => 152692
  | 28 => 152718
  | 29 => 152744
  | 30 => 152769
  | 31 => 152795
  | 32 => 152821
  | 33 => 152846
  | 34 => 152872
  | 35 => 152897
  | 36 => 152923
  | 37 => 152949
  | 38 => 152974
  | 39 => 153000
  | _ => 153000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((152000:ℝ)) ≤ (152026); norm_num
  · show ((152026:ℝ)) ≤ (152051); norm_num
  · show ((152051:ℝ)) ≤ (152077); norm_num
  · show ((152077:ℝ)) ≤ (152103); norm_num
  · show ((152103:ℝ)) ≤ (152128); norm_num
  · show ((152128:ℝ)) ≤ (152154); norm_num
  · show ((152154:ℝ)) ≤ (152179); norm_num
  · show ((152179:ℝ)) ≤ (152205); norm_num
  · show ((152205:ℝ)) ≤ (152231); norm_num
  · show ((152231:ℝ)) ≤ (152256); norm_num
  · show ((152256:ℝ)) ≤ (152282); norm_num
  · show ((152282:ℝ)) ≤ (152308); norm_num
  · show ((152308:ℝ)) ≤ (152333); norm_num
  · show ((152333:ℝ)) ≤ (152359); norm_num
  · show ((152359:ℝ)) ≤ (152385); norm_num
  · show ((152385:ℝ)) ≤ (152410); norm_num
  · show ((152410:ℝ)) ≤ (152436); norm_num
  · show ((152436:ℝ)) ≤ (152462); norm_num
  · show ((152462:ℝ)) ≤ (152487); norm_num
  · show ((152487:ℝ)) ≤ (152513); norm_num
  · show ((152513:ℝ)) ≤ (152538); norm_num
  · show ((152538:ℝ)) ≤ (152564); norm_num
  · show ((152564:ℝ)) ≤ (152590); norm_num
  · show ((152590:ℝ)) ≤ (152615); norm_num
  · show ((152615:ℝ)) ≤ (152641); norm_num
  · show ((152641:ℝ)) ≤ (152667); norm_num
  · show ((152667:ℝ)) ≤ (152692); norm_num
  · show ((152692:ℝ)) ≤ (152718); norm_num
  · show ((152718:ℝ)) ≤ (152744); norm_num
  · show ((152744:ℝ)) ≤ (152769); norm_num
  · show ((152769:ℝ)) ≤ (152795); norm_num
  · show ((152795:ℝ)) ≤ (152821); norm_num
  · show ((152821:ℝ)) ≤ (152846); norm_num
  · show ((152846:ℝ)) ≤ (152872); norm_num
  · show ((152872:ℝ)) ≤ (152897); norm_num
  · show ((152897:ℝ)) ≤ (152923); norm_num
  · show ((152923:ℝ)) ≤ (152949); norm_num
  · show ((152949:ℝ)) ≤ (152974); norm_num
  · show ((152974:ℝ)) ≤ (153000); norm_num
  · show ((153000:ℝ)) ≤ (153000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 152000
  | 1 => 608103 / 4
  | 2 => 152051
  | 3 => 152077
  | 4 => 152103
  | 5 => 304255 / 2
  | 6 => 152154
  | 7 => 152179
  | 8 => 608819 / 4
  | 9 => 152231
  | 10 => 152256
  | 11 => 152282
  | 12 => 152308
  | 13 => 152333
  | 14 => 152359
  | 15 => 152385
  | 16 => 152410
  | 17 => 152436
  | 18 => 152462
  | 19 => 152487
  | 20 => 610051 / 4
  | 21 => 152538
  | 22 => 152564
  | 23 => 152590
  | 24 => 152615
  | 25 => 152641
  | 26 => 152667
  | 27 => 152692
  | 28 => 152718
  | 29 => 152744
  | 30 => 611075 / 4
  | 31 => 152795
  | 32 => 152821
  | 33 => 152846
  | 34 => 152872
  | 35 => 152897
  | 36 => 152923
  | 37 => 152949
  | 38 => 152974
  | _ => 152974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 608105 / 4
  | 1 => 152051
  | 2 => 152077
  | 3 => 152103
  | 4 => 152128
  | 5 => 152154
  | 6 => 152179
  | 7 => 152205
  | 8 => 152231
  | 9 => 609025 / 4
  | 10 => 152282
  | 11 => 152308
  | 12 => 152333
  | 13 => 152359
  | 14 => 152385
  | 15 => 152410
  | 16 => 609745 / 4
  | 17 => 152462
  | 18 => 609949 / 4
  | 19 => 152513
  | 20 => 152538
  | 21 => 152564
  | 22 => 152590
  | 23 => 152615
  | 24 => 152641
  | 25 => 152667
  | 26 => 152692
  | 27 => 152718
  | 28 => 152744
  | 29 => 152769
  | 30 => 152795
  | 31 => 152821
  | 32 => 611385 / 4
  | 33 => 152872
  | 34 => 152897
  | 35 => 152923
  | 36 => 152949
  | 37 => 611897 / 4
  | 38 => 153000
  | _ => 153000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 153000` (`log 153000 ≤ 13`, `2.7^13 ≥ 153000`). -/
theorem haC_153000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 153000 := by
  have hlog : Real.log 153000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 153000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 153000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[152000, 153000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[152000, 153000]` SEGMENT: every zero with `152000 ≤ Im ≤ 153000` is on the line. -/
theorem segment_152000_153000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 153000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (152000:ℝ) ≤ ρ.im → ρ.im ≤ 153000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 152000 153000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_153000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 153000 via the HEIGHT CHAIN**: `[0,152000]` ∘ `[152000,153000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_153000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 153000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 153000 → ρ.re = 1 / 2 := by
  have hγ152000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 152000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 152000 153000
    (AllZeros_h152000.all_nontrivial_zeros_up_to_height_152000_of_bands
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
      hγ152000)
    (segment_152000_153000 hbands hγ)

end AllZeros_h153000

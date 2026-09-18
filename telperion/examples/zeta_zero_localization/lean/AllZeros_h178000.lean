/-  Height-chain step: all nontrivial zeta zeros up to height 178000 on Re = 1/2 --
    `AllZeros_h177000` + a `[177000, 178000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h177000
import RHInBoxT_1d4000000_3999999d4000000_177000_177026
import RHInBoxT_1d4000000_3999999d4000000_177026_177051
import RHInBoxT_1d4000000_3999999d4000000_177051_708309d4
import RHInBoxT_1d4000000_3999999d4000000_177077_177103
import RHInBoxT_1d4000000_3999999d4000000_177103_177128
import RHInBoxT_1d4000000_3999999d4000000_354255d2_177154
import RHInBoxT_1d4000000_3999999d4000000_177154_177179
import RHInBoxT_1d4000000_3999999d4000000_708715d4_177205
import RHInBoxT_1d4000000_3999999d4000000_177205_177231
import RHInBoxT_1d4000000_3999999d4000000_177231_177256
import RHInBoxT_1d4000000_3999999d4000000_177256_709129d4
import RHInBoxT_1d4000000_3999999d4000000_177282_177308
import RHInBoxT_1d4000000_3999999d4000000_177308_177333
import RHInBoxT_1d4000000_3999999d4000000_177333_177359
import RHInBoxT_1d4000000_3999999d4000000_177359_709541d4
import RHInBoxT_1d4000000_3999999d4000000_177385_177410
import RHInBoxT_1d4000000_3999999d4000000_177410_177436
import RHInBoxT_1d4000000_3999999d4000000_177436_709849d4
import RHInBoxT_1d4000000_3999999d4000000_177462_177487
import RHInBoxT_1d4000000_3999999d4000000_177487_177513
import RHInBoxT_1d4000000_3999999d4000000_177513_177538
import RHInBoxT_1d4000000_3999999d4000000_177538_177564
import RHInBoxT_1d4000000_3999999d4000000_177564_177590
import RHInBoxT_1d4000000_3999999d4000000_177590_177615
import RHInBoxT_1d4000000_3999999d4000000_177615_177641
import RHInBoxT_1d4000000_3999999d4000000_177641_710669d4
import RHInBoxT_1d4000000_3999999d4000000_177667_177692
import RHInBoxT_1d4000000_3999999d4000000_177692_177718
import RHInBoxT_1d4000000_3999999d4000000_177718_177744
import RHInBoxT_1d4000000_3999999d4000000_177744_177769
import RHInBoxT_1d4000000_3999999d4000000_177769_177795
import RHInBoxT_1d4000000_3999999d4000000_177795_177821
import RHInBoxT_1d4000000_3999999d4000000_177821_177846
import RHInBoxT_1d4000000_3999999d4000000_177846_177872
import RHInBoxT_1d4000000_3999999d4000000_177872_177897
import RHInBoxT_1d4000000_3999999d4000000_177897_177923
import RHInBoxT_1d4000000_3999999d4000000_177923_177949
import RHInBoxT_1d4000000_3999999d4000000_177949_177974
import RHInBoxT_1d4000000_3999999d4000000_177974_178000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h178000

/-- The 39-band NOMINAL partition of `[177000, 178000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 177000
  | 1 => 177026
  | 2 => 177051
  | 3 => 177077
  | 4 => 177103
  | 5 => 177128
  | 6 => 177154
  | 7 => 177179
  | 8 => 177205
  | 9 => 177231
  | 10 => 177256
  | 11 => 177282
  | 12 => 177308
  | 13 => 177333
  | 14 => 177359
  | 15 => 177385
  | 16 => 177410
  | 17 => 177436
  | 18 => 177462
  | 19 => 177487
  | 20 => 177513
  | 21 => 177538
  | 22 => 177564
  | 23 => 177590
  | 24 => 177615
  | 25 => 177641
  | 26 => 177667
  | 27 => 177692
  | 28 => 177718
  | 29 => 177744
  | 30 => 177769
  | 31 => 177795
  | 32 => 177821
  | 33 => 177846
  | 34 => 177872
  | 35 => 177897
  | 36 => 177923
  | 37 => 177949
  | 38 => 177974
  | 39 => 178000
  | _ => 178000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((177000:ℝ)) ≤ (177026); norm_num
  · show ((177026:ℝ)) ≤ (177051); norm_num
  · show ((177051:ℝ)) ≤ (177077); norm_num
  · show ((177077:ℝ)) ≤ (177103); norm_num
  · show ((177103:ℝ)) ≤ (177128); norm_num
  · show ((177128:ℝ)) ≤ (177154); norm_num
  · show ((177154:ℝ)) ≤ (177179); norm_num
  · show ((177179:ℝ)) ≤ (177205); norm_num
  · show ((177205:ℝ)) ≤ (177231); norm_num
  · show ((177231:ℝ)) ≤ (177256); norm_num
  · show ((177256:ℝ)) ≤ (177282); norm_num
  · show ((177282:ℝ)) ≤ (177308); norm_num
  · show ((177308:ℝ)) ≤ (177333); norm_num
  · show ((177333:ℝ)) ≤ (177359); norm_num
  · show ((177359:ℝ)) ≤ (177385); norm_num
  · show ((177385:ℝ)) ≤ (177410); norm_num
  · show ((177410:ℝ)) ≤ (177436); norm_num
  · show ((177436:ℝ)) ≤ (177462); norm_num
  · show ((177462:ℝ)) ≤ (177487); norm_num
  · show ((177487:ℝ)) ≤ (177513); norm_num
  · show ((177513:ℝ)) ≤ (177538); norm_num
  · show ((177538:ℝ)) ≤ (177564); norm_num
  · show ((177564:ℝ)) ≤ (177590); norm_num
  · show ((177590:ℝ)) ≤ (177615); norm_num
  · show ((177615:ℝ)) ≤ (177641); norm_num
  · show ((177641:ℝ)) ≤ (177667); norm_num
  · show ((177667:ℝ)) ≤ (177692); norm_num
  · show ((177692:ℝ)) ≤ (177718); norm_num
  · show ((177718:ℝ)) ≤ (177744); norm_num
  · show ((177744:ℝ)) ≤ (177769); norm_num
  · show ((177769:ℝ)) ≤ (177795); norm_num
  · show ((177795:ℝ)) ≤ (177821); norm_num
  · show ((177821:ℝ)) ≤ (177846); norm_num
  · show ((177846:ℝ)) ≤ (177872); norm_num
  · show ((177872:ℝ)) ≤ (177897); norm_num
  · show ((177897:ℝ)) ≤ (177923); norm_num
  · show ((177923:ℝ)) ≤ (177949); norm_num
  · show ((177949:ℝ)) ≤ (177974); norm_num
  · show ((177974:ℝ)) ≤ (178000); norm_num
  · show ((178000:ℝ)) ≤ (178000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 177000
  | 1 => 177026
  | 2 => 177051
  | 3 => 177077
  | 4 => 177103
  | 5 => 354255 / 2
  | 6 => 177154
  | 7 => 708715 / 4
  | 8 => 177205
  | 9 => 177231
  | 10 => 177256
  | 11 => 177282
  | 12 => 177308
  | 13 => 177333
  | 14 => 177359
  | 15 => 177385
  | 16 => 177410
  | 17 => 177436
  | 18 => 177462
  | 19 => 177487
  | 20 => 177513
  | 21 => 177538
  | 22 => 177564
  | 23 => 177590
  | 24 => 177615
  | 25 => 177641
  | 26 => 177667
  | 27 => 177692
  | 28 => 177718
  | 29 => 177744
  | 30 => 177769
  | 31 => 177795
  | 32 => 177821
  | 33 => 177846
  | 34 => 177872
  | 35 => 177897
  | 36 => 177923
  | 37 => 177949
  | 38 => 177974
  | _ => 177974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 177026
  | 1 => 177051
  | 2 => 708309 / 4
  | 3 => 177103
  | 4 => 177128
  | 5 => 177154
  | 6 => 177179
  | 7 => 177205
  | 8 => 177231
  | 9 => 177256
  | 10 => 709129 / 4
  | 11 => 177308
  | 12 => 177333
  | 13 => 177359
  | 14 => 709541 / 4
  | 15 => 177410
  | 16 => 177436
  | 17 => 709849 / 4
  | 18 => 177487
  | 19 => 177513
  | 20 => 177538
  | 21 => 177564
  | 22 => 177590
  | 23 => 177615
  | 24 => 177641
  | 25 => 710669 / 4
  | 26 => 177692
  | 27 => 177718
  | 28 => 177744
  | 29 => 177769
  | 30 => 177795
  | 31 => 177821
  | 32 => 177846
  | 33 => 177872
  | 34 => 177897
  | 35 => 177923
  | 36 => 177949
  | 37 => 177974
  | 38 => 178000
  | _ => 178000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 178000` (`log 178000 ≤ 13`, `2.7^13 ≥ 178000`). -/
theorem haC_178000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 178000 := by
  have hlog : Real.log 178000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 178000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 178000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[177000, 178000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[177000, 178000]` SEGMENT: every zero with `177000 ≤ Im ≤ 178000` is on the line. -/
theorem segment_177000_178000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 178000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (177000:ℝ) ≤ ρ.im → ρ.im ≤ 178000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 177000 178000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_178000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 178000 via the HEIGHT CHAIN**: `[0,177000]` ∘ `[177000,178000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_178000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 178000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 178000 → ρ.re = 1 / 2 := by
  have hγ177000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 177000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 177000 178000
    (AllZeros_h177000.all_nontrivial_zeros_up_to_height_177000_of_bands
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
      hγ177000)
    (segment_177000_178000 hbands hγ)

end AllZeros_h178000

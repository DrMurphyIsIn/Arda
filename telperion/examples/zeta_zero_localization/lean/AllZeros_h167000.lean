/-  Height-chain step: all nontrivial zeta zeros up to height 167000 on Re = 1/2 --
    `AllZeros_h166000` + a `[166000, 167000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h166000
import RHInBoxT_1d4000000_3999999d4000000_663999d4_166026
import RHInBoxT_1d4000000_3999999d4000000_664103d4_166051
import RHInBoxT_1d4000000_3999999d4000000_166051_166077
import RHInBoxT_1d4000000_3999999d4000000_664307d4_166103
import RHInBoxT_1d4000000_3999999d4000000_166103_166128
import RHInBoxT_1d4000000_3999999d4000000_166128_166154
import RHInBoxT_1d4000000_3999999d4000000_166154_166179
import RHInBoxT_1d4000000_3999999d4000000_166179_664821d4
import RHInBoxT_1d4000000_3999999d4000000_166205_166231
import RHInBoxT_1d4000000_3999999d4000000_166231_665025d4
import RHInBoxT_1d4000000_3999999d4000000_166256_166282
import RHInBoxT_1d4000000_3999999d4000000_166282_166308
import RHInBoxT_1d4000000_3999999d4000000_166308_166333
import RHInBoxT_1d4000000_3999999d4000000_665331d4_166359
import RHInBoxT_1d4000000_3999999d4000000_665435d4_166385
import RHInBoxT_1d4000000_3999999d4000000_166385_166410
import RHInBoxT_1d4000000_3999999d4000000_166410_166436
import RHInBoxT_1d4000000_3999999d4000000_166436_166462
import RHInBoxT_1d4000000_3999999d4000000_166462_166487
import RHInBoxT_1d4000000_3999999d4000000_166487_166513
import RHInBoxT_1d4000000_3999999d4000000_166513_166538
import RHInBoxT_1d4000000_3999999d4000000_166538_166564
import RHInBoxT_1d4000000_3999999d4000000_166564_666361d4
import RHInBoxT_1d4000000_3999999d4000000_166590_166615
import RHInBoxT_1d4000000_3999999d4000000_166615_166641
import RHInBoxT_1d4000000_3999999d4000000_166641_666669d4
import RHInBoxT_1d4000000_3999999d4000000_166667_166692
import RHInBoxT_1d4000000_3999999d4000000_166692_166718
import RHInBoxT_1d4000000_3999999d4000000_666871d4_166744
import RHInBoxT_1d4000000_3999999d4000000_166744_166769
import RHInBoxT_1d4000000_3999999d4000000_166769_166795
import RHInBoxT_1d4000000_3999999d4000000_667179d4_166821
import RHInBoxT_1d4000000_3999999d4000000_166821_166846
import RHInBoxT_1d4000000_3999999d4000000_667383d4_667489d4
import RHInBoxT_1d4000000_3999999d4000000_166872_667589d4
import RHInBoxT_1d4000000_3999999d4000000_166897_166923
import RHInBoxT_1d4000000_3999999d4000000_166923_166949
import RHInBoxT_1d4000000_3999999d4000000_166949_166974
import RHInBoxT_1d4000000_3999999d4000000_166974_167000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h167000

/-- The 39-band NOMINAL partition of `[166000, 167000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 166000
  | 1 => 166026
  | 2 => 166051
  | 3 => 166077
  | 4 => 166103
  | 5 => 166128
  | 6 => 166154
  | 7 => 166179
  | 8 => 166205
  | 9 => 166231
  | 10 => 166256
  | 11 => 166282
  | 12 => 166308
  | 13 => 166333
  | 14 => 166359
  | 15 => 166385
  | 16 => 166410
  | 17 => 166436
  | 18 => 166462
  | 19 => 166487
  | 20 => 166513
  | 21 => 166538
  | 22 => 166564
  | 23 => 166590
  | 24 => 166615
  | 25 => 166641
  | 26 => 166667
  | 27 => 166692
  | 28 => 166718
  | 29 => 166744
  | 30 => 166769
  | 31 => 166795
  | 32 => 166821
  | 33 => 166846
  | 34 => 166872
  | 35 => 166897
  | 36 => 166923
  | 37 => 166949
  | 38 => 166974
  | 39 => 167000
  | _ => 167000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((166000:ℝ)) ≤ (166026); norm_num
  · show ((166026:ℝ)) ≤ (166051); norm_num
  · show ((166051:ℝ)) ≤ (166077); norm_num
  · show ((166077:ℝ)) ≤ (166103); norm_num
  · show ((166103:ℝ)) ≤ (166128); norm_num
  · show ((166128:ℝ)) ≤ (166154); norm_num
  · show ((166154:ℝ)) ≤ (166179); norm_num
  · show ((166179:ℝ)) ≤ (166205); norm_num
  · show ((166205:ℝ)) ≤ (166231); norm_num
  · show ((166231:ℝ)) ≤ (166256); norm_num
  · show ((166256:ℝ)) ≤ (166282); norm_num
  · show ((166282:ℝ)) ≤ (166308); norm_num
  · show ((166308:ℝ)) ≤ (166333); norm_num
  · show ((166333:ℝ)) ≤ (166359); norm_num
  · show ((166359:ℝ)) ≤ (166385); norm_num
  · show ((166385:ℝ)) ≤ (166410); norm_num
  · show ((166410:ℝ)) ≤ (166436); norm_num
  · show ((166436:ℝ)) ≤ (166462); norm_num
  · show ((166462:ℝ)) ≤ (166487); norm_num
  · show ((166487:ℝ)) ≤ (166513); norm_num
  · show ((166513:ℝ)) ≤ (166538); norm_num
  · show ((166538:ℝ)) ≤ (166564); norm_num
  · show ((166564:ℝ)) ≤ (166590); norm_num
  · show ((166590:ℝ)) ≤ (166615); norm_num
  · show ((166615:ℝ)) ≤ (166641); norm_num
  · show ((166641:ℝ)) ≤ (166667); norm_num
  · show ((166667:ℝ)) ≤ (166692); norm_num
  · show ((166692:ℝ)) ≤ (166718); norm_num
  · show ((166718:ℝ)) ≤ (166744); norm_num
  · show ((166744:ℝ)) ≤ (166769); norm_num
  · show ((166769:ℝ)) ≤ (166795); norm_num
  · show ((166795:ℝ)) ≤ (166821); norm_num
  · show ((166821:ℝ)) ≤ (166846); norm_num
  · show ((166846:ℝ)) ≤ (166872); norm_num
  · show ((166872:ℝ)) ≤ (166897); norm_num
  · show ((166897:ℝ)) ≤ (166923); norm_num
  · show ((166923:ℝ)) ≤ (166949); norm_num
  · show ((166949:ℝ)) ≤ (166974); norm_num
  · show ((166974:ℝ)) ≤ (167000); norm_num
  · show ((167000:ℝ)) ≤ (167000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 663999 / 4
  | 1 => 664103 / 4
  | 2 => 166051
  | 3 => 664307 / 4
  | 4 => 166103
  | 5 => 166128
  | 6 => 166154
  | 7 => 166179
  | 8 => 166205
  | 9 => 166231
  | 10 => 166256
  | 11 => 166282
  | 12 => 166308
  | 13 => 665331 / 4
  | 14 => 665435 / 4
  | 15 => 166385
  | 16 => 166410
  | 17 => 166436
  | 18 => 166462
  | 19 => 166487
  | 20 => 166513
  | 21 => 166538
  | 22 => 166564
  | 23 => 166590
  | 24 => 166615
  | 25 => 166641
  | 26 => 166667
  | 27 => 166692
  | 28 => 666871 / 4
  | 29 => 166744
  | 30 => 166769
  | 31 => 667179 / 4
  | 32 => 166821
  | 33 => 667383 / 4
  | 34 => 166872
  | 35 => 166897
  | 36 => 166923
  | 37 => 166949
  | 38 => 166974
  | _ => 166974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 166026
  | 1 => 166051
  | 2 => 166077
  | 3 => 166103
  | 4 => 166128
  | 5 => 166154
  | 6 => 166179
  | 7 => 664821 / 4
  | 8 => 166231
  | 9 => 665025 / 4
  | 10 => 166282
  | 11 => 166308
  | 12 => 166333
  | 13 => 166359
  | 14 => 166385
  | 15 => 166410
  | 16 => 166436
  | 17 => 166462
  | 18 => 166487
  | 19 => 166513
  | 20 => 166538
  | 21 => 166564
  | 22 => 666361 / 4
  | 23 => 166615
  | 24 => 166641
  | 25 => 666669 / 4
  | 26 => 166692
  | 27 => 166718
  | 28 => 166744
  | 29 => 166769
  | 30 => 166795
  | 31 => 166821
  | 32 => 166846
  | 33 => 667489 / 4
  | 34 => 667589 / 4
  | 35 => 166923
  | 36 => 166949
  | 37 => 166974
  | 38 => 167000
  | _ => 167000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 167000` (`log 167000 ≤ 13`, `2.7^13 ≥ 167000`). -/
theorem haC_167000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 167000 := by
  have hlog : Real.log 167000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 167000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 167000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[166000, 167000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[166000, 167000]` SEGMENT: every zero with `166000 ≤ Im ≤ 167000` is on the line. -/
theorem segment_166000_167000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 167000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (166000:ℝ) ≤ ρ.im → ρ.im ≤ 167000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 166000 167000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_167000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 167000 via the HEIGHT CHAIN**: `[0,166000]` ∘ `[166000,167000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_167000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 167000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 167000 → ρ.re = 1 / 2 := by
  have hγ166000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 166000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 166000 167000
    (AllZeros_h166000.all_nontrivial_zeros_up_to_height_166000_of_bands
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
      hγ166000)
    (segment_166000_167000 hbands hγ)

end AllZeros_h167000

/-  Height-chain step: all nontrivial zeta zeros up to height 147000 on Re = 1/2 --
    `AllZeros_h146000` + a `[146000, 147000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h146000
import RHInBoxT_1d4000000_3999999d4000000_146000_146026
import RHInBoxT_1d4000000_3999999d4000000_584103d4_146051
import RHInBoxT_1d4000000_3999999d4000000_146051_146077
import RHInBoxT_1d4000000_3999999d4000000_146077_146103
import RHInBoxT_1d4000000_3999999d4000000_146103_146128
import RHInBoxT_1d4000000_3999999d4000000_146128_146154
import RHInBoxT_1d4000000_3999999d4000000_146154_146179
import RHInBoxT_1d4000000_3999999d4000000_146179_146205
import RHInBoxT_1d4000000_3999999d4000000_146205_146231
import RHInBoxT_1d4000000_3999999d4000000_146231_146256
import RHInBoxT_1d4000000_3999999d4000000_146256_146282
import RHInBoxT_1d4000000_3999999d4000000_146282_585233d4
import RHInBoxT_1d4000000_3999999d4000000_146308_146333
import RHInBoxT_1d4000000_3999999d4000000_585331d4_146359
import RHInBoxT_1d4000000_3999999d4000000_146359_146385
import RHInBoxT_1d4000000_3999999d4000000_146385_585641d4
import RHInBoxT_1d4000000_3999999d4000000_146410_146436
import RHInBoxT_1d4000000_3999999d4000000_146436_585849d4
import RHInBoxT_1d4000000_3999999d4000000_146462_585949d4
import RHInBoxT_1d4000000_3999999d4000000_146487_146513
import RHInBoxT_1d4000000_3999999d4000000_146513_146538
import RHInBoxT_1d4000000_3999999d4000000_146538_146564
import RHInBoxT_1d4000000_3999999d4000000_146564_586361d4
import RHInBoxT_1d4000000_3999999d4000000_146590_586461d4
import RHInBoxT_1d4000000_3999999d4000000_146615_146641
import RHInBoxT_1d4000000_3999999d4000000_146641_146667
import RHInBoxT_1d4000000_3999999d4000000_146667_146692
import RHInBoxT_1d4000000_3999999d4000000_146692_146718
import RHInBoxT_1d4000000_3999999d4000000_146718_146744
import RHInBoxT_1d4000000_3999999d4000000_146744_146769
import RHInBoxT_1d4000000_3999999d4000000_146769_146795
import RHInBoxT_1d4000000_3999999d4000000_587179d4_146821
import RHInBoxT_1d4000000_3999999d4000000_146821_146846
import RHInBoxT_1d4000000_3999999d4000000_146846_146872
import RHInBoxT_1d4000000_3999999d4000000_146872_146897
import RHInBoxT_1d4000000_3999999d4000000_146897_146923
import RHInBoxT_1d4000000_3999999d4000000_146923_146949
import RHInBoxT_1d4000000_3999999d4000000_146949_146974
import RHInBoxT_1d4000000_3999999d4000000_146974_147000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h147000

/-- The 39-band NOMINAL partition of `[146000, 147000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 146000
  | 1 => 146026
  | 2 => 146051
  | 3 => 146077
  | 4 => 146103
  | 5 => 146128
  | 6 => 146154
  | 7 => 146179
  | 8 => 146205
  | 9 => 146231
  | 10 => 146256
  | 11 => 146282
  | 12 => 146308
  | 13 => 146333
  | 14 => 146359
  | 15 => 146385
  | 16 => 146410
  | 17 => 146436
  | 18 => 146462
  | 19 => 146487
  | 20 => 146513
  | 21 => 146538
  | 22 => 146564
  | 23 => 146590
  | 24 => 146615
  | 25 => 146641
  | 26 => 146667
  | 27 => 146692
  | 28 => 146718
  | 29 => 146744
  | 30 => 146769
  | 31 => 146795
  | 32 => 146821
  | 33 => 146846
  | 34 => 146872
  | 35 => 146897
  | 36 => 146923
  | 37 => 146949
  | 38 => 146974
  | 39 => 147000
  | _ => 147000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((146000:ℝ)) ≤ (146026); norm_num
  · show ((146026:ℝ)) ≤ (146051); norm_num
  · show ((146051:ℝ)) ≤ (146077); norm_num
  · show ((146077:ℝ)) ≤ (146103); norm_num
  · show ((146103:ℝ)) ≤ (146128); norm_num
  · show ((146128:ℝ)) ≤ (146154); norm_num
  · show ((146154:ℝ)) ≤ (146179); norm_num
  · show ((146179:ℝ)) ≤ (146205); norm_num
  · show ((146205:ℝ)) ≤ (146231); norm_num
  · show ((146231:ℝ)) ≤ (146256); norm_num
  · show ((146256:ℝ)) ≤ (146282); norm_num
  · show ((146282:ℝ)) ≤ (146308); norm_num
  · show ((146308:ℝ)) ≤ (146333); norm_num
  · show ((146333:ℝ)) ≤ (146359); norm_num
  · show ((146359:ℝ)) ≤ (146385); norm_num
  · show ((146385:ℝ)) ≤ (146410); norm_num
  · show ((146410:ℝ)) ≤ (146436); norm_num
  · show ((146436:ℝ)) ≤ (146462); norm_num
  · show ((146462:ℝ)) ≤ (146487); norm_num
  · show ((146487:ℝ)) ≤ (146513); norm_num
  · show ((146513:ℝ)) ≤ (146538); norm_num
  · show ((146538:ℝ)) ≤ (146564); norm_num
  · show ((146564:ℝ)) ≤ (146590); norm_num
  · show ((146590:ℝ)) ≤ (146615); norm_num
  · show ((146615:ℝ)) ≤ (146641); norm_num
  · show ((146641:ℝ)) ≤ (146667); norm_num
  · show ((146667:ℝ)) ≤ (146692); norm_num
  · show ((146692:ℝ)) ≤ (146718); norm_num
  · show ((146718:ℝ)) ≤ (146744); norm_num
  · show ((146744:ℝ)) ≤ (146769); norm_num
  · show ((146769:ℝ)) ≤ (146795); norm_num
  · show ((146795:ℝ)) ≤ (146821); norm_num
  · show ((146821:ℝ)) ≤ (146846); norm_num
  · show ((146846:ℝ)) ≤ (146872); norm_num
  · show ((146872:ℝ)) ≤ (146897); norm_num
  · show ((146897:ℝ)) ≤ (146923); norm_num
  · show ((146923:ℝ)) ≤ (146949); norm_num
  · show ((146949:ℝ)) ≤ (146974); norm_num
  · show ((146974:ℝ)) ≤ (147000); norm_num
  · show ((147000:ℝ)) ≤ (147000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 146000
  | 1 => 584103 / 4
  | 2 => 146051
  | 3 => 146077
  | 4 => 146103
  | 5 => 146128
  | 6 => 146154
  | 7 => 146179
  | 8 => 146205
  | 9 => 146231
  | 10 => 146256
  | 11 => 146282
  | 12 => 146308
  | 13 => 585331 / 4
  | 14 => 146359
  | 15 => 146385
  | 16 => 146410
  | 17 => 146436
  | 18 => 146462
  | 19 => 146487
  | 20 => 146513
  | 21 => 146538
  | 22 => 146564
  | 23 => 146590
  | 24 => 146615
  | 25 => 146641
  | 26 => 146667
  | 27 => 146692
  | 28 => 146718
  | 29 => 146744
  | 30 => 146769
  | 31 => 587179 / 4
  | 32 => 146821
  | 33 => 146846
  | 34 => 146872
  | 35 => 146897
  | 36 => 146923
  | 37 => 146949
  | 38 => 146974
  | _ => 146974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 146026
  | 1 => 146051
  | 2 => 146077
  | 3 => 146103
  | 4 => 146128
  | 5 => 146154
  | 6 => 146179
  | 7 => 146205
  | 8 => 146231
  | 9 => 146256
  | 10 => 146282
  | 11 => 585233 / 4
  | 12 => 146333
  | 13 => 146359
  | 14 => 146385
  | 15 => 585641 / 4
  | 16 => 146436
  | 17 => 585849 / 4
  | 18 => 585949 / 4
  | 19 => 146513
  | 20 => 146538
  | 21 => 146564
  | 22 => 586361 / 4
  | 23 => 586461 / 4
  | 24 => 146641
  | 25 => 146667
  | 26 => 146692
  | 27 => 146718
  | 28 => 146744
  | 29 => 146769
  | 30 => 146795
  | 31 => 146821
  | 32 => 146846
  | 33 => 146872
  | 34 => 146897
  | 35 => 146923
  | 36 => 146949
  | 37 => 146974
  | 38 => 147000
  | _ => 147000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 147000` (`log 147000 ≤ 12`, `2.7^12 ≥ 147000`). -/
theorem haC_147000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 147000 := by
  have hlog : Real.log 147000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 147000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 147000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[146000, 147000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[146000, 147000]` SEGMENT: every zero with `146000 ≤ Im ≤ 147000` is on the line. -/
theorem segment_146000_147000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 147000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (146000:ℝ) ≤ ρ.im → ρ.im ≤ 147000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 146000 147000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_147000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 147000 via the HEIGHT CHAIN**: `[0,146000]` ∘ `[146000,147000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_147000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 147000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 147000 → ρ.re = 1 / 2 := by
  have hγ146000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 146000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 146000 147000
    (AllZeros_h146000.all_nontrivial_zeros_up_to_height_146000_of_bands
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
      hγ146000)
    (segment_146000_147000 hbands hγ)

end AllZeros_h147000

/-  Height-chain step: all nontrivial zeta zeros up to height 184000 on Re = 1/2 --
    `AllZeros_h183000` + a `[183000, 184000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h183000
import RHInBoxT_1d4000000_3999999d4000000_183000_183026
import RHInBoxT_1d4000000_3999999d4000000_183026_183051
import RHInBoxT_1d4000000_3999999d4000000_183051_183077
import RHInBoxT_1d4000000_3999999d4000000_183077_183103
import RHInBoxT_1d4000000_3999999d4000000_183103_183128
import RHInBoxT_1d4000000_3999999d4000000_183128_183154
import RHInBoxT_1d4000000_3999999d4000000_183154_183179
import RHInBoxT_1d4000000_3999999d4000000_183179_183205
import RHInBoxT_1d4000000_3999999d4000000_732819d4_183231
import RHInBoxT_1d4000000_3999999d4000000_183231_183256
import RHInBoxT_1d4000000_3999999d4000000_183256_183282
import RHInBoxT_1d4000000_3999999d4000000_183282_183308
import RHInBoxT_1d4000000_3999999d4000000_183308_183333
import RHInBoxT_1d4000000_3999999d4000000_183333_183359
import RHInBoxT_1d4000000_3999999d4000000_183359_183385
import RHInBoxT_1d4000000_3999999d4000000_733539d4_183410
import RHInBoxT_1d4000000_3999999d4000000_183410_183436
import RHInBoxT_1d4000000_3999999d4000000_183436_183462
import RHInBoxT_1d4000000_3999999d4000000_733847d4_183487
import RHInBoxT_1d4000000_3999999d4000000_183487_183513
import RHInBoxT_1d4000000_3999999d4000000_734051d4_183538
import RHInBoxT_1d4000000_3999999d4000000_183538_734257d4
import RHInBoxT_1d4000000_3999999d4000000_183564_734361d4
import RHInBoxT_1d4000000_3999999d4000000_183590_183615
import RHInBoxT_1d4000000_3999999d4000000_183615_183641
import RHInBoxT_1d4000000_3999999d4000000_183641_183667
import RHInBoxT_1d4000000_3999999d4000000_183667_183692
import RHInBoxT_1d4000000_3999999d4000000_183692_183718
import RHInBoxT_1d4000000_3999999d4000000_183718_183744
import RHInBoxT_1d4000000_3999999d4000000_183744_183769
import RHInBoxT_1d4000000_3999999d4000000_183769_183795
import RHInBoxT_1d4000000_3999999d4000000_183795_183821
import RHInBoxT_1d4000000_3999999d4000000_183821_367693d2
import RHInBoxT_1d4000000_3999999d4000000_183846_735489d4
import RHInBoxT_1d4000000_3999999d4000000_183872_183897
import RHInBoxT_1d4000000_3999999d4000000_183897_735693d4
import RHInBoxT_1d4000000_3999999d4000000_183923_183949
import RHInBoxT_1d4000000_3999999d4000000_183949_183974
import RHInBoxT_1d4000000_3999999d4000000_183974_184000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h184000

/-- The 39-band NOMINAL partition of `[183000, 184000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 183000
  | 1 => 183026
  | 2 => 183051
  | 3 => 183077
  | 4 => 183103
  | 5 => 183128
  | 6 => 183154
  | 7 => 183179
  | 8 => 183205
  | 9 => 183231
  | 10 => 183256
  | 11 => 183282
  | 12 => 183308
  | 13 => 183333
  | 14 => 183359
  | 15 => 183385
  | 16 => 183410
  | 17 => 183436
  | 18 => 183462
  | 19 => 183487
  | 20 => 183513
  | 21 => 183538
  | 22 => 183564
  | 23 => 183590
  | 24 => 183615
  | 25 => 183641
  | 26 => 183667
  | 27 => 183692
  | 28 => 183718
  | 29 => 183744
  | 30 => 183769
  | 31 => 183795
  | 32 => 183821
  | 33 => 183846
  | 34 => 183872
  | 35 => 183897
  | 36 => 183923
  | 37 => 183949
  | 38 => 183974
  | 39 => 184000
  | _ => 184000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((183000:ℝ)) ≤ (183026); norm_num
  · show ((183026:ℝ)) ≤ (183051); norm_num
  · show ((183051:ℝ)) ≤ (183077); norm_num
  · show ((183077:ℝ)) ≤ (183103); norm_num
  · show ((183103:ℝ)) ≤ (183128); norm_num
  · show ((183128:ℝ)) ≤ (183154); norm_num
  · show ((183154:ℝ)) ≤ (183179); norm_num
  · show ((183179:ℝ)) ≤ (183205); norm_num
  · show ((183205:ℝ)) ≤ (183231); norm_num
  · show ((183231:ℝ)) ≤ (183256); norm_num
  · show ((183256:ℝ)) ≤ (183282); norm_num
  · show ((183282:ℝ)) ≤ (183308); norm_num
  · show ((183308:ℝ)) ≤ (183333); norm_num
  · show ((183333:ℝ)) ≤ (183359); norm_num
  · show ((183359:ℝ)) ≤ (183385); norm_num
  · show ((183385:ℝ)) ≤ (183410); norm_num
  · show ((183410:ℝ)) ≤ (183436); norm_num
  · show ((183436:ℝ)) ≤ (183462); norm_num
  · show ((183462:ℝ)) ≤ (183487); norm_num
  · show ((183487:ℝ)) ≤ (183513); norm_num
  · show ((183513:ℝ)) ≤ (183538); norm_num
  · show ((183538:ℝ)) ≤ (183564); norm_num
  · show ((183564:ℝ)) ≤ (183590); norm_num
  · show ((183590:ℝ)) ≤ (183615); norm_num
  · show ((183615:ℝ)) ≤ (183641); norm_num
  · show ((183641:ℝ)) ≤ (183667); norm_num
  · show ((183667:ℝ)) ≤ (183692); norm_num
  · show ((183692:ℝ)) ≤ (183718); norm_num
  · show ((183718:ℝ)) ≤ (183744); norm_num
  · show ((183744:ℝ)) ≤ (183769); norm_num
  · show ((183769:ℝ)) ≤ (183795); norm_num
  · show ((183795:ℝ)) ≤ (183821); norm_num
  · show ((183821:ℝ)) ≤ (183846); norm_num
  · show ((183846:ℝ)) ≤ (183872); norm_num
  · show ((183872:ℝ)) ≤ (183897); norm_num
  · show ((183897:ℝ)) ≤ (183923); norm_num
  · show ((183923:ℝ)) ≤ (183949); norm_num
  · show ((183949:ℝ)) ≤ (183974); norm_num
  · show ((183974:ℝ)) ≤ (184000); norm_num
  · show ((184000:ℝ)) ≤ (184000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 183000
  | 1 => 183026
  | 2 => 183051
  | 3 => 183077
  | 4 => 183103
  | 5 => 183128
  | 6 => 183154
  | 7 => 183179
  | 8 => 732819 / 4
  | 9 => 183231
  | 10 => 183256
  | 11 => 183282
  | 12 => 183308
  | 13 => 183333
  | 14 => 183359
  | 15 => 733539 / 4
  | 16 => 183410
  | 17 => 183436
  | 18 => 733847 / 4
  | 19 => 183487
  | 20 => 734051 / 4
  | 21 => 183538
  | 22 => 183564
  | 23 => 183590
  | 24 => 183615
  | 25 => 183641
  | 26 => 183667
  | 27 => 183692
  | 28 => 183718
  | 29 => 183744
  | 30 => 183769
  | 31 => 183795
  | 32 => 183821
  | 33 => 183846
  | 34 => 183872
  | 35 => 183897
  | 36 => 183923
  | 37 => 183949
  | 38 => 183974
  | _ => 183974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 183026
  | 1 => 183051
  | 2 => 183077
  | 3 => 183103
  | 4 => 183128
  | 5 => 183154
  | 6 => 183179
  | 7 => 183205
  | 8 => 183231
  | 9 => 183256
  | 10 => 183282
  | 11 => 183308
  | 12 => 183333
  | 13 => 183359
  | 14 => 183385
  | 15 => 183410
  | 16 => 183436
  | 17 => 183462
  | 18 => 183487
  | 19 => 183513
  | 20 => 183538
  | 21 => 734257 / 4
  | 22 => 734361 / 4
  | 23 => 183615
  | 24 => 183641
  | 25 => 183667
  | 26 => 183692
  | 27 => 183718
  | 28 => 183744
  | 29 => 183769
  | 30 => 183795
  | 31 => 183821
  | 32 => 367693 / 2
  | 33 => 735489 / 4
  | 34 => 183897
  | 35 => 735693 / 4
  | 36 => 183949
  | 37 => 183974
  | 38 => 184000
  | _ => 184000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 184000` (`log 184000 ≤ 13`, `2.7^13 ≥ 184000`). -/
theorem haC_184000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 184000 := by
  have hlog : Real.log 184000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 184000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 184000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[183000, 184000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[183000, 184000]` SEGMENT: every zero with `183000 ≤ Im ≤ 184000` is on the line. -/
theorem segment_183000_184000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 184000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (183000:ℝ) ≤ ρ.im → ρ.im ≤ 184000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 183000 184000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_184000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 184000 via the HEIGHT CHAIN**: `[0,183000]` ∘ `[183000,184000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_184000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 184000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 184000 → ρ.re = 1 / 2 := by
  have hγ183000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 183000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 183000 184000
    (AllZeros_h183000.all_nontrivial_zeros_up_to_height_183000_of_bands
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
      hγ183000)
    (segment_183000_184000 hbands hγ)

end AllZeros_h184000

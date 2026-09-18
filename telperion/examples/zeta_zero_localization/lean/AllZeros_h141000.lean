/-  Height-chain step: all nontrivial zeta zeros up to height 141000 on Re = 1/2 --
    `AllZeros_h140000` + a `[140000, 141000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h140000
import RHInBoxT_1d4000000_3999999d4000000_140000_140026
import RHInBoxT_1d4000000_3999999d4000000_140026_140051
import RHInBoxT_1d4000000_3999999d4000000_140051_560309d4
import RHInBoxT_1d4000000_3999999d4000000_140077_560413d4
import RHInBoxT_1d4000000_3999999d4000000_140103_140128
import RHInBoxT_1d4000000_3999999d4000000_140128_140154
import RHInBoxT_1d4000000_3999999d4000000_140154_140179
import RHInBoxT_1d4000000_3999999d4000000_140179_140205
import RHInBoxT_1d4000000_3999999d4000000_140205_140231
import RHInBoxT_1d4000000_3999999d4000000_560923d4_140256
import RHInBoxT_1d4000000_3999999d4000000_140256_140282
import RHInBoxT_1d4000000_3999999d4000000_140282_140308
import RHInBoxT_1d4000000_3999999d4000000_140308_280667d2
import RHInBoxT_1d4000000_3999999d4000000_140333_140359
import RHInBoxT_1d4000000_3999999d4000000_140359_140385
import RHInBoxT_1d4000000_3999999d4000000_140385_140410
import RHInBoxT_1d4000000_3999999d4000000_561639d4_140436
import RHInBoxT_1d4000000_3999999d4000000_140436_140462
import RHInBoxT_1d4000000_3999999d4000000_140462_140487
import RHInBoxT_1d4000000_3999999d4000000_140487_140513
import RHInBoxT_1d4000000_3999999d4000000_140513_140538
import RHInBoxT_1d4000000_3999999d4000000_140538_140564
import RHInBoxT_1d4000000_3999999d4000000_140564_140590
import RHInBoxT_1d4000000_3999999d4000000_140590_140615
import RHInBoxT_1d4000000_3999999d4000000_140615_562565d4
import RHInBoxT_1d4000000_3999999d4000000_140641_140667
import RHInBoxT_1d4000000_3999999d4000000_140667_140692
import RHInBoxT_1d4000000_3999999d4000000_140692_140718
import RHInBoxT_1d4000000_3999999d4000000_140718_140744
import RHInBoxT_1d4000000_3999999d4000000_140744_140769
import RHInBoxT_1d4000000_3999999d4000000_140769_140795
import RHInBoxT_1d4000000_3999999d4000000_140795_140821
import RHInBoxT_1d4000000_3999999d4000000_140821_140846
import RHInBoxT_1d4000000_3999999d4000000_563383d4_563489d4
import RHInBoxT_1d4000000_3999999d4000000_140872_140897
import RHInBoxT_1d4000000_3999999d4000000_140897_281847d2
import RHInBoxT_1d4000000_3999999d4000000_140923_140949
import RHInBoxT_1d4000000_3999999d4000000_563795d4_140974
import RHInBoxT_1d4000000_3999999d4000000_140974_141000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h141000

/-- The 39-band NOMINAL partition of `[140000, 141000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 140000
  | 1 => 140026
  | 2 => 140051
  | 3 => 140077
  | 4 => 140103
  | 5 => 140128
  | 6 => 140154
  | 7 => 140179
  | 8 => 140205
  | 9 => 140231
  | 10 => 140256
  | 11 => 140282
  | 12 => 140308
  | 13 => 140333
  | 14 => 140359
  | 15 => 140385
  | 16 => 140410
  | 17 => 140436
  | 18 => 140462
  | 19 => 140487
  | 20 => 140513
  | 21 => 140538
  | 22 => 140564
  | 23 => 140590
  | 24 => 140615
  | 25 => 140641
  | 26 => 140667
  | 27 => 140692
  | 28 => 140718
  | 29 => 140744
  | 30 => 140769
  | 31 => 140795
  | 32 => 140821
  | 33 => 140846
  | 34 => 140872
  | 35 => 140897
  | 36 => 140923
  | 37 => 140949
  | 38 => 140974
  | 39 => 141000
  | _ => 141000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((140000:ℝ)) ≤ (140026); norm_num
  · show ((140026:ℝ)) ≤ (140051); norm_num
  · show ((140051:ℝ)) ≤ (140077); norm_num
  · show ((140077:ℝ)) ≤ (140103); norm_num
  · show ((140103:ℝ)) ≤ (140128); norm_num
  · show ((140128:ℝ)) ≤ (140154); norm_num
  · show ((140154:ℝ)) ≤ (140179); norm_num
  · show ((140179:ℝ)) ≤ (140205); norm_num
  · show ((140205:ℝ)) ≤ (140231); norm_num
  · show ((140231:ℝ)) ≤ (140256); norm_num
  · show ((140256:ℝ)) ≤ (140282); norm_num
  · show ((140282:ℝ)) ≤ (140308); norm_num
  · show ((140308:ℝ)) ≤ (140333); norm_num
  · show ((140333:ℝ)) ≤ (140359); norm_num
  · show ((140359:ℝ)) ≤ (140385); norm_num
  · show ((140385:ℝ)) ≤ (140410); norm_num
  · show ((140410:ℝ)) ≤ (140436); norm_num
  · show ((140436:ℝ)) ≤ (140462); norm_num
  · show ((140462:ℝ)) ≤ (140487); norm_num
  · show ((140487:ℝ)) ≤ (140513); norm_num
  · show ((140513:ℝ)) ≤ (140538); norm_num
  · show ((140538:ℝ)) ≤ (140564); norm_num
  · show ((140564:ℝ)) ≤ (140590); norm_num
  · show ((140590:ℝ)) ≤ (140615); norm_num
  · show ((140615:ℝ)) ≤ (140641); norm_num
  · show ((140641:ℝ)) ≤ (140667); norm_num
  · show ((140667:ℝ)) ≤ (140692); norm_num
  · show ((140692:ℝ)) ≤ (140718); norm_num
  · show ((140718:ℝ)) ≤ (140744); norm_num
  · show ((140744:ℝ)) ≤ (140769); norm_num
  · show ((140769:ℝ)) ≤ (140795); norm_num
  · show ((140795:ℝ)) ≤ (140821); norm_num
  · show ((140821:ℝ)) ≤ (140846); norm_num
  · show ((140846:ℝ)) ≤ (140872); norm_num
  · show ((140872:ℝ)) ≤ (140897); norm_num
  · show ((140897:ℝ)) ≤ (140923); norm_num
  · show ((140923:ℝ)) ≤ (140949); norm_num
  · show ((140949:ℝ)) ≤ (140974); norm_num
  · show ((140974:ℝ)) ≤ (141000); norm_num
  · show ((141000:ℝ)) ≤ (141000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 140000
  | 1 => 140026
  | 2 => 140051
  | 3 => 140077
  | 4 => 140103
  | 5 => 140128
  | 6 => 140154
  | 7 => 140179
  | 8 => 140205
  | 9 => 560923 / 4
  | 10 => 140256
  | 11 => 140282
  | 12 => 140308
  | 13 => 140333
  | 14 => 140359
  | 15 => 140385
  | 16 => 561639 / 4
  | 17 => 140436
  | 18 => 140462
  | 19 => 140487
  | 20 => 140513
  | 21 => 140538
  | 22 => 140564
  | 23 => 140590
  | 24 => 140615
  | 25 => 140641
  | 26 => 140667
  | 27 => 140692
  | 28 => 140718
  | 29 => 140744
  | 30 => 140769
  | 31 => 140795
  | 32 => 140821
  | 33 => 563383 / 4
  | 34 => 140872
  | 35 => 140897
  | 36 => 140923
  | 37 => 563795 / 4
  | 38 => 140974
  | _ => 140974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 140026
  | 1 => 140051
  | 2 => 560309 / 4
  | 3 => 560413 / 4
  | 4 => 140128
  | 5 => 140154
  | 6 => 140179
  | 7 => 140205
  | 8 => 140231
  | 9 => 140256
  | 10 => 140282
  | 11 => 140308
  | 12 => 280667 / 2
  | 13 => 140359
  | 14 => 140385
  | 15 => 140410
  | 16 => 140436
  | 17 => 140462
  | 18 => 140487
  | 19 => 140513
  | 20 => 140538
  | 21 => 140564
  | 22 => 140590
  | 23 => 140615
  | 24 => 562565 / 4
  | 25 => 140667
  | 26 => 140692
  | 27 => 140718
  | 28 => 140744
  | 29 => 140769
  | 30 => 140795
  | 31 => 140821
  | 32 => 140846
  | 33 => 563489 / 4
  | 34 => 140897
  | 35 => 281847 / 2
  | 36 => 140949
  | 37 => 140974
  | 38 => 141000
  | _ => 141000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 141000` (`log 141000 ≤ 12`, `2.7^12 ≥ 141000`). -/
theorem haC_141000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 141000 := by
  have hlog : Real.log 141000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 141000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 141000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[140000, 141000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[140000, 141000]` SEGMENT: every zero with `140000 ≤ Im ≤ 141000` is on the line. -/
theorem segment_140000_141000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 141000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (140000:ℝ) ≤ ρ.im → ρ.im ≤ 141000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 140000 141000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_141000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 141000 via the HEIGHT CHAIN**: `[0,140000]` ∘ `[140000,141000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_141000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 141000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 141000 → ρ.re = 1 / 2 := by
  have hγ140000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 140000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 140000 141000
    (AllZeros_h140000.all_nontrivial_zeros_up_to_height_140000_of_bands
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
      hγ140000)
    (segment_140000_141000 hbands hγ)

end AllZeros_h141000

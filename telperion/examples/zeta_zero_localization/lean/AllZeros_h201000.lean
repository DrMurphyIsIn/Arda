/-  Height-chain step: all nontrivial zeta zeros up to height 201000 on Re = 1/2 --
    `AllZeros_h200000` + a `[200000, 201000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h200000
import RHInBoxT_1d4000000_3999999d4000000_200000_800105d4
import RHInBoxT_1d4000000_3999999d4000000_200026_200051
import RHInBoxT_1d4000000_3999999d4000000_200051_800309d4
import RHInBoxT_1d4000000_3999999d4000000_200077_200103
import RHInBoxT_1d4000000_3999999d4000000_200103_200128
import RHInBoxT_1d4000000_3999999d4000000_200128_800617d4
import RHInBoxT_1d4000000_3999999d4000000_200154_200179
import RHInBoxT_1d4000000_3999999d4000000_200179_800821d4
import RHInBoxT_1d4000000_3999999d4000000_200205_200231
import RHInBoxT_1d4000000_3999999d4000000_800923d4_801025d4
import RHInBoxT_1d4000000_3999999d4000000_200256_200282
import RHInBoxT_1d4000000_3999999d4000000_200282_200308
import RHInBoxT_1d4000000_3999999d4000000_200308_200333
import RHInBoxT_1d4000000_3999999d4000000_801331d4_200359
import RHInBoxT_1d4000000_3999999d4000000_200359_200385
import RHInBoxT_1d4000000_3999999d4000000_200385_801641d4
import RHInBoxT_1d4000000_3999999d4000000_200410_200436
import RHInBoxT_1d4000000_3999999d4000000_801743d4_200462
import RHInBoxT_1d4000000_3999999d4000000_200462_200487
import RHInBoxT_1d4000000_3999999d4000000_200487_200513
import RHInBoxT_1d4000000_3999999d4000000_200513_200538
import RHInBoxT_1d4000000_3999999d4000000_200538_200564
import RHInBoxT_1d4000000_3999999d4000000_200564_802361d4
import RHInBoxT_1d4000000_3999999d4000000_200590_200615
import RHInBoxT_1d4000000_3999999d4000000_802459d4_200641
import RHInBoxT_1d4000000_3999999d4000000_200641_200667
import RHInBoxT_1d4000000_3999999d4000000_200667_200692
import RHInBoxT_1d4000000_3999999d4000000_200692_200718
import RHInBoxT_1d4000000_3999999d4000000_200718_200744
import RHInBoxT_1d4000000_3999999d4000000_200744_200769
import RHInBoxT_1d4000000_3999999d4000000_200769_803181d4
import RHInBoxT_1d4000000_3999999d4000000_200795_200821
import RHInBoxT_1d4000000_3999999d4000000_200821_200846
import RHInBoxT_1d4000000_3999999d4000000_200846_200872
import RHInBoxT_1d4000000_3999999d4000000_200872_200897
import RHInBoxT_1d4000000_3999999d4000000_200897_200923
import RHInBoxT_1d4000000_3999999d4000000_200923_200949
import RHInBoxT_1d4000000_3999999d4000000_200949_200974
import RHInBoxT_1d4000000_3999999d4000000_200974_201000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h201000

/-- The 39-band NOMINAL partition of `[200000, 201000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 200000
  | 1 => 200026
  | 2 => 200051
  | 3 => 200077
  | 4 => 200103
  | 5 => 200128
  | 6 => 200154
  | 7 => 200179
  | 8 => 200205
  | 9 => 200231
  | 10 => 200256
  | 11 => 200282
  | 12 => 200308
  | 13 => 200333
  | 14 => 200359
  | 15 => 200385
  | 16 => 200410
  | 17 => 200436
  | 18 => 200462
  | 19 => 200487
  | 20 => 200513
  | 21 => 200538
  | 22 => 200564
  | 23 => 200590
  | 24 => 200615
  | 25 => 200641
  | 26 => 200667
  | 27 => 200692
  | 28 => 200718
  | 29 => 200744
  | 30 => 200769
  | 31 => 200795
  | 32 => 200821
  | 33 => 200846
  | 34 => 200872
  | 35 => 200897
  | 36 => 200923
  | 37 => 200949
  | 38 => 200974
  | 39 => 201000
  | _ => 201000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((200000:ℝ)) ≤ (200026); norm_num
  · show ((200026:ℝ)) ≤ (200051); norm_num
  · show ((200051:ℝ)) ≤ (200077); norm_num
  · show ((200077:ℝ)) ≤ (200103); norm_num
  · show ((200103:ℝ)) ≤ (200128); norm_num
  · show ((200128:ℝ)) ≤ (200154); norm_num
  · show ((200154:ℝ)) ≤ (200179); norm_num
  · show ((200179:ℝ)) ≤ (200205); norm_num
  · show ((200205:ℝ)) ≤ (200231); norm_num
  · show ((200231:ℝ)) ≤ (200256); norm_num
  · show ((200256:ℝ)) ≤ (200282); norm_num
  · show ((200282:ℝ)) ≤ (200308); norm_num
  · show ((200308:ℝ)) ≤ (200333); norm_num
  · show ((200333:ℝ)) ≤ (200359); norm_num
  · show ((200359:ℝ)) ≤ (200385); norm_num
  · show ((200385:ℝ)) ≤ (200410); norm_num
  · show ((200410:ℝ)) ≤ (200436); norm_num
  · show ((200436:ℝ)) ≤ (200462); norm_num
  · show ((200462:ℝ)) ≤ (200487); norm_num
  · show ((200487:ℝ)) ≤ (200513); norm_num
  · show ((200513:ℝ)) ≤ (200538); norm_num
  · show ((200538:ℝ)) ≤ (200564); norm_num
  · show ((200564:ℝ)) ≤ (200590); norm_num
  · show ((200590:ℝ)) ≤ (200615); norm_num
  · show ((200615:ℝ)) ≤ (200641); norm_num
  · show ((200641:ℝ)) ≤ (200667); norm_num
  · show ((200667:ℝ)) ≤ (200692); norm_num
  · show ((200692:ℝ)) ≤ (200718); norm_num
  · show ((200718:ℝ)) ≤ (200744); norm_num
  · show ((200744:ℝ)) ≤ (200769); norm_num
  · show ((200769:ℝ)) ≤ (200795); norm_num
  · show ((200795:ℝ)) ≤ (200821); norm_num
  · show ((200821:ℝ)) ≤ (200846); norm_num
  · show ((200846:ℝ)) ≤ (200872); norm_num
  · show ((200872:ℝ)) ≤ (200897); norm_num
  · show ((200897:ℝ)) ≤ (200923); norm_num
  · show ((200923:ℝ)) ≤ (200949); norm_num
  · show ((200949:ℝ)) ≤ (200974); norm_num
  · show ((200974:ℝ)) ≤ (201000); norm_num
  · show ((201000:ℝ)) ≤ (201000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 200000
  | 1 => 200026
  | 2 => 200051
  | 3 => 200077
  | 4 => 200103
  | 5 => 200128
  | 6 => 200154
  | 7 => 200179
  | 8 => 200205
  | 9 => 800923 / 4
  | 10 => 200256
  | 11 => 200282
  | 12 => 200308
  | 13 => 801331 / 4
  | 14 => 200359
  | 15 => 200385
  | 16 => 200410
  | 17 => 801743 / 4
  | 18 => 200462
  | 19 => 200487
  | 20 => 200513
  | 21 => 200538
  | 22 => 200564
  | 23 => 200590
  | 24 => 802459 / 4
  | 25 => 200641
  | 26 => 200667
  | 27 => 200692
  | 28 => 200718
  | 29 => 200744
  | 30 => 200769
  | 31 => 200795
  | 32 => 200821
  | 33 => 200846
  | 34 => 200872
  | 35 => 200897
  | 36 => 200923
  | 37 => 200949
  | 38 => 200974
  | _ => 200974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 800105 / 4
  | 1 => 200051
  | 2 => 800309 / 4
  | 3 => 200103
  | 4 => 200128
  | 5 => 800617 / 4
  | 6 => 200179
  | 7 => 800821 / 4
  | 8 => 200231
  | 9 => 801025 / 4
  | 10 => 200282
  | 11 => 200308
  | 12 => 200333
  | 13 => 200359
  | 14 => 200385
  | 15 => 801641 / 4
  | 16 => 200436
  | 17 => 200462
  | 18 => 200487
  | 19 => 200513
  | 20 => 200538
  | 21 => 200564
  | 22 => 802361 / 4
  | 23 => 200615
  | 24 => 200641
  | 25 => 200667
  | 26 => 200692
  | 27 => 200718
  | 28 => 200744
  | 29 => 200769
  | 30 => 803181 / 4
  | 31 => 200821
  | 32 => 200846
  | 33 => 200872
  | 34 => 200897
  | 35 => 200923
  | 36 => 200949
  | 37 => 200974
  | 38 => 201000
  | _ => 201000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 201000` (`log 201000 ≤ 13`, `2.7^13 ≥ 201000`). -/
theorem haC_201000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 201000 := by
  have hlog : Real.log 201000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 201000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 201000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[200000, 201000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[200000, 201000]` SEGMENT: every zero with `200000 ≤ Im ≤ 201000` is on the line. -/
theorem segment_200000_201000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 201000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (200000:ℝ) ≤ ρ.im → ρ.im ≤ 201000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 200000 201000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_201000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 201000 via the HEIGHT CHAIN**: `[0,200000]` ∘ `[200000,201000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_201000_of_bands
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
    (hbands_188000 : AllZeros_h188000.BandHyp)
    (hbands_189000 : AllZeros_h189000.BandHyp)
    (hbands_190000 : AllZeros_h190000.BandHyp)
    (hbands_191000 : AllZeros_h191000.BandHyp)
    (hbands_192000 : AllZeros_h192000.BandHyp)
    (hbands_193000 : AllZeros_h193000.BandHyp)
    (hbands_194000 : AllZeros_h194000.BandHyp)
    (hbands_195000 : AllZeros_h195000.BandHyp)
    (hbands_196000 : AllZeros_h196000.BandHyp)
    (hbands_197000 : AllZeros_h197000.BandHyp)
    (hbands_198000 : AllZeros_h198000.BandHyp)
    (hbands_199000 : AllZeros_h199000.BandHyp)
    (hbands_200000 : AllZeros_h200000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 201000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 201000 → ρ.re = 1 / 2 := by
  have hγ200000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 200000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 200000 201000
    (AllZeros_h200000.all_nontrivial_zeros_up_to_height_200000_of_bands
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
      hbands_188000
      hbands_189000
      hbands_190000
      hbands_191000
      hbands_192000
      hbands_193000
      hbands_194000
      hbands_195000
      hbands_196000
      hbands_197000
      hbands_198000
      hbands_199000
      hbands_200000
      hγ200000)
    (segment_200000_201000 hbands hγ)

end AllZeros_h201000

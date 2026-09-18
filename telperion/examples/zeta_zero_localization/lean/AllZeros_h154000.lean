/-  Height-chain step: all nontrivial zeta zeros up to height 154000 on Re = 1/2 --
    `AllZeros_h153000` + a `[153000, 154000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h153000
import RHInBoxT_1d4000000_3999999d4000000_153000_153026
import RHInBoxT_1d4000000_3999999d4000000_612103d4_153051
import RHInBoxT_1d4000000_3999999d4000000_153051_153077
import RHInBoxT_1d4000000_3999999d4000000_153077_153103
import RHInBoxT_1d4000000_3999999d4000000_153103_153128
import RHInBoxT_1d4000000_3999999d4000000_153128_612617d4
import RHInBoxT_1d4000000_3999999d4000000_153154_153179
import RHInBoxT_1d4000000_3999999d4000000_153179_153205
import RHInBoxT_1d4000000_3999999d4000000_153205_153231
import RHInBoxT_1d4000000_3999999d4000000_153231_153256
import RHInBoxT_1d4000000_3999999d4000000_153256_153282
import RHInBoxT_1d4000000_3999999d4000000_153282_613233d4
import RHInBoxT_1d4000000_3999999d4000000_153308_153333
import RHInBoxT_1d4000000_3999999d4000000_153333_613437d4
import RHInBoxT_1d4000000_3999999d4000000_153359_153385
import RHInBoxT_1d4000000_3999999d4000000_153385_153410
import RHInBoxT_1d4000000_3999999d4000000_613639d4_153436
import RHInBoxT_1d4000000_3999999d4000000_153436_153462
import RHInBoxT_1d4000000_3999999d4000000_153462_153487
import RHInBoxT_1d4000000_3999999d4000000_153487_614053d4
import RHInBoxT_1d4000000_3999999d4000000_153513_153538
import RHInBoxT_1d4000000_3999999d4000000_153538_153564
import RHInBoxT_1d4000000_3999999d4000000_153564_153590
import RHInBoxT_1d4000000_3999999d4000000_614359d4_153615
import RHInBoxT_1d4000000_3999999d4000000_153615_153641
import RHInBoxT_1d4000000_3999999d4000000_153641_153667
import RHInBoxT_1d4000000_3999999d4000000_153667_153692
import RHInBoxT_1d4000000_3999999d4000000_153692_153718
import RHInBoxT_1d4000000_3999999d4000000_153718_153744
import RHInBoxT_1d4000000_3999999d4000000_614975d4_153769
import RHInBoxT_1d4000000_3999999d4000000_153769_153795
import RHInBoxT_1d4000000_3999999d4000000_153795_153821
import RHInBoxT_1d4000000_3999999d4000000_153821_153846
import RHInBoxT_1d4000000_3999999d4000000_615383d4_153872
import RHInBoxT_1d4000000_3999999d4000000_153872_153897
import RHInBoxT_1d4000000_3999999d4000000_615587d4_153923
import RHInBoxT_1d4000000_3999999d4000000_153923_153949
import RHInBoxT_1d4000000_3999999d4000000_153949_153974
import RHInBoxT_1d4000000_3999999d4000000_153974_154000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h154000

/-- The 39-band NOMINAL partition of `[153000, 154000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 153000
  | 1 => 153026
  | 2 => 153051
  | 3 => 153077
  | 4 => 153103
  | 5 => 153128
  | 6 => 153154
  | 7 => 153179
  | 8 => 153205
  | 9 => 153231
  | 10 => 153256
  | 11 => 153282
  | 12 => 153308
  | 13 => 153333
  | 14 => 153359
  | 15 => 153385
  | 16 => 153410
  | 17 => 153436
  | 18 => 153462
  | 19 => 153487
  | 20 => 153513
  | 21 => 153538
  | 22 => 153564
  | 23 => 153590
  | 24 => 153615
  | 25 => 153641
  | 26 => 153667
  | 27 => 153692
  | 28 => 153718
  | 29 => 153744
  | 30 => 153769
  | 31 => 153795
  | 32 => 153821
  | 33 => 153846
  | 34 => 153872
  | 35 => 153897
  | 36 => 153923
  | 37 => 153949
  | 38 => 153974
  | 39 => 154000
  | _ => 154000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((153000:ℝ)) ≤ (153026); norm_num
  · show ((153026:ℝ)) ≤ (153051); norm_num
  · show ((153051:ℝ)) ≤ (153077); norm_num
  · show ((153077:ℝ)) ≤ (153103); norm_num
  · show ((153103:ℝ)) ≤ (153128); norm_num
  · show ((153128:ℝ)) ≤ (153154); norm_num
  · show ((153154:ℝ)) ≤ (153179); norm_num
  · show ((153179:ℝ)) ≤ (153205); norm_num
  · show ((153205:ℝ)) ≤ (153231); norm_num
  · show ((153231:ℝ)) ≤ (153256); norm_num
  · show ((153256:ℝ)) ≤ (153282); norm_num
  · show ((153282:ℝ)) ≤ (153308); norm_num
  · show ((153308:ℝ)) ≤ (153333); norm_num
  · show ((153333:ℝ)) ≤ (153359); norm_num
  · show ((153359:ℝ)) ≤ (153385); norm_num
  · show ((153385:ℝ)) ≤ (153410); norm_num
  · show ((153410:ℝ)) ≤ (153436); norm_num
  · show ((153436:ℝ)) ≤ (153462); norm_num
  · show ((153462:ℝ)) ≤ (153487); norm_num
  · show ((153487:ℝ)) ≤ (153513); norm_num
  · show ((153513:ℝ)) ≤ (153538); norm_num
  · show ((153538:ℝ)) ≤ (153564); norm_num
  · show ((153564:ℝ)) ≤ (153590); norm_num
  · show ((153590:ℝ)) ≤ (153615); norm_num
  · show ((153615:ℝ)) ≤ (153641); norm_num
  · show ((153641:ℝ)) ≤ (153667); norm_num
  · show ((153667:ℝ)) ≤ (153692); norm_num
  · show ((153692:ℝ)) ≤ (153718); norm_num
  · show ((153718:ℝ)) ≤ (153744); norm_num
  · show ((153744:ℝ)) ≤ (153769); norm_num
  · show ((153769:ℝ)) ≤ (153795); norm_num
  · show ((153795:ℝ)) ≤ (153821); norm_num
  · show ((153821:ℝ)) ≤ (153846); norm_num
  · show ((153846:ℝ)) ≤ (153872); norm_num
  · show ((153872:ℝ)) ≤ (153897); norm_num
  · show ((153897:ℝ)) ≤ (153923); norm_num
  · show ((153923:ℝ)) ≤ (153949); norm_num
  · show ((153949:ℝ)) ≤ (153974); norm_num
  · show ((153974:ℝ)) ≤ (154000); norm_num
  · show ((154000:ℝ)) ≤ (154000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 153000
  | 1 => 612103 / 4
  | 2 => 153051
  | 3 => 153077
  | 4 => 153103
  | 5 => 153128
  | 6 => 153154
  | 7 => 153179
  | 8 => 153205
  | 9 => 153231
  | 10 => 153256
  | 11 => 153282
  | 12 => 153308
  | 13 => 153333
  | 14 => 153359
  | 15 => 153385
  | 16 => 613639 / 4
  | 17 => 153436
  | 18 => 153462
  | 19 => 153487
  | 20 => 153513
  | 21 => 153538
  | 22 => 153564
  | 23 => 614359 / 4
  | 24 => 153615
  | 25 => 153641
  | 26 => 153667
  | 27 => 153692
  | 28 => 153718
  | 29 => 614975 / 4
  | 30 => 153769
  | 31 => 153795
  | 32 => 153821
  | 33 => 615383 / 4
  | 34 => 153872
  | 35 => 615587 / 4
  | 36 => 153923
  | 37 => 153949
  | 38 => 153974
  | _ => 153974

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 153026
  | 1 => 153051
  | 2 => 153077
  | 3 => 153103
  | 4 => 153128
  | 5 => 612617 / 4
  | 6 => 153179
  | 7 => 153205
  | 8 => 153231
  | 9 => 153256
  | 10 => 153282
  | 11 => 613233 / 4
  | 12 => 153333
  | 13 => 613437 / 4
  | 14 => 153385
  | 15 => 153410
  | 16 => 153436
  | 17 => 153462
  | 18 => 153487
  | 19 => 614053 / 4
  | 20 => 153538
  | 21 => 153564
  | 22 => 153590
  | 23 => 153615
  | 24 => 153641
  | 25 => 153667
  | 26 => 153692
  | 27 => 153718
  | 28 => 153744
  | 29 => 153769
  | 30 => 153795
  | 31 => 153821
  | 32 => 153846
  | 33 => 153872
  | 34 => 153897
  | 35 => 153923
  | 36 => 153949
  | 37 => 153974
  | 38 => 154000
  | _ => 154000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 154000` (`log 154000 ≤ 13`, `2.7^13 ≥ 154000`). -/
theorem haC_154000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 154000 := by
  have hlog : Real.log 154000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 154000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 154000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[153000, 154000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[153000, 154000]` SEGMENT: every zero with `153000 ≤ Im ≤ 154000` is on the line. -/
theorem segment_153000_154000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 154000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (153000:ℝ) ≤ ρ.im → ρ.im ≤ 154000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 153000 154000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_154000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 154000 via the HEIGHT CHAIN**: `[0,153000]` ∘ `[153000,154000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_154000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 154000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 154000 → ρ.re = 1 / 2 := by
  have hγ153000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 153000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 153000 154000
    (AllZeros_h153000.all_nontrivial_zeros_up_to_height_153000_of_bands
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
      hγ153000)
    (segment_153000_154000 hbands hγ)

end AllZeros_h154000

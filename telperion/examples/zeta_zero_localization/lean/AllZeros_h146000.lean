/-  Height-chain step: all nontrivial zeta zeros up to height 146000 on Re = 1/2 --
    `AllZeros_h145000` + a `[145000, 146000]` SEGMENT certificate (39 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h145000
import RHInBoxT_1d4000000_3999999d4000000_145000_145026
import RHInBoxT_1d4000000_3999999d4000000_580103d4_145051
import RHInBoxT_1d4000000_3999999d4000000_580203d4_145077
import RHInBoxT_1d4000000_3999999d4000000_145077_580413d4
import RHInBoxT_1d4000000_3999999d4000000_145103_145128
import RHInBoxT_1d4000000_3999999d4000000_145128_145154
import RHInBoxT_1d4000000_3999999d4000000_145154_580717d4
import RHInBoxT_1d4000000_3999999d4000000_145179_145205
import RHInBoxT_1d4000000_3999999d4000000_580819d4_580925d4
import RHInBoxT_1d4000000_3999999d4000000_145231_145256
import RHInBoxT_1d4000000_3999999d4000000_145256_145282
import RHInBoxT_1d4000000_3999999d4000000_145282_145308
import RHInBoxT_1d4000000_3999999d4000000_145308_581333d4
import RHInBoxT_1d4000000_3999999d4000000_145333_145359
import RHInBoxT_1d4000000_3999999d4000000_145359_581541d4
import RHInBoxT_1d4000000_3999999d4000000_145385_145410
import RHInBoxT_1d4000000_3999999d4000000_145410_145436
import RHInBoxT_1d4000000_3999999d4000000_145436_145462
import RHInBoxT_1d4000000_3999999d4000000_145462_581949d4
import RHInBoxT_1d4000000_3999999d4000000_145487_145513
import RHInBoxT_1d4000000_3999999d4000000_145513_145538
import RHInBoxT_1d4000000_3999999d4000000_145538_145564
import RHInBoxT_1d4000000_3999999d4000000_582255d4_145590
import RHInBoxT_1d4000000_3999999d4000000_145590_145615
import RHInBoxT_1d4000000_3999999d4000000_145615_145641
import RHInBoxT_1d4000000_3999999d4000000_145641_145667
import RHInBoxT_1d4000000_3999999d4000000_145667_145692
import RHInBoxT_1d4000000_3999999d4000000_145692_145718
import RHInBoxT_1d4000000_3999999d4000000_145718_145744
import RHInBoxT_1d4000000_3999999d4000000_145744_145769
import RHInBoxT_1d4000000_3999999d4000000_145769_145795
import RHInBoxT_1d4000000_3999999d4000000_583179d4_583285d4
import RHInBoxT_1d4000000_3999999d4000000_145821_145846
import RHInBoxT_1d4000000_3999999d4000000_145846_145872
import RHInBoxT_1d4000000_3999999d4000000_145872_145897
import RHInBoxT_1d4000000_3999999d4000000_145897_583693d4
import RHInBoxT_1d4000000_3999999d4000000_145923_145949
import RHInBoxT_1d4000000_3999999d4000000_145949_145974
import RHInBoxT_1d4000000_3999999d4000000_583895d4_146000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h146000

/-- The 39-band NOMINAL partition of `[145000, 146000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 145000
  | 1 => 145026
  | 2 => 145051
  | 3 => 145077
  | 4 => 145103
  | 5 => 145128
  | 6 => 145154
  | 7 => 145179
  | 8 => 145205
  | 9 => 145231
  | 10 => 145256
  | 11 => 145282
  | 12 => 145308
  | 13 => 145333
  | 14 => 145359
  | 15 => 145385
  | 16 => 145410
  | 17 => 145436
  | 18 => 145462
  | 19 => 145487
  | 20 => 145513
  | 21 => 145538
  | 22 => 145564
  | 23 => 145590
  | 24 => 145615
  | 25 => 145641
  | 26 => 145667
  | 27 => 145692
  | 28 => 145718
  | 29 => 145744
  | 30 => 145769
  | 31 => 145795
  | 32 => 145821
  | 33 => 145846
  | 34 => 145872
  | 35 => 145897
  | 36 => 145923
  | 37 => 145949
  | 38 => 145974
  | 39 => 146000
  | _ => 146000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((145000:ℝ)) ≤ (145026); norm_num
  · show ((145026:ℝ)) ≤ (145051); norm_num
  · show ((145051:ℝ)) ≤ (145077); norm_num
  · show ((145077:ℝ)) ≤ (145103); norm_num
  · show ((145103:ℝ)) ≤ (145128); norm_num
  · show ((145128:ℝ)) ≤ (145154); norm_num
  · show ((145154:ℝ)) ≤ (145179); norm_num
  · show ((145179:ℝ)) ≤ (145205); norm_num
  · show ((145205:ℝ)) ≤ (145231); norm_num
  · show ((145231:ℝ)) ≤ (145256); norm_num
  · show ((145256:ℝ)) ≤ (145282); norm_num
  · show ((145282:ℝ)) ≤ (145308); norm_num
  · show ((145308:ℝ)) ≤ (145333); norm_num
  · show ((145333:ℝ)) ≤ (145359); norm_num
  · show ((145359:ℝ)) ≤ (145385); norm_num
  · show ((145385:ℝ)) ≤ (145410); norm_num
  · show ((145410:ℝ)) ≤ (145436); norm_num
  · show ((145436:ℝ)) ≤ (145462); norm_num
  · show ((145462:ℝ)) ≤ (145487); norm_num
  · show ((145487:ℝ)) ≤ (145513); norm_num
  · show ((145513:ℝ)) ≤ (145538); norm_num
  · show ((145538:ℝ)) ≤ (145564); norm_num
  · show ((145564:ℝ)) ≤ (145590); norm_num
  · show ((145590:ℝ)) ≤ (145615); norm_num
  · show ((145615:ℝ)) ≤ (145641); norm_num
  · show ((145641:ℝ)) ≤ (145667); norm_num
  · show ((145667:ℝ)) ≤ (145692); norm_num
  · show ((145692:ℝ)) ≤ (145718); norm_num
  · show ((145718:ℝ)) ≤ (145744); norm_num
  · show ((145744:ℝ)) ≤ (145769); norm_num
  · show ((145769:ℝ)) ≤ (145795); norm_num
  · show ((145795:ℝ)) ≤ (145821); norm_num
  · show ((145821:ℝ)) ≤ (145846); norm_num
  · show ((145846:ℝ)) ≤ (145872); norm_num
  · show ((145872:ℝ)) ≤ (145897); norm_num
  · show ((145897:ℝ)) ≤ (145923); norm_num
  · show ((145923:ℝ)) ≤ (145949); norm_num
  · show ((145949:ℝ)) ≤ (145974); norm_num
  · show ((145974:ℝ)) ≤ (146000); norm_num
  · show ((146000:ℝ)) ≤ (146000); norm_num
  · exact le_refl _

/-- The lower edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 145000
  | 1 => 580103 / 4
  | 2 => 580203 / 4
  | 3 => 145077
  | 4 => 145103
  | 5 => 145128
  | 6 => 145154
  | 7 => 145179
  | 8 => 580819 / 4
  | 9 => 145231
  | 10 => 145256
  | 11 => 145282
  | 12 => 145308
  | 13 => 145333
  | 14 => 145359
  | 15 => 145385
  | 16 => 145410
  | 17 => 145436
  | 18 => 145462
  | 19 => 145487
  | 20 => 145513
  | 21 => 145538
  | 22 => 582255 / 4
  | 23 => 145590
  | 24 => 145615
  | 25 => 145641
  | 26 => 145667
  | 27 => 145692
  | 28 => 145718
  | 29 => 145744
  | 30 => 145769
  | 31 => 583179 / 4
  | 32 => 145821
  | 33 => 145846
  | 34 => 145872
  | 35 => 145897
  | 36 => 145923
  | 37 => 145949
  | 38 => 583895 / 4
  | _ => 583895 / 4

/-- The upper edges of the 39 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 145026
  | 1 => 145051
  | 2 => 145077
  | 3 => 580413 / 4
  | 4 => 145128
  | 5 => 145154
  | 6 => 580717 / 4
  | 7 => 145205
  | 8 => 580925 / 4
  | 9 => 145256
  | 10 => 145282
  | 11 => 145308
  | 12 => 581333 / 4
  | 13 => 145359
  | 14 => 581541 / 4
  | 15 => 145410
  | 16 => 145436
  | 17 => 145462
  | 18 => 581949 / 4
  | 19 => 145513
  | 20 => 145538
  | 21 => 145564
  | 22 => 145590
  | 23 => 145615
  | 24 => 145641
  | 25 => 145667
  | 26 => 145692
  | 27 => 145718
  | 28 => 145744
  | 29 => 145769
  | 30 => 145795
  | 31 => 583285 / 4
  | 32 => 145846
  | 33 => 145872
  | 34 => 145897
  | 35 => 583693 / 4
  | 36 => 145949
  | 37 => 145974
  | 38 => 146000
  | _ => 146000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 39 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 146000` (`log 146000 ≤ 12`, `2.7^12 ≥ 146000`). -/
theorem haC_146000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 146000 := by
  have hlog : Real.log 146000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 146000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 146000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[145000, 146000]` segment's band hypothesis: every band `i < 39` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 39 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 39 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[145000, 146000]` SEGMENT: every zero with `145000 ≤ Im ≤ 146000` is on the line. -/
theorem segment_145000_146000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 146000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (145000:ℝ) ≤ ρ.im → ρ.im ≤ 146000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 145000 146000 bndSeg 39 (by norm_num) bndSeg_mono rfl rfl haC_146000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 146000 via the HEIGHT CHAIN**: `[0,145000]` ∘ `[145000,146000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_146000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 146000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 146000 → ρ.re = 1 / 2 := by
  have hγ145000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 145000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 145000 146000
    (AllZeros_h145000.all_nontrivial_zeros_up_to_height_145000_of_bands
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
      hγ145000)
    (segment_145000_146000 hbands hγ)

end AllZeros_h146000

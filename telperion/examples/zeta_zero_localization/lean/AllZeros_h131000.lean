/-  Height-chain step: all nontrivial zeta zeros up to height 131000 on Re = 1/2 --
    `AllZeros_h130000` + a `[130000, 131000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h130000
import RHInBoxT_1d4000000_3999999d4000000_130000_130026
import RHInBoxT_1d4000000_3999999d4000000_130026_130053
import RHInBoxT_1d4000000_3999999d4000000_520211d4_130079
import RHInBoxT_1d4000000_3999999d4000000_130079_130105
import RHInBoxT_1d4000000_3999999d4000000_130105_130132
import RHInBoxT_1d4000000_3999999d4000000_130132_130158
import RHInBoxT_1d4000000_3999999d4000000_130158_130184
import RHInBoxT_1d4000000_3999999d4000000_130184_130211
import RHInBoxT_1d4000000_3999999d4000000_130211_130237
import RHInBoxT_1d4000000_3999999d4000000_130237_130263
import RHInBoxT_1d4000000_3999999d4000000_130263_130289
import RHInBoxT_1d4000000_3999999d4000000_130289_130316
import RHInBoxT_1d4000000_3999999d4000000_130316_130342
import RHInBoxT_1d4000000_3999999d4000000_130342_130368
import RHInBoxT_1d4000000_3999999d4000000_521471d4_521581d4
import RHInBoxT_1d4000000_3999999d4000000_130395_130421
import RHInBoxT_1d4000000_3999999d4000000_130421_521789d4
import RHInBoxT_1d4000000_3999999d4000000_130447_130474
import RHInBoxT_1d4000000_3999999d4000000_130474_522001d4
import RHInBoxT_1d4000000_3999999d4000000_130500_130526
import RHInBoxT_1d4000000_3999999d4000000_130526_130553
import RHInBoxT_1d4000000_3999999d4000000_130553_130579
import RHInBoxT_1d4000000_3999999d4000000_130579_130605
import RHInBoxT_1d4000000_3999999d4000000_130605_130632
import RHInBoxT_1d4000000_3999999d4000000_130632_130658
import RHInBoxT_1d4000000_3999999d4000000_130658_130684
import RHInBoxT_1d4000000_3999999d4000000_130684_130711
import RHInBoxT_1d4000000_3999999d4000000_130711_130737
import RHInBoxT_1d4000000_3999999d4000000_130737_130763
import RHInBoxT_1d4000000_3999999d4000000_130763_523157d4
import RHInBoxT_1d4000000_3999999d4000000_130789_130816
import RHInBoxT_1d4000000_3999999d4000000_130816_130842
import RHInBoxT_1d4000000_3999999d4000000_130842_130868
import RHInBoxT_1d4000000_3999999d4000000_130868_130895
import RHInBoxT_1d4000000_3999999d4000000_130895_130921
import RHInBoxT_1d4000000_3999999d4000000_130921_523789d4
import RHInBoxT_1d4000000_3999999d4000000_130947_130974
import RHInBoxT_1d4000000_3999999d4000000_130974_131000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h131000

/-- The 38-band NOMINAL partition of `[130000, 131000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 130000
  | 1 => 130026
  | 2 => 130053
  | 3 => 130079
  | 4 => 130105
  | 5 => 130132
  | 6 => 130158
  | 7 => 130184
  | 8 => 130211
  | 9 => 130237
  | 10 => 130263
  | 11 => 130289
  | 12 => 130316
  | 13 => 130342
  | 14 => 130368
  | 15 => 130395
  | 16 => 130421
  | 17 => 130447
  | 18 => 130474
  | 19 => 130500
  | 20 => 130526
  | 21 => 130553
  | 22 => 130579
  | 23 => 130605
  | 24 => 130632
  | 25 => 130658
  | 26 => 130684
  | 27 => 130711
  | 28 => 130737
  | 29 => 130763
  | 30 => 130789
  | 31 => 130816
  | 32 => 130842
  | 33 => 130868
  | 34 => 130895
  | 35 => 130921
  | 36 => 130947
  | 37 => 130974
  | 38 => 131000
  | _ => 131000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((130000:ℝ)) ≤ (130026); norm_num
  · show ((130026:ℝ)) ≤ (130053); norm_num
  · show ((130053:ℝ)) ≤ (130079); norm_num
  · show ((130079:ℝ)) ≤ (130105); norm_num
  · show ((130105:ℝ)) ≤ (130132); norm_num
  · show ((130132:ℝ)) ≤ (130158); norm_num
  · show ((130158:ℝ)) ≤ (130184); norm_num
  · show ((130184:ℝ)) ≤ (130211); norm_num
  · show ((130211:ℝ)) ≤ (130237); norm_num
  · show ((130237:ℝ)) ≤ (130263); norm_num
  · show ((130263:ℝ)) ≤ (130289); norm_num
  · show ((130289:ℝ)) ≤ (130316); norm_num
  · show ((130316:ℝ)) ≤ (130342); norm_num
  · show ((130342:ℝ)) ≤ (130368); norm_num
  · show ((130368:ℝ)) ≤ (130395); norm_num
  · show ((130395:ℝ)) ≤ (130421); norm_num
  · show ((130421:ℝ)) ≤ (130447); norm_num
  · show ((130447:ℝ)) ≤ (130474); norm_num
  · show ((130474:ℝ)) ≤ (130500); norm_num
  · show ((130500:ℝ)) ≤ (130526); norm_num
  · show ((130526:ℝ)) ≤ (130553); norm_num
  · show ((130553:ℝ)) ≤ (130579); norm_num
  · show ((130579:ℝ)) ≤ (130605); norm_num
  · show ((130605:ℝ)) ≤ (130632); norm_num
  · show ((130632:ℝ)) ≤ (130658); norm_num
  · show ((130658:ℝ)) ≤ (130684); norm_num
  · show ((130684:ℝ)) ≤ (130711); norm_num
  · show ((130711:ℝ)) ≤ (130737); norm_num
  · show ((130737:ℝ)) ≤ (130763); norm_num
  · show ((130763:ℝ)) ≤ (130789); norm_num
  · show ((130789:ℝ)) ≤ (130816); norm_num
  · show ((130816:ℝ)) ≤ (130842); norm_num
  · show ((130842:ℝ)) ≤ (130868); norm_num
  · show ((130868:ℝ)) ≤ (130895); norm_num
  · show ((130895:ℝ)) ≤ (130921); norm_num
  · show ((130921:ℝ)) ≤ (130947); norm_num
  · show ((130947:ℝ)) ≤ (130974); norm_num
  · show ((130974:ℝ)) ≤ (131000); norm_num
  · show ((131000:ℝ)) ≤ (131000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 130000
  | 1 => 130026
  | 2 => 520211 / 4
  | 3 => 130079
  | 4 => 130105
  | 5 => 130132
  | 6 => 130158
  | 7 => 130184
  | 8 => 130211
  | 9 => 130237
  | 10 => 130263
  | 11 => 130289
  | 12 => 130316
  | 13 => 130342
  | 14 => 521471 / 4
  | 15 => 130395
  | 16 => 130421
  | 17 => 130447
  | 18 => 130474
  | 19 => 130500
  | 20 => 130526
  | 21 => 130553
  | 22 => 130579
  | 23 => 130605
  | 24 => 130632
  | 25 => 130658
  | 26 => 130684
  | 27 => 130711
  | 28 => 130737
  | 29 => 130763
  | 30 => 130789
  | 31 => 130816
  | 32 => 130842
  | 33 => 130868
  | 34 => 130895
  | 35 => 130921
  | 36 => 130947
  | 37 => 130974
  | _ => 130974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 130026
  | 1 => 130053
  | 2 => 130079
  | 3 => 130105
  | 4 => 130132
  | 5 => 130158
  | 6 => 130184
  | 7 => 130211
  | 8 => 130237
  | 9 => 130263
  | 10 => 130289
  | 11 => 130316
  | 12 => 130342
  | 13 => 130368
  | 14 => 521581 / 4
  | 15 => 130421
  | 16 => 521789 / 4
  | 17 => 130474
  | 18 => 522001 / 4
  | 19 => 130526
  | 20 => 130553
  | 21 => 130579
  | 22 => 130605
  | 23 => 130632
  | 24 => 130658
  | 25 => 130684
  | 26 => 130711
  | 27 => 130737
  | 28 => 130763
  | 29 => 523157 / 4
  | 30 => 130816
  | 31 => 130842
  | 32 => 130868
  | 33 => 130895
  | 34 => 130921
  | 35 => 523789 / 4
  | 36 => 130974
  | 37 => 131000
  | _ => 131000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 131000` (`log 131000 ≤ 12`, `2.7^12 ≥ 131000`). -/
theorem haC_131000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 131000 := by
  have hlog : Real.log 131000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 131000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 131000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[130000, 131000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[130000, 131000]` SEGMENT: every zero with `130000 ≤ Im ≤ 131000` is on the line. -/
theorem segment_130000_131000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 131000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (130000:ℝ) ≤ ρ.im → ρ.im ≤ 131000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 130000 131000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_131000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 131000 via the HEIGHT CHAIN**: `[0,130000]` ∘ `[130000,131000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_131000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 131000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 131000 → ρ.re = 1 / 2 := by
  have hγ130000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 130000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 130000 131000
    (AllZeros_h130000.all_nontrivial_zeros_up_to_height_130000_of_bands
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
      hγ130000)
    (segment_130000_131000 hbands hγ)

end AllZeros_h131000

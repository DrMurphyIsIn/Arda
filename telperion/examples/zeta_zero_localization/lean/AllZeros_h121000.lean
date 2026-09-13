/-  Height-chain step: all nontrivial zeta zeros up to height 121000 on Re = 1/2 --
    `AllZeros_h120000` + a `[120000, 121000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h120000
import RHInBoxT_1d4000000_3999999d4000000_120000_120026
import RHInBoxT_1d4000000_3999999d4000000_120026_120053
import RHInBoxT_1d4000000_3999999d4000000_120053_120079
import RHInBoxT_1d4000000_3999999d4000000_480315d4_480421d4
import RHInBoxT_1d4000000_3999999d4000000_120105_120132
import RHInBoxT_1d4000000_3999999d4000000_480527d4_120158
import RHInBoxT_1d4000000_3999999d4000000_120158_480737d4
import RHInBoxT_1d4000000_3999999d4000000_120184_480845d4
import RHInBoxT_1d4000000_3999999d4000000_120211_120237
import RHInBoxT_1d4000000_3999999d4000000_120237_120263
import RHInBoxT_1d4000000_3999999d4000000_120263_120289
import RHInBoxT_1d4000000_3999999d4000000_120289_120316
import RHInBoxT_1d4000000_3999999d4000000_120316_120342
import RHInBoxT_1d4000000_3999999d4000000_120342_120368
import RHInBoxT_1d4000000_3999999d4000000_120368_120395
import RHInBoxT_1d4000000_3999999d4000000_120395_120421
import RHInBoxT_1d4000000_3999999d4000000_481683d4_120447
import RHInBoxT_1d4000000_3999999d4000000_120447_120474
import RHInBoxT_1d4000000_3999999d4000000_120474_482001d4
import RHInBoxT_1d4000000_3999999d4000000_120500_120526
import RHInBoxT_1d4000000_3999999d4000000_120526_120553
import RHInBoxT_1d4000000_3999999d4000000_120553_120579
import RHInBoxT_1d4000000_3999999d4000000_120579_120605
import RHInBoxT_1d4000000_3999999d4000000_120605_120632
import RHInBoxT_1d4000000_3999999d4000000_482527d4_120658
import RHInBoxT_1d4000000_3999999d4000000_120658_482737d4
import RHInBoxT_1d4000000_3999999d4000000_120684_120711
import RHInBoxT_1d4000000_3999999d4000000_482843d4_120737
import RHInBoxT_1d4000000_3999999d4000000_120737_120763
import RHInBoxT_1d4000000_3999999d4000000_120763_120789
import RHInBoxT_1d4000000_3999999d4000000_120789_120816
import RHInBoxT_1d4000000_3999999d4000000_120816_120842
import RHInBoxT_1d4000000_3999999d4000000_120842_120868
import RHInBoxT_1d4000000_3999999d4000000_120868_120895
import RHInBoxT_1d4000000_3999999d4000000_120895_120921
import RHInBoxT_1d4000000_3999999d4000000_120921_483789d4
import RHInBoxT_1d4000000_3999999d4000000_120947_120974
import RHInBoxT_1d4000000_3999999d4000000_120974_121000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h121000

/-- The 38-band NOMINAL partition of `[120000, 121000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 120000
  | 1 => 120026
  | 2 => 120053
  | 3 => 120079
  | 4 => 120105
  | 5 => 120132
  | 6 => 120158
  | 7 => 120184
  | 8 => 120211
  | 9 => 120237
  | 10 => 120263
  | 11 => 120289
  | 12 => 120316
  | 13 => 120342
  | 14 => 120368
  | 15 => 120395
  | 16 => 120421
  | 17 => 120447
  | 18 => 120474
  | 19 => 120500
  | 20 => 120526
  | 21 => 120553
  | 22 => 120579
  | 23 => 120605
  | 24 => 120632
  | 25 => 120658
  | 26 => 120684
  | 27 => 120711
  | 28 => 120737
  | 29 => 120763
  | 30 => 120789
  | 31 => 120816
  | 32 => 120842
  | 33 => 120868
  | 34 => 120895
  | 35 => 120921
  | 36 => 120947
  | 37 => 120974
  | 38 => 121000
  | _ => 121000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((120000:ℝ)) ≤ (120026); norm_num
  · show ((120026:ℝ)) ≤ (120053); norm_num
  · show ((120053:ℝ)) ≤ (120079); norm_num
  · show ((120079:ℝ)) ≤ (120105); norm_num
  · show ((120105:ℝ)) ≤ (120132); norm_num
  · show ((120132:ℝ)) ≤ (120158); norm_num
  · show ((120158:ℝ)) ≤ (120184); norm_num
  · show ((120184:ℝ)) ≤ (120211); norm_num
  · show ((120211:ℝ)) ≤ (120237); norm_num
  · show ((120237:ℝ)) ≤ (120263); norm_num
  · show ((120263:ℝ)) ≤ (120289); norm_num
  · show ((120289:ℝ)) ≤ (120316); norm_num
  · show ((120316:ℝ)) ≤ (120342); norm_num
  · show ((120342:ℝ)) ≤ (120368); norm_num
  · show ((120368:ℝ)) ≤ (120395); norm_num
  · show ((120395:ℝ)) ≤ (120421); norm_num
  · show ((120421:ℝ)) ≤ (120447); norm_num
  · show ((120447:ℝ)) ≤ (120474); norm_num
  · show ((120474:ℝ)) ≤ (120500); norm_num
  · show ((120500:ℝ)) ≤ (120526); norm_num
  · show ((120526:ℝ)) ≤ (120553); norm_num
  · show ((120553:ℝ)) ≤ (120579); norm_num
  · show ((120579:ℝ)) ≤ (120605); norm_num
  · show ((120605:ℝ)) ≤ (120632); norm_num
  · show ((120632:ℝ)) ≤ (120658); norm_num
  · show ((120658:ℝ)) ≤ (120684); norm_num
  · show ((120684:ℝ)) ≤ (120711); norm_num
  · show ((120711:ℝ)) ≤ (120737); norm_num
  · show ((120737:ℝ)) ≤ (120763); norm_num
  · show ((120763:ℝ)) ≤ (120789); norm_num
  · show ((120789:ℝ)) ≤ (120816); norm_num
  · show ((120816:ℝ)) ≤ (120842); norm_num
  · show ((120842:ℝ)) ≤ (120868); norm_num
  · show ((120868:ℝ)) ≤ (120895); norm_num
  · show ((120895:ℝ)) ≤ (120921); norm_num
  · show ((120921:ℝ)) ≤ (120947); norm_num
  · show ((120947:ℝ)) ≤ (120974); norm_num
  · show ((120974:ℝ)) ≤ (121000); norm_num
  · show ((121000:ℝ)) ≤ (121000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 120000
  | 1 => 120026
  | 2 => 120053
  | 3 => 480315 / 4
  | 4 => 120105
  | 5 => 480527 / 4
  | 6 => 120158
  | 7 => 120184
  | 8 => 120211
  | 9 => 120237
  | 10 => 120263
  | 11 => 120289
  | 12 => 120316
  | 13 => 120342
  | 14 => 120368
  | 15 => 120395
  | 16 => 481683 / 4
  | 17 => 120447
  | 18 => 120474
  | 19 => 120500
  | 20 => 120526
  | 21 => 120553
  | 22 => 120579
  | 23 => 120605
  | 24 => 482527 / 4
  | 25 => 120658
  | 26 => 120684
  | 27 => 482843 / 4
  | 28 => 120737
  | 29 => 120763
  | 30 => 120789
  | 31 => 120816
  | 32 => 120842
  | 33 => 120868
  | 34 => 120895
  | 35 => 120921
  | 36 => 120947
  | 37 => 120974
  | _ => 120974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 120026
  | 1 => 120053
  | 2 => 120079
  | 3 => 480421 / 4
  | 4 => 120132
  | 5 => 120158
  | 6 => 480737 / 4
  | 7 => 480845 / 4
  | 8 => 120237
  | 9 => 120263
  | 10 => 120289
  | 11 => 120316
  | 12 => 120342
  | 13 => 120368
  | 14 => 120395
  | 15 => 120421
  | 16 => 120447
  | 17 => 120474
  | 18 => 482001 / 4
  | 19 => 120526
  | 20 => 120553
  | 21 => 120579
  | 22 => 120605
  | 23 => 120632
  | 24 => 120658
  | 25 => 482737 / 4
  | 26 => 120711
  | 27 => 120737
  | 28 => 120763
  | 29 => 120789
  | 30 => 120816
  | 31 => 120842
  | 32 => 120868
  | 33 => 120895
  | 34 => 120921
  | 35 => 483789 / 4
  | 36 => 120974
  | 37 => 121000
  | _ => 121000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 121000` (`log 121000 ≤ 12`, `2.7^12 ≥ 121000`). -/
theorem haC_121000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 121000 := by
  have hlog : Real.log 121000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 121000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 121000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[120000, 121000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[120000, 121000]` SEGMENT: every zero with `120000 ≤ Im ≤ 121000` is on the line. -/
theorem segment_120000_121000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 121000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (120000:ℝ) ≤ ρ.im → ρ.im ≤ 121000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 120000 121000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_121000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 121000 via the HEIGHT CHAIN**: `[0,120000]` ∘ `[120000,121000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_121000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 121000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 121000 → ρ.re = 1 / 2 := by
  have hγ120000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 120000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 120000 121000
    (AllZeros_h120000.all_nontrivial_zeros_up_to_height_120000_of_bands
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
      hγ120000)
    (segment_120000_121000 hbands hγ)

end AllZeros_h121000

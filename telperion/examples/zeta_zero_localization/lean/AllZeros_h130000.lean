/-  Height-chain step: all nontrivial zeta zeros up to height 130000 on Re = 1/2 --
    `AllZeros_h129000` + a `[129000, 130000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h129000
import RHInBoxT_1d4000000_3999999d4000000_129000_516105d4
import RHInBoxT_1d4000000_3999999d4000000_129026_129053
import RHInBoxT_1d4000000_3999999d4000000_516211d4_129079
import RHInBoxT_1d4000000_3999999d4000000_129079_129105
import RHInBoxT_1d4000000_3999999d4000000_129105_129132
import RHInBoxT_1d4000000_3999999d4000000_516527d4_129158
import RHInBoxT_1d4000000_3999999d4000000_129158_129184
import RHInBoxT_1d4000000_3999999d4000000_129184_129211
import RHInBoxT_1d4000000_3999999d4000000_516843d4_129237
import RHInBoxT_1d4000000_3999999d4000000_129237_129263
import RHInBoxT_1d4000000_3999999d4000000_129263_129289
import RHInBoxT_1d4000000_3999999d4000000_129289_129316
import RHInBoxT_1d4000000_3999999d4000000_129316_129342
import RHInBoxT_1d4000000_3999999d4000000_129342_129368
import RHInBoxT_1d4000000_3999999d4000000_129368_129395
import RHInBoxT_1d4000000_3999999d4000000_129395_129421
import RHInBoxT_1d4000000_3999999d4000000_517683d4_129447
import RHInBoxT_1d4000000_3999999d4000000_129447_129474
import RHInBoxT_1d4000000_3999999d4000000_129474_129500
import RHInBoxT_1d4000000_3999999d4000000_129500_129526
import RHInBoxT_1d4000000_3999999d4000000_129526_129553
import RHInBoxT_1d4000000_3999999d4000000_129553_129579
import RHInBoxT_1d4000000_3999999d4000000_129579_129605
import RHInBoxT_1d4000000_3999999d4000000_129605_129632
import RHInBoxT_1d4000000_3999999d4000000_129632_129658
import RHInBoxT_1d4000000_3999999d4000000_518631d4_129684
import RHInBoxT_1d4000000_3999999d4000000_129684_129711
import RHInBoxT_1d4000000_3999999d4000000_129711_129737
import RHInBoxT_1d4000000_3999999d4000000_129737_519053d4
import RHInBoxT_1d4000000_3999999d4000000_129763_129789
import RHInBoxT_1d4000000_3999999d4000000_519155d4_129816
import RHInBoxT_1d4000000_3999999d4000000_129816_519369d4
import RHInBoxT_1d4000000_3999999d4000000_129842_129868
import RHInBoxT_1d4000000_3999999d4000000_129868_519581d4
import RHInBoxT_1d4000000_3999999d4000000_129895_129921
import RHInBoxT_1d4000000_3999999d4000000_129921_129947
import RHInBoxT_1d4000000_3999999d4000000_519787d4_519897d4
import RHInBoxT_1d4000000_3999999d4000000_129974_520001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h130000

/-- The 38-band NOMINAL partition of `[129000, 130000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 129000
  | 1 => 129026
  | 2 => 129053
  | 3 => 129079
  | 4 => 129105
  | 5 => 129132
  | 6 => 129158
  | 7 => 129184
  | 8 => 129211
  | 9 => 129237
  | 10 => 129263
  | 11 => 129289
  | 12 => 129316
  | 13 => 129342
  | 14 => 129368
  | 15 => 129395
  | 16 => 129421
  | 17 => 129447
  | 18 => 129474
  | 19 => 129500
  | 20 => 129526
  | 21 => 129553
  | 22 => 129579
  | 23 => 129605
  | 24 => 129632
  | 25 => 129658
  | 26 => 129684
  | 27 => 129711
  | 28 => 129737
  | 29 => 129763
  | 30 => 129789
  | 31 => 129816
  | 32 => 129842
  | 33 => 129868
  | 34 => 129895
  | 35 => 129921
  | 36 => 129947
  | 37 => 129974
  | 38 => 130000
  | _ => 130000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((129000:ℝ)) ≤ (129026); norm_num
  · show ((129026:ℝ)) ≤ (129053); norm_num
  · show ((129053:ℝ)) ≤ (129079); norm_num
  · show ((129079:ℝ)) ≤ (129105); norm_num
  · show ((129105:ℝ)) ≤ (129132); norm_num
  · show ((129132:ℝ)) ≤ (129158); norm_num
  · show ((129158:ℝ)) ≤ (129184); norm_num
  · show ((129184:ℝ)) ≤ (129211); norm_num
  · show ((129211:ℝ)) ≤ (129237); norm_num
  · show ((129237:ℝ)) ≤ (129263); norm_num
  · show ((129263:ℝ)) ≤ (129289); norm_num
  · show ((129289:ℝ)) ≤ (129316); norm_num
  · show ((129316:ℝ)) ≤ (129342); norm_num
  · show ((129342:ℝ)) ≤ (129368); norm_num
  · show ((129368:ℝ)) ≤ (129395); norm_num
  · show ((129395:ℝ)) ≤ (129421); norm_num
  · show ((129421:ℝ)) ≤ (129447); norm_num
  · show ((129447:ℝ)) ≤ (129474); norm_num
  · show ((129474:ℝ)) ≤ (129500); norm_num
  · show ((129500:ℝ)) ≤ (129526); norm_num
  · show ((129526:ℝ)) ≤ (129553); norm_num
  · show ((129553:ℝ)) ≤ (129579); norm_num
  · show ((129579:ℝ)) ≤ (129605); norm_num
  · show ((129605:ℝ)) ≤ (129632); norm_num
  · show ((129632:ℝ)) ≤ (129658); norm_num
  · show ((129658:ℝ)) ≤ (129684); norm_num
  · show ((129684:ℝ)) ≤ (129711); norm_num
  · show ((129711:ℝ)) ≤ (129737); norm_num
  · show ((129737:ℝ)) ≤ (129763); norm_num
  · show ((129763:ℝ)) ≤ (129789); norm_num
  · show ((129789:ℝ)) ≤ (129816); norm_num
  · show ((129816:ℝ)) ≤ (129842); norm_num
  · show ((129842:ℝ)) ≤ (129868); norm_num
  · show ((129868:ℝ)) ≤ (129895); norm_num
  · show ((129895:ℝ)) ≤ (129921); norm_num
  · show ((129921:ℝ)) ≤ (129947); norm_num
  · show ((129947:ℝ)) ≤ (129974); norm_num
  · show ((129974:ℝ)) ≤ (130000); norm_num
  · show ((130000:ℝ)) ≤ (130000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 129000
  | 1 => 129026
  | 2 => 516211 / 4
  | 3 => 129079
  | 4 => 129105
  | 5 => 516527 / 4
  | 6 => 129158
  | 7 => 129184
  | 8 => 516843 / 4
  | 9 => 129237
  | 10 => 129263
  | 11 => 129289
  | 12 => 129316
  | 13 => 129342
  | 14 => 129368
  | 15 => 129395
  | 16 => 517683 / 4
  | 17 => 129447
  | 18 => 129474
  | 19 => 129500
  | 20 => 129526
  | 21 => 129553
  | 22 => 129579
  | 23 => 129605
  | 24 => 129632
  | 25 => 518631 / 4
  | 26 => 129684
  | 27 => 129711
  | 28 => 129737
  | 29 => 129763
  | 30 => 519155 / 4
  | 31 => 129816
  | 32 => 129842
  | 33 => 129868
  | 34 => 129895
  | 35 => 129921
  | 36 => 519787 / 4
  | 37 => 129974
  | _ => 129974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 516105 / 4
  | 1 => 129053
  | 2 => 129079
  | 3 => 129105
  | 4 => 129132
  | 5 => 129158
  | 6 => 129184
  | 7 => 129211
  | 8 => 129237
  | 9 => 129263
  | 10 => 129289
  | 11 => 129316
  | 12 => 129342
  | 13 => 129368
  | 14 => 129395
  | 15 => 129421
  | 16 => 129447
  | 17 => 129474
  | 18 => 129500
  | 19 => 129526
  | 20 => 129553
  | 21 => 129579
  | 22 => 129605
  | 23 => 129632
  | 24 => 129658
  | 25 => 129684
  | 26 => 129711
  | 27 => 129737
  | 28 => 519053 / 4
  | 29 => 129789
  | 30 => 129816
  | 31 => 519369 / 4
  | 32 => 129868
  | 33 => 519581 / 4
  | 34 => 129921
  | 35 => 129947
  | 36 => 519897 / 4
  | 37 => 520001 / 4
  | _ => 520001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 130000` (`log 130000 ≤ 12`, `2.7^12 ≥ 130000`). -/
theorem haC_130000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 130000 := by
  have hlog : Real.log 130000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 130000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 130000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[129000, 130000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[129000, 130000]` SEGMENT: every zero with `129000 ≤ Im ≤ 130000` is on the line. -/
theorem segment_129000_130000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 130000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (129000:ℝ) ≤ ρ.im → ρ.im ≤ 130000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 129000 130000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_130000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 130000 via the HEIGHT CHAIN**: `[0,129000]` ∘ `[129000,130000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_130000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 130000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 130000 → ρ.re = 1 / 2 := by
  have hγ129000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 129000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 129000 130000
    (AllZeros_h129000.all_nontrivial_zeros_up_to_height_129000_of_bands
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
      hγ129000)
    (segment_129000_130000 hbands hγ)

end AllZeros_h130000

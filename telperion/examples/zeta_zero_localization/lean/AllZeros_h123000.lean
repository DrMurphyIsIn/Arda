/-  Height-chain step: all nontrivial zeta zeros up to height 123000 on Re = 1/2 --
    `AllZeros_h122000` + a `[122000, 123000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h122000
import RHInBoxT_1d4000000_3999999d4000000_122000_488105d4
import RHInBoxT_1d4000000_3999999d4000000_122026_122053
import RHInBoxT_1d4000000_3999999d4000000_122053_122079
import RHInBoxT_1d4000000_3999999d4000000_122079_122105
import RHInBoxT_1d4000000_3999999d4000000_122105_122132
import RHInBoxT_1d4000000_3999999d4000000_122132_122158
import RHInBoxT_1d4000000_3999999d4000000_122158_122184
import RHInBoxT_1d4000000_3999999d4000000_122184_122211
import RHInBoxT_1d4000000_3999999d4000000_122211_122237
import RHInBoxT_1d4000000_3999999d4000000_122237_122263
import RHInBoxT_1d4000000_3999999d4000000_122263_489157d4
import RHInBoxT_1d4000000_3999999d4000000_122289_122316
import RHInBoxT_1d4000000_3999999d4000000_122316_122342
import RHInBoxT_1d4000000_3999999d4000000_122342_122368
import RHInBoxT_1d4000000_3999999d4000000_489471d4_489581d4
import RHInBoxT_1d4000000_3999999d4000000_122395_122421
import RHInBoxT_1d4000000_3999999d4000000_122421_122447
import RHInBoxT_1d4000000_3999999d4000000_122447_489897d4
import RHInBoxT_1d4000000_3999999d4000000_122474_490001d4
import RHInBoxT_1d4000000_3999999d4000000_122500_122526
import RHInBoxT_1d4000000_3999999d4000000_122526_122553
import RHInBoxT_1d4000000_3999999d4000000_122553_122579
import RHInBoxT_1d4000000_3999999d4000000_122579_490421d4
import RHInBoxT_1d4000000_3999999d4000000_122605_490529d4
import RHInBoxT_1d4000000_3999999d4000000_122632_122658
import RHInBoxT_1d4000000_3999999d4000000_122658_490737d4
import RHInBoxT_1d4000000_3999999d4000000_122684_122711
import RHInBoxT_1d4000000_3999999d4000000_122711_122737
import RHInBoxT_1d4000000_3999999d4000000_122737_122763
import RHInBoxT_1d4000000_3999999d4000000_122763_122789
import RHInBoxT_1d4000000_3999999d4000000_122789_122816
import RHInBoxT_1d4000000_3999999d4000000_122816_122842
import RHInBoxT_1d4000000_3999999d4000000_491367d4_122868
import RHInBoxT_1d4000000_3999999d4000000_122868_491581d4
import RHInBoxT_1d4000000_3999999d4000000_122895_122921
import RHInBoxT_1d4000000_3999999d4000000_122921_122947
import RHInBoxT_1d4000000_3999999d4000000_122947_122974
import RHInBoxT_1d4000000_3999999d4000000_122974_492001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h123000

/-- The 38-band NOMINAL partition of `[122000, 123000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 122000
  | 1 => 122026
  | 2 => 122053
  | 3 => 122079
  | 4 => 122105
  | 5 => 122132
  | 6 => 122158
  | 7 => 122184
  | 8 => 122211
  | 9 => 122237
  | 10 => 122263
  | 11 => 122289
  | 12 => 122316
  | 13 => 122342
  | 14 => 122368
  | 15 => 122395
  | 16 => 122421
  | 17 => 122447
  | 18 => 122474
  | 19 => 122500
  | 20 => 122526
  | 21 => 122553
  | 22 => 122579
  | 23 => 122605
  | 24 => 122632
  | 25 => 122658
  | 26 => 122684
  | 27 => 122711
  | 28 => 122737
  | 29 => 122763
  | 30 => 122789
  | 31 => 122816
  | 32 => 122842
  | 33 => 122868
  | 34 => 122895
  | 35 => 122921
  | 36 => 122947
  | 37 => 122974
  | 38 => 123000
  | _ => 123000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((122000:ℝ)) ≤ (122026); norm_num
  · show ((122026:ℝ)) ≤ (122053); norm_num
  · show ((122053:ℝ)) ≤ (122079); norm_num
  · show ((122079:ℝ)) ≤ (122105); norm_num
  · show ((122105:ℝ)) ≤ (122132); norm_num
  · show ((122132:ℝ)) ≤ (122158); norm_num
  · show ((122158:ℝ)) ≤ (122184); norm_num
  · show ((122184:ℝ)) ≤ (122211); norm_num
  · show ((122211:ℝ)) ≤ (122237); norm_num
  · show ((122237:ℝ)) ≤ (122263); norm_num
  · show ((122263:ℝ)) ≤ (122289); norm_num
  · show ((122289:ℝ)) ≤ (122316); norm_num
  · show ((122316:ℝ)) ≤ (122342); norm_num
  · show ((122342:ℝ)) ≤ (122368); norm_num
  · show ((122368:ℝ)) ≤ (122395); norm_num
  · show ((122395:ℝ)) ≤ (122421); norm_num
  · show ((122421:ℝ)) ≤ (122447); norm_num
  · show ((122447:ℝ)) ≤ (122474); norm_num
  · show ((122474:ℝ)) ≤ (122500); norm_num
  · show ((122500:ℝ)) ≤ (122526); norm_num
  · show ((122526:ℝ)) ≤ (122553); norm_num
  · show ((122553:ℝ)) ≤ (122579); norm_num
  · show ((122579:ℝ)) ≤ (122605); norm_num
  · show ((122605:ℝ)) ≤ (122632); norm_num
  · show ((122632:ℝ)) ≤ (122658); norm_num
  · show ((122658:ℝ)) ≤ (122684); norm_num
  · show ((122684:ℝ)) ≤ (122711); norm_num
  · show ((122711:ℝ)) ≤ (122737); norm_num
  · show ((122737:ℝ)) ≤ (122763); norm_num
  · show ((122763:ℝ)) ≤ (122789); norm_num
  · show ((122789:ℝ)) ≤ (122816); norm_num
  · show ((122816:ℝ)) ≤ (122842); norm_num
  · show ((122842:ℝ)) ≤ (122868); norm_num
  · show ((122868:ℝ)) ≤ (122895); norm_num
  · show ((122895:ℝ)) ≤ (122921); norm_num
  · show ((122921:ℝ)) ≤ (122947); norm_num
  · show ((122947:ℝ)) ≤ (122974); norm_num
  · show ((122974:ℝ)) ≤ (123000); norm_num
  · show ((123000:ℝ)) ≤ (123000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 122000
  | 1 => 122026
  | 2 => 122053
  | 3 => 122079
  | 4 => 122105
  | 5 => 122132
  | 6 => 122158
  | 7 => 122184
  | 8 => 122211
  | 9 => 122237
  | 10 => 122263
  | 11 => 122289
  | 12 => 122316
  | 13 => 122342
  | 14 => 489471 / 4
  | 15 => 122395
  | 16 => 122421
  | 17 => 122447
  | 18 => 122474
  | 19 => 122500
  | 20 => 122526
  | 21 => 122553
  | 22 => 122579
  | 23 => 122605
  | 24 => 122632
  | 25 => 122658
  | 26 => 122684
  | 27 => 122711
  | 28 => 122737
  | 29 => 122763
  | 30 => 122789
  | 31 => 122816
  | 32 => 491367 / 4
  | 33 => 122868
  | 34 => 122895
  | 35 => 122921
  | 36 => 122947
  | 37 => 122974
  | _ => 122974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 488105 / 4
  | 1 => 122053
  | 2 => 122079
  | 3 => 122105
  | 4 => 122132
  | 5 => 122158
  | 6 => 122184
  | 7 => 122211
  | 8 => 122237
  | 9 => 122263
  | 10 => 489157 / 4
  | 11 => 122316
  | 12 => 122342
  | 13 => 122368
  | 14 => 489581 / 4
  | 15 => 122421
  | 16 => 122447
  | 17 => 489897 / 4
  | 18 => 490001 / 4
  | 19 => 122526
  | 20 => 122553
  | 21 => 122579
  | 22 => 490421 / 4
  | 23 => 490529 / 4
  | 24 => 122658
  | 25 => 490737 / 4
  | 26 => 122711
  | 27 => 122737
  | 28 => 122763
  | 29 => 122789
  | 30 => 122816
  | 31 => 122842
  | 32 => 122868
  | 33 => 491581 / 4
  | 34 => 122921
  | 35 => 122947
  | 36 => 122974
  | 37 => 492001 / 4
  | _ => 492001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 123000` (`log 123000 ≤ 12`, `2.7^12 ≥ 123000`). -/
theorem haC_123000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 123000 := by
  have hlog : Real.log 123000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 123000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 123000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[122000, 123000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[122000, 123000]` SEGMENT: every zero with `122000 ≤ Im ≤ 123000` is on the line. -/
theorem segment_122000_123000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 123000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (122000:ℝ) ≤ ρ.im → ρ.im ≤ 123000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 122000 123000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_123000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 123000 via the HEIGHT CHAIN**: `[0,122000]` ∘ `[122000,123000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_123000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 123000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 123000 → ρ.re = 1 / 2 := by
  have hγ122000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 122000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 122000 123000
    (AllZeros_h122000.all_nontrivial_zeros_up_to_height_122000_of_bands
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
      hγ122000)
    (segment_122000_123000 hbands hγ)

end AllZeros_h123000

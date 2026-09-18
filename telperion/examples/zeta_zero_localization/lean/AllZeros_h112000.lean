/-  Height-chain step: all nontrivial zeta zeros up to height 112000 on Re = 1/2 --
    `AllZeros_h111000` + a `[111000, 112000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h111000
import RHInBoxT_1d4000000_3999999d4000000_111000_111026
import RHInBoxT_1d4000000_3999999d4000000_111026_111053
import RHInBoxT_1d4000000_3999999d4000000_111053_111079
import RHInBoxT_1d4000000_3999999d4000000_111079_111105
import RHInBoxT_1d4000000_3999999d4000000_111105_111132
import RHInBoxT_1d4000000_3999999d4000000_111132_111158
import RHInBoxT_1d4000000_3999999d4000000_111158_111184
import RHInBoxT_1d4000000_3999999d4000000_111184_111211
import RHInBoxT_1d4000000_3999999d4000000_444843d4_111237
import RHInBoxT_1d4000000_3999999d4000000_111237_111263
import RHInBoxT_1d4000000_3999999d4000000_111263_111289
import RHInBoxT_1d4000000_3999999d4000000_111289_445265d4
import RHInBoxT_1d4000000_3999999d4000000_111316_111342
import RHInBoxT_1d4000000_3999999d4000000_111342_111368
import RHInBoxT_1d4000000_3999999d4000000_111368_111395
import RHInBoxT_1d4000000_3999999d4000000_111395_111421
import RHInBoxT_1d4000000_3999999d4000000_111421_111447
import RHInBoxT_1d4000000_3999999d4000000_111447_111474
import RHInBoxT_1d4000000_3999999d4000000_111474_111500
import RHInBoxT_1d4000000_3999999d4000000_445999d4_111526
import RHInBoxT_1d4000000_3999999d4000000_111526_111553
import RHInBoxT_1d4000000_3999999d4000000_111553_111579
import RHInBoxT_1d4000000_3999999d4000000_111579_111605
import RHInBoxT_1d4000000_3999999d4000000_111605_111632
import RHInBoxT_1d4000000_3999999d4000000_111632_446633d4
import RHInBoxT_1d4000000_3999999d4000000_111658_111684
import RHInBoxT_1d4000000_3999999d4000000_111684_111711
import RHInBoxT_1d4000000_3999999d4000000_111711_111737
import RHInBoxT_1d4000000_3999999d4000000_111737_111763
import RHInBoxT_1d4000000_3999999d4000000_111763_111789
import RHInBoxT_1d4000000_3999999d4000000_111789_111816
import RHInBoxT_1d4000000_3999999d4000000_111816_447369d4
import RHInBoxT_1d4000000_3999999d4000000_111842_111868
import RHInBoxT_1d4000000_3999999d4000000_111868_447581d4
import RHInBoxT_1d4000000_3999999d4000000_111895_111921
import RHInBoxT_1d4000000_3999999d4000000_111921_111947
import RHInBoxT_1d4000000_3999999d4000000_111947_111974
import RHInBoxT_1d4000000_3999999d4000000_111974_112000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h112000

/-- The 38-band NOMINAL partition of `[111000, 112000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 111000
  | 1 => 111026
  | 2 => 111053
  | 3 => 111079
  | 4 => 111105
  | 5 => 111132
  | 6 => 111158
  | 7 => 111184
  | 8 => 111211
  | 9 => 111237
  | 10 => 111263
  | 11 => 111289
  | 12 => 111316
  | 13 => 111342
  | 14 => 111368
  | 15 => 111395
  | 16 => 111421
  | 17 => 111447
  | 18 => 111474
  | 19 => 111500
  | 20 => 111526
  | 21 => 111553
  | 22 => 111579
  | 23 => 111605
  | 24 => 111632
  | 25 => 111658
  | 26 => 111684
  | 27 => 111711
  | 28 => 111737
  | 29 => 111763
  | 30 => 111789
  | 31 => 111816
  | 32 => 111842
  | 33 => 111868
  | 34 => 111895
  | 35 => 111921
  | 36 => 111947
  | 37 => 111974
  | 38 => 112000
  | _ => 112000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((111000:ℝ)) ≤ (111026); norm_num
  · show ((111026:ℝ)) ≤ (111053); norm_num
  · show ((111053:ℝ)) ≤ (111079); norm_num
  · show ((111079:ℝ)) ≤ (111105); norm_num
  · show ((111105:ℝ)) ≤ (111132); norm_num
  · show ((111132:ℝ)) ≤ (111158); norm_num
  · show ((111158:ℝ)) ≤ (111184); norm_num
  · show ((111184:ℝ)) ≤ (111211); norm_num
  · show ((111211:ℝ)) ≤ (111237); norm_num
  · show ((111237:ℝ)) ≤ (111263); norm_num
  · show ((111263:ℝ)) ≤ (111289); norm_num
  · show ((111289:ℝ)) ≤ (111316); norm_num
  · show ((111316:ℝ)) ≤ (111342); norm_num
  · show ((111342:ℝ)) ≤ (111368); norm_num
  · show ((111368:ℝ)) ≤ (111395); norm_num
  · show ((111395:ℝ)) ≤ (111421); norm_num
  · show ((111421:ℝ)) ≤ (111447); norm_num
  · show ((111447:ℝ)) ≤ (111474); norm_num
  · show ((111474:ℝ)) ≤ (111500); norm_num
  · show ((111500:ℝ)) ≤ (111526); norm_num
  · show ((111526:ℝ)) ≤ (111553); norm_num
  · show ((111553:ℝ)) ≤ (111579); norm_num
  · show ((111579:ℝ)) ≤ (111605); norm_num
  · show ((111605:ℝ)) ≤ (111632); norm_num
  · show ((111632:ℝ)) ≤ (111658); norm_num
  · show ((111658:ℝ)) ≤ (111684); norm_num
  · show ((111684:ℝ)) ≤ (111711); norm_num
  · show ((111711:ℝ)) ≤ (111737); norm_num
  · show ((111737:ℝ)) ≤ (111763); norm_num
  · show ((111763:ℝ)) ≤ (111789); norm_num
  · show ((111789:ℝ)) ≤ (111816); norm_num
  · show ((111816:ℝ)) ≤ (111842); norm_num
  · show ((111842:ℝ)) ≤ (111868); norm_num
  · show ((111868:ℝ)) ≤ (111895); norm_num
  · show ((111895:ℝ)) ≤ (111921); norm_num
  · show ((111921:ℝ)) ≤ (111947); norm_num
  · show ((111947:ℝ)) ≤ (111974); norm_num
  · show ((111974:ℝ)) ≤ (112000); norm_num
  · show ((112000:ℝ)) ≤ (112000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 111000
  | 1 => 111026
  | 2 => 111053
  | 3 => 111079
  | 4 => 111105
  | 5 => 111132
  | 6 => 111158
  | 7 => 111184
  | 8 => 444843 / 4
  | 9 => 111237
  | 10 => 111263
  | 11 => 111289
  | 12 => 111316
  | 13 => 111342
  | 14 => 111368
  | 15 => 111395
  | 16 => 111421
  | 17 => 111447
  | 18 => 111474
  | 19 => 445999 / 4
  | 20 => 111526
  | 21 => 111553
  | 22 => 111579
  | 23 => 111605
  | 24 => 111632
  | 25 => 111658
  | 26 => 111684
  | 27 => 111711
  | 28 => 111737
  | 29 => 111763
  | 30 => 111789
  | 31 => 111816
  | 32 => 111842
  | 33 => 111868
  | 34 => 111895
  | 35 => 111921
  | 36 => 111947
  | 37 => 111974
  | _ => 111974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 111026
  | 1 => 111053
  | 2 => 111079
  | 3 => 111105
  | 4 => 111132
  | 5 => 111158
  | 6 => 111184
  | 7 => 111211
  | 8 => 111237
  | 9 => 111263
  | 10 => 111289
  | 11 => 445265 / 4
  | 12 => 111342
  | 13 => 111368
  | 14 => 111395
  | 15 => 111421
  | 16 => 111447
  | 17 => 111474
  | 18 => 111500
  | 19 => 111526
  | 20 => 111553
  | 21 => 111579
  | 22 => 111605
  | 23 => 111632
  | 24 => 446633 / 4
  | 25 => 111684
  | 26 => 111711
  | 27 => 111737
  | 28 => 111763
  | 29 => 111789
  | 30 => 111816
  | 31 => 447369 / 4
  | 32 => 111868
  | 33 => 447581 / 4
  | 34 => 111921
  | 35 => 111947
  | 36 => 111974
  | 37 => 112000
  | _ => 112000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 112000` (`log 112000 ≤ 12`, `2.7^12 ≥ 112000`). -/
theorem haC_112000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 112000 := by
  have hlog : Real.log 112000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 112000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 112000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[111000, 112000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[111000, 112000]` SEGMENT: every zero with `111000 ≤ Im ≤ 112000` is on the line. -/
theorem segment_111000_112000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 112000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (111000:ℝ) ≤ ρ.im → ρ.im ≤ 112000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 111000 112000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_112000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 112000 via the HEIGHT CHAIN**: `[0,111000]` ∘ `[111000,112000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_112000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 112000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 112000 → ρ.re = 1 / 2 := by
  have hγ111000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 111000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 111000 112000
    (AllZeros_h111000.all_nontrivial_zeros_up_to_height_111000_of_bands
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
      hγ111000)
    (segment_111000_112000 hbands hγ)

end AllZeros_h112000

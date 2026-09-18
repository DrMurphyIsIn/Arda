/-  Height-chain step: all nontrivial zeta zeros up to height 117000 on Re = 1/2 --
    `AllZeros_h116000` + a `[116000, 117000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h116000
import RHInBoxT_1d4000000_3999999d4000000_463999d4_116026
import RHInBoxT_1d4000000_3999999d4000000_116026_116053
import RHInBoxT_1d4000000_3999999d4000000_116053_116079
import RHInBoxT_1d4000000_3999999d4000000_116079_116105
import RHInBoxT_1d4000000_3999999d4000000_116105_464529d4
import RHInBoxT_1d4000000_3999999d4000000_116132_116158
import RHInBoxT_1d4000000_3999999d4000000_116158_116184
import RHInBoxT_1d4000000_3999999d4000000_116184_464845d4
import RHInBoxT_1d4000000_3999999d4000000_116211_116237
import RHInBoxT_1d4000000_3999999d4000000_116237_116263
import RHInBoxT_1d4000000_3999999d4000000_116263_116289
import RHInBoxT_1d4000000_3999999d4000000_465155d4_116316
import RHInBoxT_1d4000000_3999999d4000000_465263d4_116342
import RHInBoxT_1d4000000_3999999d4000000_116342_116368
import RHInBoxT_1d4000000_3999999d4000000_116368_116395
import RHInBoxT_1d4000000_3999999d4000000_116395_116421
import RHInBoxT_1d4000000_3999999d4000000_465683d4_116447
import RHInBoxT_1d4000000_3999999d4000000_116447_116474
import RHInBoxT_1d4000000_3999999d4000000_465895d4_116500
import RHInBoxT_1d4000000_3999999d4000000_116500_466105d4
import RHInBoxT_1d4000000_3999999d4000000_116526_116553
import RHInBoxT_1d4000000_3999999d4000000_116553_116579
import RHInBoxT_1d4000000_3999999d4000000_116579_233211d2
import RHInBoxT_1d4000000_3999999d4000000_116605_116632
import RHInBoxT_1d4000000_3999999d4000000_116632_116658
import RHInBoxT_1d4000000_3999999d4000000_116658_116684
import RHInBoxT_1d4000000_3999999d4000000_466735d4_466845d4
import RHInBoxT_1d4000000_3999999d4000000_116711_116737
import RHInBoxT_1d4000000_3999999d4000000_116737_116763
import RHInBoxT_1d4000000_3999999d4000000_116763_116789
import RHInBoxT_1d4000000_3999999d4000000_116789_116816
import RHInBoxT_1d4000000_3999999d4000000_467263d4_116842
import RHInBoxT_1d4000000_3999999d4000000_116842_116868
import RHInBoxT_1d4000000_3999999d4000000_116868_116895
import RHInBoxT_1d4000000_3999999d4000000_116895_116921
import RHInBoxT_1d4000000_3999999d4000000_116921_116947
import RHInBoxT_1d4000000_3999999d4000000_116947_116974
import RHInBoxT_1d4000000_3999999d4000000_116974_117000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h117000

/-- The 38-band NOMINAL partition of `[116000, 117000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 116000
  | 1 => 116026
  | 2 => 116053
  | 3 => 116079
  | 4 => 116105
  | 5 => 116132
  | 6 => 116158
  | 7 => 116184
  | 8 => 116211
  | 9 => 116237
  | 10 => 116263
  | 11 => 116289
  | 12 => 116316
  | 13 => 116342
  | 14 => 116368
  | 15 => 116395
  | 16 => 116421
  | 17 => 116447
  | 18 => 116474
  | 19 => 116500
  | 20 => 116526
  | 21 => 116553
  | 22 => 116579
  | 23 => 116605
  | 24 => 116632
  | 25 => 116658
  | 26 => 116684
  | 27 => 116711
  | 28 => 116737
  | 29 => 116763
  | 30 => 116789
  | 31 => 116816
  | 32 => 116842
  | 33 => 116868
  | 34 => 116895
  | 35 => 116921
  | 36 => 116947
  | 37 => 116974
  | 38 => 117000
  | _ => 117000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((116000:ℝ)) ≤ (116026); norm_num
  · show ((116026:ℝ)) ≤ (116053); norm_num
  · show ((116053:ℝ)) ≤ (116079); norm_num
  · show ((116079:ℝ)) ≤ (116105); norm_num
  · show ((116105:ℝ)) ≤ (116132); norm_num
  · show ((116132:ℝ)) ≤ (116158); norm_num
  · show ((116158:ℝ)) ≤ (116184); norm_num
  · show ((116184:ℝ)) ≤ (116211); norm_num
  · show ((116211:ℝ)) ≤ (116237); norm_num
  · show ((116237:ℝ)) ≤ (116263); norm_num
  · show ((116263:ℝ)) ≤ (116289); norm_num
  · show ((116289:ℝ)) ≤ (116316); norm_num
  · show ((116316:ℝ)) ≤ (116342); norm_num
  · show ((116342:ℝ)) ≤ (116368); norm_num
  · show ((116368:ℝ)) ≤ (116395); norm_num
  · show ((116395:ℝ)) ≤ (116421); norm_num
  · show ((116421:ℝ)) ≤ (116447); norm_num
  · show ((116447:ℝ)) ≤ (116474); norm_num
  · show ((116474:ℝ)) ≤ (116500); norm_num
  · show ((116500:ℝ)) ≤ (116526); norm_num
  · show ((116526:ℝ)) ≤ (116553); norm_num
  · show ((116553:ℝ)) ≤ (116579); norm_num
  · show ((116579:ℝ)) ≤ (116605); norm_num
  · show ((116605:ℝ)) ≤ (116632); norm_num
  · show ((116632:ℝ)) ≤ (116658); norm_num
  · show ((116658:ℝ)) ≤ (116684); norm_num
  · show ((116684:ℝ)) ≤ (116711); norm_num
  · show ((116711:ℝ)) ≤ (116737); norm_num
  · show ((116737:ℝ)) ≤ (116763); norm_num
  · show ((116763:ℝ)) ≤ (116789); norm_num
  · show ((116789:ℝ)) ≤ (116816); norm_num
  · show ((116816:ℝ)) ≤ (116842); norm_num
  · show ((116842:ℝ)) ≤ (116868); norm_num
  · show ((116868:ℝ)) ≤ (116895); norm_num
  · show ((116895:ℝ)) ≤ (116921); norm_num
  · show ((116921:ℝ)) ≤ (116947); norm_num
  · show ((116947:ℝ)) ≤ (116974); norm_num
  · show ((116974:ℝ)) ≤ (117000); norm_num
  · show ((117000:ℝ)) ≤ (117000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 463999 / 4
  | 1 => 116026
  | 2 => 116053
  | 3 => 116079
  | 4 => 116105
  | 5 => 116132
  | 6 => 116158
  | 7 => 116184
  | 8 => 116211
  | 9 => 116237
  | 10 => 116263
  | 11 => 465155 / 4
  | 12 => 465263 / 4
  | 13 => 116342
  | 14 => 116368
  | 15 => 116395
  | 16 => 465683 / 4
  | 17 => 116447
  | 18 => 465895 / 4
  | 19 => 116500
  | 20 => 116526
  | 21 => 116553
  | 22 => 116579
  | 23 => 116605
  | 24 => 116632
  | 25 => 116658
  | 26 => 466735 / 4
  | 27 => 116711
  | 28 => 116737
  | 29 => 116763
  | 30 => 116789
  | 31 => 467263 / 4
  | 32 => 116842
  | 33 => 116868
  | 34 => 116895
  | 35 => 116921
  | 36 => 116947
  | 37 => 116974
  | _ => 116974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 116026
  | 1 => 116053
  | 2 => 116079
  | 3 => 116105
  | 4 => 464529 / 4
  | 5 => 116158
  | 6 => 116184
  | 7 => 464845 / 4
  | 8 => 116237
  | 9 => 116263
  | 10 => 116289
  | 11 => 116316
  | 12 => 116342
  | 13 => 116368
  | 14 => 116395
  | 15 => 116421
  | 16 => 116447
  | 17 => 116474
  | 18 => 116500
  | 19 => 466105 / 4
  | 20 => 116553
  | 21 => 116579
  | 22 => 233211 / 2
  | 23 => 116632
  | 24 => 116658
  | 25 => 116684
  | 26 => 466845 / 4
  | 27 => 116737
  | 28 => 116763
  | 29 => 116789
  | 30 => 116816
  | 31 => 116842
  | 32 => 116868
  | 33 => 116895
  | 34 => 116921
  | 35 => 116947
  | 36 => 116974
  | 37 => 117000
  | _ => 117000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 117000` (`log 117000 ≤ 12`, `2.7^12 ≥ 117000`). -/
theorem haC_117000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 117000 := by
  have hlog : Real.log 117000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 117000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 117000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[116000, 117000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[116000, 117000]` SEGMENT: every zero with `116000 ≤ Im ≤ 117000` is on the line. -/
theorem segment_116000_117000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 117000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (116000:ℝ) ≤ ρ.im → ρ.im ≤ 117000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 116000 117000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_117000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 117000 via the HEIGHT CHAIN**: `[0,116000]` ∘ `[116000,117000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_117000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 117000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 117000 → ρ.re = 1 / 2 := by
  have hγ116000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 116000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 116000 117000
    (AllZeros_h116000.all_nontrivial_zeros_up_to_height_116000_of_bands
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
      hγ116000)
    (segment_116000_117000 hbands hγ)

end AllZeros_h117000

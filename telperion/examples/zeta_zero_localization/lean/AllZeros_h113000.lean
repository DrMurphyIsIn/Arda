/-  Height-chain step: all nontrivial zeta zeros up to height 113000 on Re = 1/2 --
    `AllZeros_h112000` + a `[112000, 113000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h112000
import RHInBoxT_1d4000000_3999999d4000000_112000_112026
import RHInBoxT_1d4000000_3999999d4000000_112026_448213d4
import RHInBoxT_1d4000000_3999999d4000000_112053_112079
import RHInBoxT_1d4000000_3999999d4000000_112079_112105
import RHInBoxT_1d4000000_3999999d4000000_112105_112132
import RHInBoxT_1d4000000_3999999d4000000_112132_112158
import RHInBoxT_1d4000000_3999999d4000000_112158_112184
import RHInBoxT_1d4000000_3999999d4000000_112184_112211
import RHInBoxT_1d4000000_3999999d4000000_112211_112237
import RHInBoxT_1d4000000_3999999d4000000_112237_112263
import RHInBoxT_1d4000000_3999999d4000000_112263_112289
import RHInBoxT_1d4000000_3999999d4000000_112289_449265d4
import RHInBoxT_1d4000000_3999999d4000000_112316_112342
import RHInBoxT_1d4000000_3999999d4000000_112342_112368
import RHInBoxT_1d4000000_3999999d4000000_112368_112395
import RHInBoxT_1d4000000_3999999d4000000_112395_112421
import RHInBoxT_1d4000000_3999999d4000000_112421_112447
import RHInBoxT_1d4000000_3999999d4000000_112447_112474
import RHInBoxT_1d4000000_3999999d4000000_112474_112500
import RHInBoxT_1d4000000_3999999d4000000_112500_112526
import RHInBoxT_1d4000000_3999999d4000000_112526_112553
import RHInBoxT_1d4000000_3999999d4000000_450211d4_112579
import RHInBoxT_1d4000000_3999999d4000000_450315d4_112605
import RHInBoxT_1d4000000_3999999d4000000_112605_112632
import RHInBoxT_1d4000000_3999999d4000000_112632_450633d4
import RHInBoxT_1d4000000_3999999d4000000_112658_112684
import RHInBoxT_1d4000000_3999999d4000000_450735d4_112711
import RHInBoxT_1d4000000_3999999d4000000_112711_112737
import RHInBoxT_1d4000000_3999999d4000000_112737_112763
import RHInBoxT_1d4000000_3999999d4000000_112763_112789
import RHInBoxT_1d4000000_3999999d4000000_112789_112816
import RHInBoxT_1d4000000_3999999d4000000_112816_112842
import RHInBoxT_1d4000000_3999999d4000000_112842_112868
import RHInBoxT_1d4000000_3999999d4000000_225735d2_112895
import RHInBoxT_1d4000000_3999999d4000000_112895_112921
import RHInBoxT_1d4000000_3999999d4000000_112921_112947
import RHInBoxT_1d4000000_3999999d4000000_112947_112974
import RHInBoxT_1d4000000_3999999d4000000_112974_452001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h113000

/-- The 38-band NOMINAL partition of `[112000, 113000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 112000
  | 1 => 112026
  | 2 => 112053
  | 3 => 112079
  | 4 => 112105
  | 5 => 112132
  | 6 => 112158
  | 7 => 112184
  | 8 => 112211
  | 9 => 112237
  | 10 => 112263
  | 11 => 112289
  | 12 => 112316
  | 13 => 112342
  | 14 => 112368
  | 15 => 112395
  | 16 => 112421
  | 17 => 112447
  | 18 => 112474
  | 19 => 112500
  | 20 => 112526
  | 21 => 112553
  | 22 => 112579
  | 23 => 112605
  | 24 => 112632
  | 25 => 112658
  | 26 => 112684
  | 27 => 112711
  | 28 => 112737
  | 29 => 112763
  | 30 => 112789
  | 31 => 112816
  | 32 => 112842
  | 33 => 112868
  | 34 => 112895
  | 35 => 112921
  | 36 => 112947
  | 37 => 112974
  | 38 => 113000
  | _ => 113000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((112000:ℝ)) ≤ (112026); norm_num
  · show ((112026:ℝ)) ≤ (112053); norm_num
  · show ((112053:ℝ)) ≤ (112079); norm_num
  · show ((112079:ℝ)) ≤ (112105); norm_num
  · show ((112105:ℝ)) ≤ (112132); norm_num
  · show ((112132:ℝ)) ≤ (112158); norm_num
  · show ((112158:ℝ)) ≤ (112184); norm_num
  · show ((112184:ℝ)) ≤ (112211); norm_num
  · show ((112211:ℝ)) ≤ (112237); norm_num
  · show ((112237:ℝ)) ≤ (112263); norm_num
  · show ((112263:ℝ)) ≤ (112289); norm_num
  · show ((112289:ℝ)) ≤ (112316); norm_num
  · show ((112316:ℝ)) ≤ (112342); norm_num
  · show ((112342:ℝ)) ≤ (112368); norm_num
  · show ((112368:ℝ)) ≤ (112395); norm_num
  · show ((112395:ℝ)) ≤ (112421); norm_num
  · show ((112421:ℝ)) ≤ (112447); norm_num
  · show ((112447:ℝ)) ≤ (112474); norm_num
  · show ((112474:ℝ)) ≤ (112500); norm_num
  · show ((112500:ℝ)) ≤ (112526); norm_num
  · show ((112526:ℝ)) ≤ (112553); norm_num
  · show ((112553:ℝ)) ≤ (112579); norm_num
  · show ((112579:ℝ)) ≤ (112605); norm_num
  · show ((112605:ℝ)) ≤ (112632); norm_num
  · show ((112632:ℝ)) ≤ (112658); norm_num
  · show ((112658:ℝ)) ≤ (112684); norm_num
  · show ((112684:ℝ)) ≤ (112711); norm_num
  · show ((112711:ℝ)) ≤ (112737); norm_num
  · show ((112737:ℝ)) ≤ (112763); norm_num
  · show ((112763:ℝ)) ≤ (112789); norm_num
  · show ((112789:ℝ)) ≤ (112816); norm_num
  · show ((112816:ℝ)) ≤ (112842); norm_num
  · show ((112842:ℝ)) ≤ (112868); norm_num
  · show ((112868:ℝ)) ≤ (112895); norm_num
  · show ((112895:ℝ)) ≤ (112921); norm_num
  · show ((112921:ℝ)) ≤ (112947); norm_num
  · show ((112947:ℝ)) ≤ (112974); norm_num
  · show ((112974:ℝ)) ≤ (113000); norm_num
  · show ((113000:ℝ)) ≤ (113000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 112000
  | 1 => 112026
  | 2 => 112053
  | 3 => 112079
  | 4 => 112105
  | 5 => 112132
  | 6 => 112158
  | 7 => 112184
  | 8 => 112211
  | 9 => 112237
  | 10 => 112263
  | 11 => 112289
  | 12 => 112316
  | 13 => 112342
  | 14 => 112368
  | 15 => 112395
  | 16 => 112421
  | 17 => 112447
  | 18 => 112474
  | 19 => 112500
  | 20 => 112526
  | 21 => 450211 / 4
  | 22 => 450315 / 4
  | 23 => 112605
  | 24 => 112632
  | 25 => 112658
  | 26 => 450735 / 4
  | 27 => 112711
  | 28 => 112737
  | 29 => 112763
  | 30 => 112789
  | 31 => 112816
  | 32 => 112842
  | 33 => 225735 / 2
  | 34 => 112895
  | 35 => 112921
  | 36 => 112947
  | 37 => 112974
  | _ => 112974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 112026
  | 1 => 448213 / 4
  | 2 => 112079
  | 3 => 112105
  | 4 => 112132
  | 5 => 112158
  | 6 => 112184
  | 7 => 112211
  | 8 => 112237
  | 9 => 112263
  | 10 => 112289
  | 11 => 449265 / 4
  | 12 => 112342
  | 13 => 112368
  | 14 => 112395
  | 15 => 112421
  | 16 => 112447
  | 17 => 112474
  | 18 => 112500
  | 19 => 112526
  | 20 => 112553
  | 21 => 112579
  | 22 => 112605
  | 23 => 112632
  | 24 => 450633 / 4
  | 25 => 112684
  | 26 => 112711
  | 27 => 112737
  | 28 => 112763
  | 29 => 112789
  | 30 => 112816
  | 31 => 112842
  | 32 => 112868
  | 33 => 112895
  | 34 => 112921
  | 35 => 112947
  | 36 => 112974
  | 37 => 452001 / 4
  | _ => 452001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 113000` (`log 113000 ≤ 12`, `2.7^12 ≥ 113000`). -/
theorem haC_113000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 113000 := by
  have hlog : Real.log 113000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 113000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 113000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[112000, 113000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[112000, 113000]` SEGMENT: every zero with `112000 ≤ Im ≤ 113000` is on the line. -/
theorem segment_112000_113000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 113000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (112000:ℝ) ≤ ρ.im → ρ.im ≤ 113000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 112000 113000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_113000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 113000 via the HEIGHT CHAIN**: `[0,112000]` ∘ `[112000,113000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_113000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 113000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 113000 → ρ.re = 1 / 2 := by
  have hγ112000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 112000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 112000 113000
    (AllZeros_h112000.all_nontrivial_zeros_up_to_height_112000_of_bands
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
      hγ112000)
    (segment_112000_113000 hbands hγ)

end AllZeros_h113000

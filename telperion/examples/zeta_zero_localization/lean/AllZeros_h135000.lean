/-  Height-chain step: all nontrivial zeta zeros up to height 135000 on Re = 1/2 --
    `AllZeros_h134000` + a `[134000, 135000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h134000
import RHInBoxT_1d4000000_3999999d4000000_134000_134026
import RHInBoxT_1d4000000_3999999d4000000_134026_134053
import RHInBoxT_1d4000000_3999999d4000000_134053_134079
import RHInBoxT_1d4000000_3999999d4000000_134079_536421d4
import RHInBoxT_1d4000000_3999999d4000000_134105_134132
import RHInBoxT_1d4000000_3999999d4000000_134132_134158
import RHInBoxT_1d4000000_3999999d4000000_134158_134184
import RHInBoxT_1d4000000_3999999d4000000_134184_134211
import RHInBoxT_1d4000000_3999999d4000000_134211_134237
import RHInBoxT_1d4000000_3999999d4000000_134237_537053d4
import RHInBoxT_1d4000000_3999999d4000000_537051d4_537157d4
import RHInBoxT_1d4000000_3999999d4000000_134289_134316
import RHInBoxT_1d4000000_3999999d4000000_134316_134342
import RHInBoxT_1d4000000_3999999d4000000_268683d2_134368
import RHInBoxT_1d4000000_3999999d4000000_134368_537581d4
import RHInBoxT_1d4000000_3999999d4000000_134395_134421
import RHInBoxT_1d4000000_3999999d4000000_134421_134447
import RHInBoxT_1d4000000_3999999d4000000_134447_134474
import RHInBoxT_1d4000000_3999999d4000000_134474_134500
import RHInBoxT_1d4000000_3999999d4000000_537999d4_134526
import RHInBoxT_1d4000000_3999999d4000000_538103d4_134553
import RHInBoxT_1d4000000_3999999d4000000_134553_134579
import RHInBoxT_1d4000000_3999999d4000000_538315d4_134605
import RHInBoxT_1d4000000_3999999d4000000_134605_134632
import RHInBoxT_1d4000000_3999999d4000000_134632_134658
import RHInBoxT_1d4000000_3999999d4000000_538631d4_538737d4
import RHInBoxT_1d4000000_3999999d4000000_134684_134711
import RHInBoxT_1d4000000_3999999d4000000_134711_538949d4
import RHInBoxT_1d4000000_3999999d4000000_134737_539053d4
import RHInBoxT_1d4000000_3999999d4000000_134763_134789
import RHInBoxT_1d4000000_3999999d4000000_134789_134816
import RHInBoxT_1d4000000_3999999d4000000_134816_134842
import RHInBoxT_1d4000000_3999999d4000000_134842_134868
import RHInBoxT_1d4000000_3999999d4000000_134868_134895
import RHInBoxT_1d4000000_3999999d4000000_134895_134921
import RHInBoxT_1d4000000_3999999d4000000_134921_134947
import RHInBoxT_1d4000000_3999999d4000000_134947_134974
import RHInBoxT_1d4000000_3999999d4000000_134974_135000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h135000

/-- The 38-band NOMINAL partition of `[134000, 135000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 134000
  | 1 => 134026
  | 2 => 134053
  | 3 => 134079
  | 4 => 134105
  | 5 => 134132
  | 6 => 134158
  | 7 => 134184
  | 8 => 134211
  | 9 => 134237
  | 10 => 134263
  | 11 => 134289
  | 12 => 134316
  | 13 => 134342
  | 14 => 134368
  | 15 => 134395
  | 16 => 134421
  | 17 => 134447
  | 18 => 134474
  | 19 => 134500
  | 20 => 134526
  | 21 => 134553
  | 22 => 134579
  | 23 => 134605
  | 24 => 134632
  | 25 => 134658
  | 26 => 134684
  | 27 => 134711
  | 28 => 134737
  | 29 => 134763
  | 30 => 134789
  | 31 => 134816
  | 32 => 134842
  | 33 => 134868
  | 34 => 134895
  | 35 => 134921
  | 36 => 134947
  | 37 => 134974
  | 38 => 135000
  | _ => 135000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((134000:ℝ)) ≤ (134026); norm_num
  · show ((134026:ℝ)) ≤ (134053); norm_num
  · show ((134053:ℝ)) ≤ (134079); norm_num
  · show ((134079:ℝ)) ≤ (134105); norm_num
  · show ((134105:ℝ)) ≤ (134132); norm_num
  · show ((134132:ℝ)) ≤ (134158); norm_num
  · show ((134158:ℝ)) ≤ (134184); norm_num
  · show ((134184:ℝ)) ≤ (134211); norm_num
  · show ((134211:ℝ)) ≤ (134237); norm_num
  · show ((134237:ℝ)) ≤ (134263); norm_num
  · show ((134263:ℝ)) ≤ (134289); norm_num
  · show ((134289:ℝ)) ≤ (134316); norm_num
  · show ((134316:ℝ)) ≤ (134342); norm_num
  · show ((134342:ℝ)) ≤ (134368); norm_num
  · show ((134368:ℝ)) ≤ (134395); norm_num
  · show ((134395:ℝ)) ≤ (134421); norm_num
  · show ((134421:ℝ)) ≤ (134447); norm_num
  · show ((134447:ℝ)) ≤ (134474); norm_num
  · show ((134474:ℝ)) ≤ (134500); norm_num
  · show ((134500:ℝ)) ≤ (134526); norm_num
  · show ((134526:ℝ)) ≤ (134553); norm_num
  · show ((134553:ℝ)) ≤ (134579); norm_num
  · show ((134579:ℝ)) ≤ (134605); norm_num
  · show ((134605:ℝ)) ≤ (134632); norm_num
  · show ((134632:ℝ)) ≤ (134658); norm_num
  · show ((134658:ℝ)) ≤ (134684); norm_num
  · show ((134684:ℝ)) ≤ (134711); norm_num
  · show ((134711:ℝ)) ≤ (134737); norm_num
  · show ((134737:ℝ)) ≤ (134763); norm_num
  · show ((134763:ℝ)) ≤ (134789); norm_num
  · show ((134789:ℝ)) ≤ (134816); norm_num
  · show ((134816:ℝ)) ≤ (134842); norm_num
  · show ((134842:ℝ)) ≤ (134868); norm_num
  · show ((134868:ℝ)) ≤ (134895); norm_num
  · show ((134895:ℝ)) ≤ (134921); norm_num
  · show ((134921:ℝ)) ≤ (134947); norm_num
  · show ((134947:ℝ)) ≤ (134974); norm_num
  · show ((134974:ℝ)) ≤ (135000); norm_num
  · show ((135000:ℝ)) ≤ (135000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 134000
  | 1 => 134026
  | 2 => 134053
  | 3 => 134079
  | 4 => 134105
  | 5 => 134132
  | 6 => 134158
  | 7 => 134184
  | 8 => 134211
  | 9 => 134237
  | 10 => 537051 / 4
  | 11 => 134289
  | 12 => 134316
  | 13 => 268683 / 2
  | 14 => 134368
  | 15 => 134395
  | 16 => 134421
  | 17 => 134447
  | 18 => 134474
  | 19 => 537999 / 4
  | 20 => 538103 / 4
  | 21 => 134553
  | 22 => 538315 / 4
  | 23 => 134605
  | 24 => 134632
  | 25 => 538631 / 4
  | 26 => 134684
  | 27 => 134711
  | 28 => 134737
  | 29 => 134763
  | 30 => 134789
  | 31 => 134816
  | 32 => 134842
  | 33 => 134868
  | 34 => 134895
  | 35 => 134921
  | 36 => 134947
  | 37 => 134974
  | _ => 134974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 134026
  | 1 => 134053
  | 2 => 134079
  | 3 => 536421 / 4
  | 4 => 134132
  | 5 => 134158
  | 6 => 134184
  | 7 => 134211
  | 8 => 134237
  | 9 => 537053 / 4
  | 10 => 537157 / 4
  | 11 => 134316
  | 12 => 134342
  | 13 => 134368
  | 14 => 537581 / 4
  | 15 => 134421
  | 16 => 134447
  | 17 => 134474
  | 18 => 134500
  | 19 => 134526
  | 20 => 134553
  | 21 => 134579
  | 22 => 134605
  | 23 => 134632
  | 24 => 134658
  | 25 => 538737 / 4
  | 26 => 134711
  | 27 => 538949 / 4
  | 28 => 539053 / 4
  | 29 => 134789
  | 30 => 134816
  | 31 => 134842
  | 32 => 134868
  | 33 => 134895
  | 34 => 134921
  | 35 => 134947
  | 36 => 134974
  | 37 => 135000
  | _ => 135000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 135000` (`log 135000 ≤ 12`, `2.7^12 ≥ 135000`). -/
theorem haC_135000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 135000 := by
  have hlog : Real.log 135000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 135000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 135000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[134000, 135000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[134000, 135000]` SEGMENT: every zero with `134000 ≤ Im ≤ 135000` is on the line. -/
theorem segment_134000_135000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 135000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (134000:ℝ) ≤ ρ.im → ρ.im ≤ 135000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 134000 135000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_135000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 135000 via the HEIGHT CHAIN**: `[0,134000]` ∘ `[134000,135000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_135000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 135000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 135000 → ρ.re = 1 / 2 := by
  have hγ134000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 134000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 134000 135000
    (AllZeros_h134000.all_nontrivial_zeros_up_to_height_134000_of_bands
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
      hγ134000)
    (segment_134000_135000 hbands hγ)

end AllZeros_h135000
